SP=~/scala
SCALAC=$(SP)/bin/scalac -deprecation
SCALA = $(SP)/bin/scala -classpath $(SP)/lib

.PHONY: marking
marking: build
	$(SCALA) YBeispiel

.PHONY: dot
dot: build
	$(SCALA) PrintDot > output.dot
	dot output.dot -Tpng > output.png


.PHONY: build
build:
	$(SCALAC) src/*.scala	
