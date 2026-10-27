module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Check
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434O8pE9

open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (digitsOf)

@[expose] def o8pE9 : E9Data where
  n := 360
  pg := CFSG.EvenSmallLie.OmegaEight.genArrs.extract 0 8
  qW := (#["0102453202735104626732010245320273510462673010245672321",
         "2376232",
         "0136712325421076264015372023542010232"]).map digitsOf
  qKeys := [0, 1, 2]
  qFuel := 245
  qOrd := 243
  dW := (#["2",
         "0",
         "1011",
         "1101"]).map digitsOf
  dKeys := [0, 1, 2]
  dFuel := 83
  hW := (#["",
         "0123676102454762640153720235420103103762640153720235420103762640153720\
          23542010",
         "0102453202735104626732010245320273510462673010245320273510462673010245\
          320273510462670120102453202735104626734542310676",
         "1370235476264015372023542010202376264015372023542010376264015372023542\
          0102376264015372023542010"]).map digitsOf

end CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
