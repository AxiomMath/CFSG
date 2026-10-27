module

public import CFSG.Sporadic.Th.Max3.GenCert

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th

open Native

@[expose] def fusionWord0 : List ℕ := [1, 2, 2, 1, 2]

@[expose] def fusionWord1 : List ℕ := [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2]

@[expose] def hRootWord0 : List ℕ := [2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2]

@[expose] def hRootWord1 : List ℕ := [2, 1, 2, 2, 1]

@[expose] def invChecks (n : ℕ) (alpha beta : Table) : Bool :=
  let betaInv := invT n beta
  let mx := wordT n (wordLetters alpha beta betaInv) xWord
  let my := wordT n (wordLetters alpha beta betaInv) yWord
  let myi := invT n my
  let R0 := abTable n mx my hRootWord0
  let R1 := powT n 9 (abTable n mx my hRootWord1)
  let tr := hTrees hTreeData
  let π := hOrder tr.1 tr.2 R0 R1 mx my mx myi
  (invOK n beta betaInv && invOK n my myi) &&
    (compT n R0 R0 == idT n && ap R0 1 != 1 && compT n R1 R1 == idT n && ap R1 1 != 1) &&
    (tr.1.size == 68796 && tr.2.size == 819 && π.size == 69615 &&
      hFpsIncreasing tr.1 tr.2 R0 R1 mx my mx myi π)

@[expose] def maxChecks (n : ℕ) (alpha beta : Table) : Bool :=
  let m3 := max3Tables n alpha beta
  let X := m3.1
  let Y := m3.2.1
  (m3.2.2 && countFix n alpha == 10200 && invChecks n alpha beta) &&
  (let Q0 := powT n 6 (compT n X Y)
   let F0 := fusionTables n alpha (abTable n alpha beta fusionWord0) Q0
   F0.2.2 && compT n F0.1 (compT n Q0 F0.2.1) == alpha &&
     genCheck n X Y F0.1 F0.2.1 (124874528, 1) (117285930, 1) (123411384, 2) (138982628, 2)
       (5943848, 1) (80847776, 2) (11320088, 2) (7357898, 2)) &&
  (let F1 := fusionTables n alpha (abTable n alpha beta fusionWord1) X
   F1.2.2 && compT n F1.1 (compT n X F1.2.1) == alpha &&
     genCheck n X Y F1.1 F1.2.1 (69792828, 2) (77042917, 2) (83608236, 2) (133437337, 2)
       (26716518, 1) (60915366, 2) (8018416, 1) (5452676, 1))

@[expose] def maxCheckAll (_ : Unit) : Bool :=
  let st := thBFS ()
  maxChecks st.count (tblOfBytes st.count st.alpha) (tblOfBytes st.count st.beta)

end CFSG.Sporadic.Th
