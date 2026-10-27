module

public import CFSG.Milestones.ASVolI.F48.D43.Data
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ASVolI

open CFSG.CosetTable

abbrev burnsideF48d_Ws (_ : Unit := ()) : List (List (Fin 17 × Bool)) :=
  burnsideF48s_eWs burnsideF48d_R1 burnsideF48d_R2 6 [(0, true)] [(1, true)] []

abbrev burnsideF48d_tS1 : List ℕ := [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

abbrev burnsideF48d_Ws1 (_ : Unit := ()) :=
  restrictWords (subsetOf 17 burnsideF48d_tS1) (burnsideF48d_Ws ())

abbrev burnsideF48d_tSB : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

abbrev burnsideF48d_Ws2 (_ : Unit := ()) :=
  restrictWords (subsetOf (subsetOf 17 burnsideF48d_tS1).length burnsideF48d_tSB)
    (burnsideF48d_Ws1 ())

abbrev burnsideF48d_tSU : List ℕ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

abbrev burnsideF48d_Ws3 (_ : Unit := ()) :=
  restrictWords (subsetOf (subsetOf (subsetOf 17 burnsideF48d_tS1).length burnsideF48d_tSB).length
    burnsideF48d_tSU) (burnsideF48d_Ws2 ())

abbrev burnsideF48d_tSU2 : List ℕ := [6, 7, 8, 9, 10, 11]

abbrev burnsideF48d_Ws4 (_ : Unit := ()) :=
  restrictWords (subsetOf (subsetOf (subsetOf (subsetOf 17 burnsideF48d_tS1).length
    burnsideF48d_tSB).length burnsideF48d_tSU).length burnsideF48d_tSU2) (burnsideF48d_Ws3 ())

end CFSG.ASVolI
