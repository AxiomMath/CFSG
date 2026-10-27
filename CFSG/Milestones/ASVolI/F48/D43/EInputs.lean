module

public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.D43.Data
public import Certificates.Data.CFSGNative.Th.Core

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th.Native CFSG.CosetTable

set_option compiler.extract_closed false

@[expose] def burnsideF48dE_PhiW : List (List (Fin 18 × Bool)) :=
  [[(5, true), (5, true), (5, true), (5, true), (3, true)],
    [(4, true)],
    [(5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true),
      (5, true)],
    [(6, true)],
    [(7, true), (6, true), (6, true)],
    [(8, true), (7, true), (6, true)],
    [(9, true)],
    [(10, true)],
    [(11, true), (10, true), (10, true)],
    [(12, true), (11, true), (10, true)],
    [(13, true)],
    [(14, true), (13, true), (13, true)],
    [(15, true), (14, true), (13, true)],
    [(16, true)],
    [(17, true)]]

abbrev burnsideF48dE_Ws (c : ℕ) : List (List (Fin 18 × Bool)) :=
  burnsideF48s_eWs burnsideF48d_R13 burnsideF48d_R23 6 [((0 : Fin 18), true)]
    [((1 : Fin 18), true)] (List.replicate c ((2 : Fin 18), true))

abbrev burnsideF48dE_S1 : List ℕ :=
  [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

abbrev burnsideF48dE_WsP1 : List (List (Fin (subsetOf 18 burnsideF48dE_S1).length × Bool)) :=
  restrictWords (subsetOf 18 burnsideF48dE_S1) (burnsideF48d_R13 ++ burnsideF48d_R23)

abbrev burnsideF48dE_WsP1' : List (List (Fin (subsetOf (subsetOf 18 burnsideF48dE_S1).length
    [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]).length × Bool)) :=
  restrictWords (subsetOf (subsetOf 18 burnsideF48dE_S1).length
    [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]) burnsideF48dE_WsP1

end CFSG.ASVolI
