module

public import Certificates.Data.CFSGNative.J4Tree.VerdictData

public section

namespace CFSG.ASVolI

open CFSG.J4Tree.Native.Col

@[expose] def burnsideJ4NP_vjIdsLit : List Nat := [2, 3, 11, 36, 39, 42, 63, 66, 76, 98, 103, 106,
  107, 112, 124, 135, 166, 219, 267, 378, 389, 464, 480, 515, 516, 527, 532, 543, 552, 715, 867,
  871, 895, 916, 937, 959, 1013, 1025, 1077, 1085, 1122, 1216, 1244, 1277, 1284, 1322, 1326, 1, 4,
  73, 81, 93, 102, 133, 134, 385, 905, 1124, 1260, 89]

@[expose] def burnsideJ4NP_m4IdsLit : List Nat := [136, 266, 486, 539, 542]

@[noinline, expose] def burnsideJ4NP_idsCoverWith (cs : List Nat) : Bool :=
  (List.range' 1 1327).all fun k =>
    cs.contains k || burnsideJ4NP_vjIdsLit.contains k || burnsideJ4NP_m4IdsLit.contains k

@[expose] def burnsideJ4NP_idsCoverOK (_ : Unit := ()) : Bool :=
  burnsideJ4NP_idsCoverWith (colNodes.map VNode.k)

end CFSG.ASVolI
