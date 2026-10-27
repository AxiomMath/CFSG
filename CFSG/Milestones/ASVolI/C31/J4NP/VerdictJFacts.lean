module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs
public import CFSG.Milestones.ASVolI.C31.J4NP.Red

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] def burnsideJ4NP_vjT3Ids : List ℕ :=
  [2, 3, 11, 36, 39, 42, 63, 66, 76, 98, 103, 106, 107, 112, 124, 135, 166, 219, 267, 378, 389,
    464, 480, 515, 516, 527, 532, 543, 552, 715, 867, 871, 895, 916, 937, 959, 1013, 1025, 1077,
    1085, 1122, 1216, 1244, 1277, 1284, 1322, 1326]

@[expose] def burnsideJ4NP_vjHIds : List ℕ := [1, 4, 73, 81, 93, 102, 133, 134, 385, 905, 1124, 1260]

@[expose] def burnsideJ4NP_NPFact (k : ℕ) : Prop :=
  ∃ g : J, P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (burnsideJ4NP_Wv k : Set J)

@[expose] def burnsideJ4NP_FFact (k : ℕ) : Prop :=
  ∃ d : J, burnsideJ4NP_F.map (MulAut.conj d).toMonoidHom ≤ burnsideJ4NP_Wv k

@[expose] def burnsideJ4NP_ConjW539 (X : Subgroup J) : Prop :=
  ∃ m : J, X = (burnsideJ4NP_Wv 539).map (MulAut.conj m).toMonoidHom

end CFSG.ASVolI
