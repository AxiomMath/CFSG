module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

variable {Hh : Type} [Group Hh]

theorem comm_of_isElemAbelian {V : Subgroup Hh} (hV : IsElemAbelian 2 V) {a b : Hh} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a :=
  Subtype.ext_iff.mp (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isElemAbelian_of_le {A B : Subgroup Hh} (hB : IsElemAbelian 2 B) (h : A ≤ B) :
    IsElemAbelian 2 A :=
  ⟨⟨⟨fun x y => Subtype.ext (comm_of_isElemAbelian hB (h x.2) (h y.2))⟩⟩,
    fun x hx => hB.2 x (h hx)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
