module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3E16b
public import CFSG.GH74.Uniqueness.SU.KI1r3FamSp2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

theorem exists_E16_alt_eight : ∃ E : Subgroup (alternatingGroup (Fin 8)),
    CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, hE, hc⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk94.e16_alt_eight_nine le_rfl (by norm_num) (MulEquiv.refl _)
  exact ⟨E, CFSG.GH74.Uniqueness.SU.K.R3.isElemAbelian_two_of_sq E hE, hc⟩

theorem exists_E16_alt_nine : ∃ E : Subgroup (alternatingGroup (Fin 9)),
    CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, hE, hc⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk94.e16_alt_eight_nine (by norm_num) le_rfl (MulEquiv.refl _)
  exact ⟨E, CFSG.GH74.Uniqueness.SU.K.R3.isElemAbelian_two_of_sq E hE, hc⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
