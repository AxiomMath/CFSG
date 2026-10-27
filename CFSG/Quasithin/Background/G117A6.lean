module

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Basic
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent

public section

namespace CFSG.Quasithin

namespace G11

namespace G117

@[expose] def A6Facts : Prop :=
  (∀ (K : Type) [Group K], Nonempty (K ≃* ↥(alternatingGroup (Fin 6))) →
      Nat.card (MulAut K) = 1440) ∧
    (∀ D : Subgroup ↥(alternatingGroup (Fin 6)), Nat.card D = 8 → ∃ a b : ↥D, a * b ≠ b * a) ∧
    (∀ (K : Type) [Group K], Nonempty (K ≃* ↥(alternatingGroup (Fin 6))) →
      ∃ E : Subgroup K, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9)

theorem a6Facts : A6Facts := by
  refine ⟨fun K _ ⟨e⟩ => CFSG.QuasithinUnique.DoubleA3.card_mulAut_alt6 e, fun D hD => ?_,
    fun K _ ⟨e⟩ => CFSG.QuasithinUnique.DoubleA3.exists_isElemAbelian_nine e⟩
  obtain ⟨ψ⟩ := CFSG.QuasithinUnique.DoubleA3.nonempty_dihedral_of_card_eight D hD
  refine ⟨ψ.symm (DihedralGroup.r 1), ψ.symm (DihedralGroup.sr 0), fun h => ?_⟩
  have h1 := congrArg ψ h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  revert h1
  decide

end G117

end G11

end CFSG.Quasithin
