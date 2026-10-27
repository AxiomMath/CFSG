module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem s16t3_card_iso_eq_of_trans (hq : CFSG.Open.IsQuasisimple ↥L)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    {Y₁ Y₂ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))}
    (h₁ : XMod.IsIrr ↥L Y₁) (h₂ : XMod.IsIrr ↥L Y₂) :
    Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
        XMod.IsIrr ↥L J ∧ XMod.Iso ↥L J Y₁} =
      Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
        XMod.IsIrr ↥L J ∧ XMod.Iso ↥L J Y₂} := by
  letI : MulDistribMulAction ↥(Subgroup.normalizer (L : Set (MulAut W)))
      (W ⧸ modFix L (⊤ : Subgroup W)) :=
    quotAct (X := L) (W := (⊤ : Subgroup W)) le_rfl (fun _ _ _ _ => trivial)
  obtain ⟨hI₁, hY₁⟩ := s16t3_lift hq h₁
  obtain ⟨hI₂, hY₂⟩ := s16t3_lift hq h₂
  obtain ⟨g, hg, hI⟩ := htrans _ hI₁ _ hI₂
  have h1 := tilde_smul (X := L) (W := (⊤ : Subgroup W)) le_rfl (fun _ _ _ _ => trivial)
    (⟨g, hg⟩ : ↥(Subgroup.normalizer (L : Set (MulAut W))))
    (modComm L (Y₁.comap (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))))
  dsimp only at h1
  rw [hY₁] at h1
  have hsmul : (⟨g, hg⟩ : ↥(Subgroup.normalizer (L : Set (MulAut W)))) • Y₁ = Y₂ := by
    rw [h1, ← hY₂, hI, Subgroup.pointwise_smul_def]
    rfl
  rw [← hsmul]
  exact (s16t3_card_iso_smul (normalizes_quot (X := L) (W := (⊤ : Subgroup W)) le_rfl
    (fun _ _ _ _ => trivial)) _ Y₁).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
