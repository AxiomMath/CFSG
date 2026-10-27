module

public import CFSG.Quasithin.Background.SmithD321Kplus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.SmithD321 Subgroup

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private noncomputable def s16t3_isoTypeEquiv {Λ : Subgroup Γ} {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) :
    {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J I} ≃
      {J : Subgroup Q // J ≤ isoComp ↥Λ I ∧ XMod.IsIrr ↥Λ J} where
  toFun J := ⟨J.1, le_isoComp J.2.1 J.2.2, J.2.1⟩
  invFun J := ⟨J.1, J.2.2, by
    obtain ⟨J', hJ'⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
      (S := fun J' : {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' I} =>
        (J' : Subgroup Q)) (fun J' => J'.2.1) J.2.2 J.2.1
    exact hJ'.trans J'.2.2⟩
  left_inv J := Subtype.ext rfl
  right_inv J := Subtype.ext rfl

theorem s16t3_card_iso_type [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Λ : Subgroup Γ} {I : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ}
    (hY : IsotypicOfLength ↥Λ (isoComp ↥Λ I) I c)
    (hE : Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) = 2) :
    Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J I} = 2 ^ c - 1 := by
  have h := card_irr_eq (Q := Q) hQ hI hY hE
  rw [← h]
  exact Nat.card_congr (s16t3_isoTypeEquiv hI)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
