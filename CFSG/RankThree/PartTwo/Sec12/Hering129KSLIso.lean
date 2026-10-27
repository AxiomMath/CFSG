module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.Open.StatedSUFieldChange
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129KSLIso

open CFSG CFSG.RankThree.PartTwo

@[expose] noncomputable def slEquiv {K K' : Type} [CommRing K] [CommRing K'] (n : ℕ)
    (κ : K ≃+* K') :
    Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K' :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map κ.toRingHom)
    (Matrix.SpecialLinearGroup.map κ.symm.toRingHom) (by ext x i j; simp) (by ext x i j; simp)

theorem nonempty_mulEquiv_of_isSLThreePiAt {X Y : Type} [Group X] [Group Y] {m : ℕ}
    (hX : Sec4.IsSLThreePiAt X m) (hY : Sec4.IsSLThreePiAt Y m) : Nonempty (X ≃* Y) := by
  obtain ⟨K₁, _, _, h₁⟩ := hX
  obtain ⟨K₂, _, _, h₂⟩ := hY
  have := Fintype.ofFinite K₁
  have := Fintype.ofFinite K₂
  rcases h₁ with ⟨hc₁, hm₁, ⟨f₁⟩⟩ | ⟨hc₁, hm₁, ⟨f₁⟩⟩ <;>
    rcases h₂ with ⟨hc₂, hm₂, ⟨f₂⟩⟩ | ⟨hc₂, hm₂, ⟨f₂⟩⟩
  · have hcard : Fintype.card K₁ = Fintype.card K₂ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc₁, hc₂]
    exact ⟨f₁.trans ((Sec4.statedSLEquiv 3 K₁).trans
      ((slEquiv 3 (FiniteField.ringEquivOfCardEq hcard)).trans
        ((Sec4.statedSLEquiv 3 K₂).symm.trans f₂.symm)))⟩
  · omega
  · omega
  · have hcard : Fintype.card K₁ = Fintype.card K₂ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc₁, hc₂]
    exact ⟨f₁.trans
      ((CFSG.Open.StatedSUFieldChange.statedSUEquiv (FiniteField.ringEquivOfCardEq hcard) 3 m).trans
        f₂.symm)⟩

end CFSG.RankThree.PartTwo.Sec12.Hering129KSLIso
