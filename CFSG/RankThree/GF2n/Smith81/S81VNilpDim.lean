module

public import CFSG.RankThree.GF2n.Smith81.S81UElem

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.Open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem card_oneAdd_le_card_submodule [Finite F] [CharP F 2] {n : ℕ}
    (S : Submodule F (Matrix (Fin n) (Fin n) F))
    (hmul : ∀ X ∈ S, ∀ Y ∈ S, X * Y ∈ S) (hsq : ∀ X ∈ S, X * X = 0) :
    Nat.card (oneAdd S hmul hsq) ≤ Nat.card S := by
  have hmem : ∀ g : oneAdd S hmul hsq, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ S := by
    intro g
    obtain ⟨X, hX, hg⟩ := g.2
    rw [hg, add_sub_cancel_left]
    exact hX
  refine Nat.card_le_card_of_injective
    (fun g => (⟨((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1, hmem g⟩ : S)) ?_
  intro g g' hgg
  have e : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
      ((g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 := congrArg Subtype.val hgg
  exact Subtype.ext (Units.ext (sub_left_inj.1 e))

theorem nine_le_finrank_nilpSpan [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {E : Subgroup (GL (Fin 6) F)} (hE : IsElemAbelian 2 E) (hle : E ≤ SUid σ 6)
    (h : Nat.card (Fσ σ) ^ 9 ≤ Nat.card E) : 9 ≤ finrank F (nilpSpan E) := by
  have hsa := conjTr_eq_of_mem_SUid_of_elemAbelian σ hE hle
  have h1 := card_sq_le_card_oneAdd σ hσ.exists_ne hE hsa
  have h2 := card_oneAdd_le_card_submodule (nilpSpan E)
    (fun _ hX _ hY => nilpSpan_mul_mem hX hY) (fun _ hX => nilpSpan_sq hE hX)
  have h3 : Nat.card (nilpSpan E) = Nat.card F ^ finrank F (nilpSpan E) :=
    Module.natCard_eq_pow_finrank
  have h4 := card_Fσ_sq hσ
  have hq : 1 < Nat.card (Fσ σ) := Finite.one_lt_card
  have h5 : Nat.card (Fσ σ) ^ 18 ≤ Nat.card (nilpSpan E) :=
    calc Nat.card (Fσ σ) ^ 18 = (Nat.card (Fσ σ) ^ 9) ^ 2 := by ring
      _ ≤ Nat.card E ^ 2 := Nat.pow_le_pow_left h 2
      _ ≤ Nat.card (nilpSpan E) := h1.trans h2
  have h6 : Nat.card (Fσ σ) ^ 18 ≤ Nat.card (Fσ σ) ^ (2 * finrank F (nilpSpan E)) := by
    rw [pow_mul, h4, ← h3]
    exact h5
  have h7 : 18 ≤ 2 * finrank F (nilpSpan E) := (pow_le_pow_iff_right₀ hq).1 h6
  omega

end CFSG.RankThree.GF2n.Smith81.S81V
