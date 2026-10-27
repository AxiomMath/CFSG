module

public import CFSG.RankThree.GF2n.Smith81.S81VAmbCloser

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary Module

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem gu2b_finrank_inf_le {a b : Submodule F (Fin 6 → F)} (ha : IsPt σ a) :
    finrank F ↥(a ⊓ b) ≤ 3 := by
  have h1 : finrank F ↥(a ⊓ b) ≤ finrank F ↥a := Submodule.finrank_mono inf_le_left
  have h2 : finrank F ↥a = 3 := ha.2
  omega

private theorem gu2b_eq_of_inf_three {x y : Submodule F (Fin 6 → F)} (hx : IsPt σ x)
    (hy : IsPt σ y) (h : finrank F ↥(x ⊓ y) = 3) : x = y := by
  have hx3 : finrank F ↥x = 3 := hx.2
  have hy3 : finrank F ↥y = 3 := hy.2
  have hxy : x ⊓ y = x := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have hxy' : x ⊓ y = y := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  exact hxy.symm.trans hxy'

theorem adj_connected (hσ : IsUnitaryInvolution σ) {x y : Submodule F (Fin 6 → F)}
    (hx : IsPt σ x) (hy : IsPt σ y) : Relation.ReflTransGen (Adj σ) x y := by
  have key : ∀ n : ℕ, ∀ a b : Submodule F (Fin 6 → F), IsPt σ a → IsPt σ b →
      3 - finrank F ↥(a ⊓ b) ≤ n → Relation.ReflTransGen (Adj σ) a b := by
    intro n
    induction n with
    | zero =>
      intro a b ha hb hn
      have h3 : finrank F ↥(a ⊓ b) = 3 := by
        have := gu2b_finrank_inf_le (b := b) ha
        omega
      obtain rfl := gu2b_eq_of_inf_three ha hb h3
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro a b ha hb hn
      have hle := gu2b_finrank_inf_le (b := b) ha
      by_cases h2 : 2 ≤ finrank F ↥(a ⊓ b)
      · by_cases h3 : finrank F ↥(a ⊓ b) = 3
        · obtain rfl := gu2b_eq_of_inf_three ha hb h3
          exact Relation.ReflTransGen.refl
        · have h2' : finrank F ↥(a ⊓ b) = 2 := by omega
          exact Relation.ReflTransGen.single ⟨ha, hb, h2'⟩
      · obtain ⟨z, hadj, hlt⟩ := exists_adjacent_closer hσ ha hb (by omega)
        have hz : IsPt σ z := hadj.2.1
        have hzb : finrank F ↥(z ⊓ b) ≤ 3 := gu2b_finrank_inf_le (b := b) hz
        exact Relation.ReflTransGen.head hadj (ih z b hz hb (by omega))
  exact key 3 x y hx hy (by omega)

end CFSG.RankThree.GF2n.Smith81.S81V
