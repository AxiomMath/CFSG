module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Clauses
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Ord3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section Transfer3


variable {X : Type} [Group X] {Y : Subgroup X}

theorem toC_zpowers (e : ↥Y ≃* F42C) {x : X} (hx : x ∈ Y) :
    toC e (Subgroup.zpowers x) = Subgroup.zpowers (e ⟨x, hx⟩) := by
  have h : Subgroup.zpowers x = (Subgroup.zpowers (e ⟨x, hx⟩)).map (ιY e) := by
    rw [MonoidHom.map_zpowers, ιY_e]
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective (ιY_injective e) _

theorem isElemAb_toC (e : ↥Y ≃* F42C) [Finite X] {B : Subgroup X} (hBY : B ≤ Y)
    (hB : IsElemAb 3 4 B) : IsElemAb 3 4 (toC e B) := by
  refine ⟨CFSG.IsElementaryAbelian.of_forall ?_ ?_, (card_toC e hBY).trans hB.2⟩
  · intro c₁ h₁ c₂ h₂
    apply ιY_injective e
    rw [map_mul, map_mul]
    exact elemAb_comm hB _ h₁ _ h₂
  · intro c hc
    apply ιY_injective e
    rw [map_pow, map_one]
    exact elemAb_pow hB _ hc

theorem isSylowOf_toC (e : ↥Y ≃* F42C) [Finite X] {Q : Subgroup X} (hQ : IsSylowOf 3 Q Y) :
    IsSylowOf 3 (toC e Q) (⊤ : Subgroup F42C) := by
  haveI : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_of_card_p le_top ?_
  rw [card_toC e hQ.1, card_sylow_three e hQ, Subgroup.card_top, card_F42C,
    factorization_three_card]

end Transfer3


section Clauses3


variable {X : Type} [Group X] {Y : Subgroup X}

theorem clause_order3 (e : ↥Y ≃* F42C) :
    ∀ x ∈ Y, orderOf x = 3 → 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) ∨
      Nat.card ↥(Y ⊓ Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  intro x hx hx3
  rw [card_inf_cen e hx]
  exact L2_star (by rw [orderOf_e e hx]; exact hx3)

theorem clause_unique_E81 [Finite X] (e : ↥Y ≃* F42C) :
    ∀ Q : Subgroup X, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup X, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂ := by
  intro Q hQ B₁ B₂ h₁ h₂ e₁ e₂
  have h₁Y : B₁ ≤ Y := h₁.trans hQ.1
  have h₂Y : B₂ ≤ Y := h₂.trans hQ.1
  have := L5_C (isSylowOf_toC e hQ) (toC_le e h₁) (toC_le e h₂)
    (isElemAb_toC e h₁Y e₁) (isElemAb_toC e h₂Y e₂)
  exact toC_injective e h₁Y h₂Y this

theorem clause_inv_order3 [Finite X] (e : ↥Y ≃* F42C) :
    ∀ t ∈ Y, orderOf t = 2 → ∀ x ∈ Y, orderOf x = 3 → ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      ∃ y ∈ Y, y * x * y⁻¹ ∈ Cen t := by
  intro t ht ht2 x hx hx3 hnd
  rw [card_inf_cen e hx] at hnd
  obtain ⟨c, hc⟩ := L6_star_C (t := e ⟨t, ht⟩) (x := e ⟨x, hx⟩)
    (by rw [orderOf_e e ht]; exact ht2) (by rw [orderOf_e e hx]; exact hx3) hnd
  refine ⟨ιY e c, ιY_mem e c, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  have h1 := congrArg (ιY e) hc
  simp only [map_mul, map_inv, ιY_e] at h1
  simpa [mul_assoc] using h1


theorem clause_lines [Finite X] (e : ↥Y ≃* F42C) :
    ∀ B : Subgroup X, B ≤ Y → IsElemAb 3 4 B → Y ⊓ CenS B = B → ∀ x ∈ Y, orderOf x = 3 →
      ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      {D : Subgroup X | D ≤ B ∧ ∃ y ∈ Y, conjBy y (Subgroup.zpowers x) = D}.ncard ≤ 12 ∧
        ∃ y ∈ Y, y * x * y⁻¹ ∈ B := by
  intro B hBY hB _ x hx hx3 hnd
  rw [card_inf_cen e hx] at hnd
  have hB' := isElemAb_toC e hBY hB
  obtain ⟨hlines, y, hy⟩ := L4_star_C hB' (by rw [orderOf_e e hx]; exact hx3) hnd
  refine ⟨?_, ?_⟩
  · refine le_trans (Set.ncard_le_ncard_of_injOn (toC e) ?_ ?_ (Set.toFinite _)) hlines
    · rintro D ⟨hDB, y, hy, rfl⟩
      refine ⟨toC_le e hDB, e ⟨y, hy⟩, ?_⟩
      rw [← toC_zpowers e hx]
      have h := toC_conjBy e (Subgroup.zpowers x) (e ⟨y, hy⟩)
      rw [ιY_e] at h
      exact h.symm
    · intro D₁ h₁ D₂ h₂ h
      exact toC_injective e (h₁.1.trans hBY) (h₂.1.trans hBY) h
  · refine ⟨ιY e y, ιY_mem e y, ?_⟩
    rw [mem_toC] at hy
    simpa [map_mul, map_inv, ιY_e] using hy

end Clauses3

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
