module

public import CFSG.Quasithin.Vol2.Ch10SecQ4F1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V]

theorem mem_four (hV2 : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} (hW : Nat.card W = 4) {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) {w : V} (hw : w ∈ W) :
    w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hxy1 : x * y ≠ 1 := fun h => hxy (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, ← mul_one y⁻¹, ← hV2 y, pow_two, inv_mul_cancel_left])
  have hxyx : x * y ≠ x := fun h => hy1 (mul_eq_left.mp h)
  have hxyy : x * y ≠ y := fun h => hx1 (mul_eq_right.mp h)
  set S : Finset V := {1, x, y, x * y} with hS
  have hScard : S.card = 4 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair hxyy.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, fun h => hxyx (h.symm)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 h.symm, fun h => hy1 h.symm, fun h => hxy1 h.symm⟩
  set T : Finset V := (W : Set V).toFinset with hT
  have hTcard : T.card = 4 := by
    rw [hT, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hW
  have hST : S ⊆ T := by
    intro z hz
    rw [hT, Set.mem_toFinset]
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact hx
    · exact hy
    · exact W.mul_mem hx hy
  have heq : S = T := Finset.eq_of_subset_of_card_le hST (by rw [hScard, hTcard])
  have hwT : w ∈ T := by rw [hT, Set.mem_toFinset]; exact hw
  rw [← heq, hS] at hwT
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hwT

theorem false_of_commute_transv (hV2 : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} (hW : Nat.card W = 4)
    {a b : MulAut V} {v₁ v₂ : V} (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ W) (hv₁1 : v₁ ≠ 1) (hv₂1 : v₂ ≠ 1)
    (hv₁₂ : v₁ ≠ v₂) (ha : ∀ w, a w = w ∨ a w = v₁ * w) (hb : ∀ w, b w = w ∨ b w = v₂ * w)
    (haW : ∃ w ∈ W, a w ≠ w) (hbW : ∃ w ∈ W, b w ≠ w) (hab : a * b = b * a) : False := by
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV2 v
  have hav₁ : a v₁ = v₁ := (ha v₁).resolve_right fun h => hv₁1 (by
    have : a v₁ = a 1 := by rw [h, hsq, map_one]
    exact a.injective this)
  have hbv₂ : b v₂ = v₂ := (hb v₂).resolve_right fun h => hv₂1 (by
    have : b v₂ = b 1 := by rw [h, hsq, map_one]
    exact b.injective this)
  have hav₂ : a v₂ = v₁ * v₂ := by
    refine (ha v₂).resolve_left fun h => ?_
    obtain ⟨w, hw, hwa⟩ := haW
    rcases mem_four hV2 hW hv₁ hv₂ hv₁1 hv₂1 hv₁₂ hw with rfl | rfl | rfl | rfl
    · exact hwa (map_one a)
    · exact hwa hav₁
    · exact hwa h
    · exact hwa (by rw [map_mul, hav₁, h])
  have hbv₁ : b v₁ = v₂ * v₁ := by
    refine (hb v₁).resolve_left fun h => ?_
    obtain ⟨w, hw, hwb⟩ := hbW
    rcases mem_four hV2 hW hv₁ hv₂ hv₁1 hv₂1 hv₁₂ hw with rfl | rfl | rfl | rfl
    · exact hwb (map_one b)
    · exact hwb h
    · exact hwb hbv₂
    · exact hwb (by rw [map_mul, h, hbv₂])
  have e1 : (a * b) v₁ = v₂ := by
    rw [MulAut.mul_apply, hbv₁, map_mul, hav₂, hav₁, mul_comm v₁ v₂, mul_assoc, hsq, mul_one]
  have e2 : (b * a) v₁ = v₂ * v₁ := by rw [MulAut.mul_apply, hav₁, hbv₁]
  rw [hab, e2] at e1
  exact hv₁1 (mul_eq_left.mp e1)

theorem sq_fix_of_fix (hV2 : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} (hW : Nat.card W = 4)
    {k : MulAut V} (hkW : ∀ w ∈ W, k w ∈ W) {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀1 : w₀ ≠ 1)
    (hkw₀ : k w₀ = w₀) : ∀ w ∈ W, (k ^ 2) w = w := by
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV2 v
  obtain ⟨x, hx, hx1, hxw₀⟩ : ∃ x ∈ W, x ≠ 1 ∧ x ≠ w₀ := by
    by_contra hall
    push Not at hall
    have hle : Nat.card W ≤ 2 := by
      have hsub : (W : Set V) ⊆ {1, w₀} := fun z hz => by
        by_cases hz1 : z = 1
        · exact Or.inl hz1
        · exact Or.inr (hall z hz hz1)
      calc Nat.card W = Nat.card (W : Set V) := rfl
        _ ≤ Nat.card ({1, w₀} : Set V) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  have hkx : k x = x ∨ k x = w₀ * x := by
    rcases mem_four hV2 hW hw₀ hx hw₀1 hx1 (Ne.symm hxw₀) (hkW x hx) with h | h | h | h
    · exact absurd (k.injective (h.trans (map_one k).symm)) hx1
    · exact absurd (k.injective (h.trans hkw₀.symm)) hxw₀
    · exact Or.inl h
    · exact Or.inr h
  have hk2x : (k ^ 2) x = x := by
    rw [pow_two, MulAut.mul_apply]
    rcases hkx with h | h
    · rw [h, h]
    · rw [h, map_mul, hkw₀, h, ← mul_assoc, hsq, one_mul]
  intro w hw
  have hk2w₀ : (k ^ 2) w₀ = w₀ := by rw [pow_two, MulAut.mul_apply, hkw₀, hkw₀]
  rcases mem_four hV2 hW hw₀ hx hw₀1 hx1 (Ne.symm hxw₀) hw with rfl | rfl | rfl | rfl
  · exact map_one _
  · exact hk2w₀
  · exact hk2x
  · rw [map_mul, hk2w₀, hk2x]

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4
