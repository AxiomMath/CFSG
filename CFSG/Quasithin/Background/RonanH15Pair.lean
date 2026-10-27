module

public import CFSG.Quasithin.Background.HMathieuStd

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

private theorem h15_mem_golayC (x : G6.PermMod 24) :
    x ∈ golayC ↔ Multiplicative.toAdd x ∈ CFSG.Monster.Code.C := Iff.rfl

private theorem h15_toAdd_pairVec {i j : Fin 24} (hij : i ≠ j) :
    Multiplicative.toAdd (pairVec i j) =
      fun m => if m ∈ ({i, j} : Finset (Fin 24)) then (1 : ZMod 2) else 0 := by
  funext m
  simp only [pairVec, unitVec, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Pi.single_apply,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : m = i
  · subst h1
    simp [hij]
  · by_cases h2 : m = j
    · subst h2
      simp [h1]
    · simp [h1, h2]

private theorem h15_eq_zero_of_support {x : Fin 24 → ZMod 2} {W : Finset (Fin 24)}
    (hx : x ∈ CFSG.Monster.Code.C) (hW : W.card < 8) (hsupp : ∀ m, x m ≠ 0 → m ∈ W) :
    x = 0 := by
  by_contra h0
  have h8 := CFSG.Monster.Code.eight_le_wt hx h0
  have hle : hammingNorm x ≤ W.card := by
    unfold hammingNorm
    exact Finset.card_le_card fun m hm => hsupp m (Finset.mem_filter.1 hm).2
  omega

private theorem h15_ind_mem_iff {U W : Finset (Fin 24)} (hUW : U ⊆ W) (hW : W.card < 8) :
    (fun m => if m ∈ U then (1 : ZMod 2) else 0) ∈ CFSG.Monster.Code.C ↔ U = ∅ := by
  constructor
  · intro hx
    have h0 : (fun m : Fin 24 => if m ∈ U then (1 : ZMod 2) else 0) = 0 := by
      refine h15_eq_zero_of_support hx hW ?_
      intro m hm
      exact hUW (by
        by_contra h
        exact hm (if_neg h))
    by_contra hne
    obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hv := congrFun h0 m
    simp [hm] at hv
  · rintro rfl
    have h0 : (fun m : Fin 24 => if m ∈ (∅ : Finset (Fin 24)) then (1 : ZMod 2) else 0) = 0 := by
      funext m
      simp
    rw [h0]
    exact Submodule.zero_mem _

theorem pairVec_not_mem_golayC {i j : Fin 24} (hij : i ≠ j) : pairVec i j ∉ golayC := by
  have hW : ({i, j} : Finset (Fin 24)).card < 8 := by
    have h2 : ({i, j} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
    omega
  rw [h15_mem_golayC, h15_toAdd_pairVec hij, h15_ind_mem_iff Finset.Subset.rfl hW]
  exact Finset.insert_ne_empty _ _

private theorem h15_ind_add (U V : Finset (Fin 24)) :
    (fun m => if m ∈ U then (1 : ZMod 2) else 0) + (fun m => if m ∈ V then (1 : ZMod 2) else 0) =
      fun m => if m ∈ symmDiff U V then (1 : ZMod 2) else 0 := by
  funext m
  simp only [Pi.add_apply, Finset.mem_symmDiff]
  by_cases hU : m ∈ U <;> by_cases hV : m ∈ V <;> simp [hU, hV] <;> decide

private theorem h15_symmDiff_eq_empty_iff (U V : Finset (Fin 24)) :
    symmDiff U V = ∅ ↔ U = V := by
  rw [← Finset.bot_eq_empty, symmDiff_eq_bot]

private theorem h15_pair_mul_pair_mem_iff {i j k l : Fin 24} (hij : i ≠ j) (hkl : k ≠ l) :
    pairVec i j * pairVec k l ∈ golayC ↔ ({i, j} : Finset (Fin 24)) = {k, l} := by
  have hUW : symmDiff ({i, j} : Finset (Fin 24)) {k, l} ⊆ {i, j} ∪ {k, l} := by
    intro m hm
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hm ⊢
    tauto
  have hW : (({i, j} : Finset (Fin 24)) ∪ {k, l}).card < 8 := by
    have h1 := Finset.card_union_le ({i, j} : Finset (Fin 24)) {k, l}
    have h2 : ({i, j} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
    have h3 : ({k, l} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
    omega
  rw [h15_mem_golayC, toAdd_mul, h15_toAdd_pairVec hij, h15_toAdd_pairVec hkl, h15_ind_add,
    h15_ind_mem_iff hUW hW, h15_symmDiff_eq_empty_iff]

theorem pairVec_inv_mul_mem_golayC_iff {i j k l : Fin 24} (hij : i ≠ j) (hkl : k ≠ l) :
    (pairVec i j)⁻¹ * pairVec k l ∈ golayC ↔ ({i, j} : Finset (Fin 24)) = {k, l} := by
  rw [inv_eq_of_mul_eq_one_right (pairVec_sq i j)]
  exact h15_pair_mul_pair_mem_iff hij hkl

theorem pairVec_inv_mul_mem_sup_iff {a b i j k l : Fin 24} (hab : a ≠ b) (hij : i ≠ j)
    (hkl : k ≠ l) :
    (pairVec i j)⁻¹ * pairVec k l ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) ↔
      ({i, j} : Finset (Fin 24)) = {k, l} ∨
        symmDiff ({i, j} : Finset (Fin 24)) {k, l} = {a, b} := by
  have hUW : symmDiff (symmDiff ({i, j} : Finset (Fin 24)) {k, l}) {a, b} ⊆
      {i, j} ∪ {k, l} ∪ {a, b} := by
    intro m hm
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hm ⊢
    tauto
  have hW : (({i, j} : Finset (Fin 24)) ∪ {k, l} ∪ {a, b}).card < 8 := by
    have h1 := Finset.card_union_le (({i, j} : Finset (Fin 24)) ∪ {k, l}) {a, b}
    have h2 := Finset.card_union_le ({i, j} : Finset (Fin 24)) {k, l}
    have h3 : ({i, j} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
    have h4 : ({k, l} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
    have h5 : ({a, b} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
    omega
  have hQ : pairVec i j * pairVec k l * pairVec a b ∈ golayC ↔
      symmDiff ({i, j} : Finset (Fin 24)) {k, l} = {a, b} := by
    rw [h15_mem_golayC, toAdd_mul, toAdd_mul, h15_toAdd_pairVec hij, h15_toAdd_pairVec hkl,
      h15_toAdd_pairVec hab, h15_ind_add, h15_ind_add, h15_ind_mem_iff hUW hW,
      h15_symmDiff_eq_empty_iff]
  rw [inv_eq_of_mul_eq_one_right (pairVec_sq i j), mem_sup_zpowers_iff' (pairVec_sq a b),
    h15_pair_mul_pair_mem_iff hij hkl, hQ]

theorem pairVec_mem_sup_iff {a b i j : Fin 24} (hab : a ≠ b) (hij : i ≠ j) :
    pairVec i j ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) ↔
      ({i, j} : Finset (Fin 24)) = {a, b} := by
  rw [mem_sup_zpowers_iff' (pairVec_sq a b), or_iff_right (pairVec_not_mem_golayC hij)]
  exact h15_pair_mul_pair_mem_iff hij hab

end CFSG.Quasithin.RonanH15
