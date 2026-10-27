module

public import CFSG.Walter.ReeOrder.Ward.BasicSet
public import CFSG.CharacterTheory.SmallDefect.ClassMultiplication

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

namespace WardL

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (W : WardL L q e)

theorem conj_apply_R {θ : L → ℂ} (hθ : θ ∈ W.RFam) (y : L) : starRingEnd ℂ (θ y) = θ y :=
  congrFun (W.conj_R θ hθ) y

theorem conj_apply_S {θ : L → ℂ} (hθ : θ ∈ W.SFam) (y : L) : starRingEnd ℂ (θ y) = θ y :=
  congrFun (W.conj_S θ hθ) y

theorem conj_apply_θ4 (y : L) : starRingEnd ℂ (W.θ4 y) = W.θ4 y := congrFun W.conj_θ4 y

theorem sum_R_Ro {r : L} (hr : r ∈ W.Ro) (hr1 : r ≠ 1) : ∑ θ ∈ W.RFam, θ r = e := by
  have h := sum_irr_mul_conj r W.unip
  have hnc : ¬ IsConj r W.unip := fun hc => W.unip_not_conj r hr hc.symm
  simp only [hnc, ↓reduceIte] at h
  rw [W.sum_irr] at h
  obtain ⟨h2, h3, h4, hS⟩ := W.val_Ro r hr hr1
  obtain ⟨-, hu4, huR, -⟩ := W.unip_vals
  have hRsum : ∑ θ ∈ W.RFam, θ r * starRingEnd ℂ (θ W.unip) = -e * ∑ θ ∈ W.RFam, θ r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [huR θ hθ, map_neg, conj_e]
    ring
  have hSsum : ∑ θ ∈ W.SFam, θ r * starRingEnd ℂ (θ W.unip) = 0 :=
    Finset.sum_eq_zero fun θ hθ => by rw [hS θ hθ, zero_mul]
  rw [hRsum, hSsum, h2, h3, hu4] at h
  simp only [Pi.one_apply, map_one, mul_one, zero_mul, map_zero, mul_zero, add_zero] at h
  have he := W.e_sq_complex
  linear_combination (-(e : ℂ)) * h - (∑ θ ∈ W.RFam, θ r) * he

theorem sum_sq_R_Ro {r : L} (hr : r ∈ W.Ro) (hr1 : r ≠ 1) :
    ∑ θ ∈ W.RFam, θ r * θ r = (Nat.card W.Ro : ℂ) - 2 := by
  have h := sum_irr_mul_conj r r
  simp only [IsConj.refl, ↓reduceIte] at h
  rw [W.Ro_centralizer r hr hr1, W.sum_irr] at h
  obtain ⟨h2, h3, h4, hS⟩ := W.val_Ro r hr hr1
  have hRsum : ∑ θ ∈ W.RFam, θ r * starRingEnd ℂ (θ r) = ∑ θ ∈ W.RFam, θ r * θ r :=
    Finset.sum_congr rfl fun θ hθ => by rw [W.conj_apply_R hθ]
  have hSsum : ∑ θ ∈ W.SFam, θ r * starRingEnd ℂ (θ r) = 0 :=
    Finset.sum_eq_zero fun θ hθ => by rw [hS θ hθ, zero_mul]
  rw [hRsum, hSsum, h2, h3, h4] at h
  simp only [Pi.one_apply, map_one, mul_one, zero_mul, map_neg, conj_e, add_zero] at h
  have he := W.e_sq_complex
  linear_combination h - he

theorem R_agree {θ θ' : L → ℂ} (hθ : θ ∈ W.RFam) (hθ' : θ' ∈ W.RFam) {y : L}
    (hy : ∀ g : L, g⁻¹ * y * g ∈ W.Ro → g⁻¹ * y * g = 1) : θ y = θ' y := by
  rcases Nat.even_or_odd (orderOf y) with hev | hodd
  · rw [W.R_even hθ hev, W.R_even hθ' hev]
  · rcases W.odd_classes y hodd with rfl | ⟨g, hg, hg1⟩ | ⟨g, hg, hg1⟩ | ⟨-, -, hR, -⟩
    · rw [W.degR θ hθ, W.degR θ' hθ']
    · exact absurd (hy g hg) hg1
    · obtain ⟨-, -, -, hR⟩ := W.val_So _ hg hg1
      rw [← conj_eq (W.R_mem hθ) g y, ← conj_eq (W.R_mem hθ') g y, hR θ hθ, hR θ' hθ']
    · rw [hR θ hθ, hR θ' hθ']

omit [Fintype L] in
theorem involutions_invariant [Fintype L] :
    ∀ x ∈ (Finset.univ.filter fun x : L => orderOf x = 2), ∀ g : L,
      g * x * g⁻¹ ∈ (Finset.univ.filter fun x : L => orderOf x = 2) := by
  intro x hx g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]

theorem sum_involutions {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    ∑ x ∈ (Finset.univ.filter fun x : L => orderOf x = 2), θ x =
      (Nat.card (ConjClasses.mk W.J').carrier : ℂ) * θ W.J' := by
  have h := sum_isConj_mul (blocksVChar_isClassFunction (AddSubgroup.subset_closure hθ)) W.J'
  rw [← h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff : orderOf x = 2 ↔ IsConj x W.J' := by
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := W.involution_conj x hx
      exact isConj_iff.mpr ⟨g⁻¹, by rw [← hg]; group⟩
    · intro hc
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      have ho : orderOf (c * x * c⁻¹) = orderOf x := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      rw [← ho, hc, W.orderOf_J']
  by_cases hx : orderOf x = 2
  · simp only [hx, hiff.mp hx, ↓reduceIte, one_mul]
  · have hx' : ¬ IsConj x W.J' := fun h => hx (hiff.mpr h)
    simp only [hx, hx', ↓reduceIte, zero_mul]

theorem card_class_J' : (Nat.card (ConjClasses.mk W.J').carrier : ℂ) * ((q : ℂ) - e) =
    Nat.card L := by
  have h := card_conjClass_mul_card_centralizer W.J'
  have h2 : ((Nat.card (Subgroup.centralizer ({W.J'} : Set L)) : ℤ) : ℂ) = (q : ℂ) - e := by
    rw [W.card_centralizer_J']
    push_cast
    ring
  push_cast at h2
  rw [← h2]
  exact_mod_cast h

theorem card_inv_pairs {r : L} (hr : r ∈ W.Ro) (hr1 : r ≠ 1) :
    ((((Finset.univ.filter fun x : L => orderOf x = 2) ×ˢ
        (Finset.univ.filter fun x : L => orderOf x = 2)).filter
          fun p => p.1 * p.2 = r).card : ℂ) = ((q : ℂ) + e) / 2 := by
  rw [card_mul_eq _ _ (involutions_invariant (L := L)) (involutions_invariant (L := L)) r,
    W.sum_irr]
  obtain ⟨h2, h3, h4, hS⟩ := W.val_Ro r hr hr1
  have hJ' := W.val_J'So 1 W.So.one_mem
  rw [mul_one] at hJ'
  obtain ⟨j2, j3, j4, jR⟩ := hJ'
  set c := (Nat.card (ConjClasses.mk W.J').carrier : ℂ) with hc
  have hRsum : ∑ θ ∈ W.RFam, (∑ x ∈ (Finset.univ.filter fun x : L => orderOf x = 2), θ x) *
      (∑ x ∈ (Finset.univ.filter fun x : L => orderOf x = 2), θ x) *
        starRingEnd ℂ (θ r) / θ 1 = 0 :=
    Finset.sum_eq_zero fun θ hθ => by
      rw [W.sum_involutions (W.R_mem hθ), jR θ hθ, mul_zero, zero_mul, zero_mul, zero_div]
  have hSsum : ∑ θ ∈ W.SFam, (∑ x ∈ (Finset.univ.filter fun x : L => orderOf x = 2), θ x) *
      (∑ x ∈ (Finset.univ.filter fun x : L => orderOf x = 2), θ x) *
        starRingEnd ℂ (θ r) / θ 1 = 0 :=
    Finset.sum_eq_zero fun θ hθ => by
      rw [hS θ hθ, map_zero, mul_zero, zero_div]
  rw [hRsum, hSsum, W.sum_involutions W.one_mem, W.sum_involutions W.θ2_mem,
    W.sum_involutions W.θ3_mem, W.sum_involutions W.θ4_mem, h2, h3, h4, W.deg4, j4]
  simp only [Pi.one_apply, map_one, div_one, mul_one, map_zero, mul_zero, zero_div, add_zero,
    map_neg, conj_e]
  have hcard := W.card_class_J'
  have hL : (2 : ℂ) * Nat.card L = q * ((q : ℂ) ^ 2 - 1) := by
    have h := W.card
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by have := W.q_ge; omega)
    have h' : ((2 * Nat.card L : ℕ) : ℂ) = ((q * (q ^ 2 - 1) : ℕ) : ℂ) := by rw [h]
    push_cast [Nat.cast_sub h1] at h'
    linear_combination h'
  have hq0 : (q : ℂ) ≠ 0 := by
    have := W.q_ge
    exact_mod_cast (show q ≠ 0 by omega)
  have hqe : (q : ℂ) - e ≠ 0 := by
    intro h
    have : (q : ℤ) = e := by exact_mod_cast (sub_eq_zero.mp h)
    have := W.int_facts
    omega
  have he := W.e_sq_complex
  have hc2 : 2 * c = q * (q + e) := by
    have hprod : ((q : ℂ) - e) * (2 * c - q * (q + e)) = 0 := by
      rw [← hcard] at hL
      linear_combination hL + (q : ℂ) * he
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hqe
    · linear_combination h
  rw [← hcard]
  field_simp
  linear_combination ((q : ℂ) - (e : ℂ) ^ 3) * hc2 -
    ((q : ℂ) ^ 2 * e + (q : ℂ) * (e : ℂ) ^ 2) * he

end WardL

end CFSG.Walter.Ward
