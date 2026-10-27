module

public import CFSG.Quasithin.Vol2.Ch11SecGTransv

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG.SL2

open Matrix
open scoped MatrixGroups

variable {k : Type} [Field k]

theorem sq_eq_one_of_mem_center {z : SL(2, k)} (hz : z ∈ Subgroup.center SL(2, k)) :
    z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

@[expose] def wElt : SL(2, k) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def tElt : SL(2, k) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_wElt : ((wElt : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl

theorem coe_tElt : ((tElt : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, 1; 0, 1] := rfl

theorem wElt_sq_mem_center : (wElt : SL(2, k)) ^ 2 ∈ Subgroup.center SL(2, k) := by
  have hw2 : (((wElt : SL(2, k)) ^ 2 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = -1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_wElt]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, hw2, mul_neg, mul_one, neg_mul, one_mul]

theorem tElt_mul_wElt_ne : (tElt : SL(2, k)) * wElt ≠ wElt * tElt := by
  intro h
  have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp [coe_wElt, coe_tElt, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem wElt_not_mem_center : (wElt : SL(2, k)) ∉ Subgroup.center SL(2, k) :=
  fun h => tElt_mul_wElt_ne (Subgroup.mem_center_iff.mp h tElt)

theorem tElt_not_mem_center : (tElt : SL(2, k)) ∉ Subgroup.center SL(2, k) :=
  fun h => tElt_mul_wElt_ne (Subgroup.mem_center_iff.mp h wElt).symm

theorem eq_bot_of_normal_of_odd [Finite k] (hk : 4 ≤ Nat.card k) (N : Subgroup SL(2, k))
    (hN : N.Normal) (hodd : ∀ n ∈ N, ∃ m : ℕ, Odd m ∧ n ^ m = 1) : N = ⊥ := by
  have hs : IsSimpleGroup PSL(2, k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hk
  set Z := Subgroup.center SL(2, k) with hZ
  have key : ∀ (S : Subgroup SL(2, k)) (n : SL(2, k)), n ∈ N → n ^ 2 ∈ S → n ∈ S := by
    intro S n hn hn2
    obtain ⟨m, hm, hnm⟩ := hodd n hn
    have h1 : n ^ m ∈ S := by
      rw [hnm]
      exact one_mem S
    have h2 := pow_gcd_mem hn2 h1
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hm), pow_one] at h2
  have : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have hnZ : n ∈ Z := by
      have h1 : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem _ hn
      rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact key ⊥ n hn (by rw [Subgroup.mem_bot]; exact sq_eq_one_of_mem_center hnZ)
  · exfalso
    have h1 : QuotientGroup.mk' Z wElt ∈ N.map (QuotientGroup.mk' Z) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnw⟩ := h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnw
    have hwz : (wElt : SL(2, k)) = n * (n⁻¹ * wElt) := by group
    have hn2 : n ^ 2 ∈ Z := by
      have e : n = wElt * (n⁻¹ * wElt)⁻¹ := by group
      have hc : Commute (wElt : SL(2, k)) (n⁻¹ * wElt)⁻¹ :=
        Subgroup.mem_center_iff.mp (inv_mem hnw) wElt
      rw [e, hc.mul_pow 2]
      exact mul_mem wElt_sq_mem_center (pow_mem (inv_mem hnw) 2)
    have hnZ := key Z n hn hn2
    exact wElt_not_mem_center (by rw [hwz]; exact mul_mem hnZ hnw)

theorem pow_180_eq_one [Finite k] (hk : Nat.card k = 4) (s : SL(2, k)) : s ^ 180 = 1 := by
  have : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card (GL (Fin 2) k) = 180 := by
    rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hk]
    simp [Fin.prod_univ_two]
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_pow, map_one, ← hcard]
  exact pow_card_eq_one'

theorem coe_tElt_pow (n : ℕ) :
    (((tElt : SL(2, k)) ^ n : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, (n : k); 0, 1] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, coe_tElt]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem exists_orderOf_eq [Finite k] {p : ℕ} (hp : p.Prime) (hk : Nat.card k = p) :
    ∃ x : PSL(2, k), orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype k := Fintype.ofFinite k
  have hpk : (p : k) = 0 := by
    rw [← hk, ← Fintype.card_eq_nat_card]
    exact FiniteField.cast_card_eq_zero k
  have htp : (tElt : SL(2, k)) ^ p = 1 := by
    ext i j
    rw [coe_tElt_pow, hpk]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨QuotientGroup.mk tElt, orderOf_eq_prime ?_ ?_⟩
  · rw [← QuotientGroup.mk_pow, htp, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff]
    exact tElt_not_mem_center

end CFSG.Quasithin.Vol2.Ch11.SecG.SL2
