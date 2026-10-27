module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152

theorem ch_fin_two {F : Type*} [CommRing F] (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Nat.reduceAdd, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne,
      Matrix.one_apply_eq, mul_one, mul_zero, sub_zero] <;> ring

theorem trace_eq_neg_one_of_cube {F : Type*} [Field F] (g : Matrix (Fin 2) (Fin 2) F)
    (hdet : g.det = 1) (h3 : g * g * g = 1) (hne : g ≠ 1) : g.trace = -1 := by
  by_contra ht
  have hch := ch_fin_two g
  rw [hdet, one_smul] at hch
  set t := g.trace with htdef
  have h1 : t + 1 ≠ 0 := fun h => ht (by linear_combination h)
  have hcube : g * g * g = (t ^ 2 - 1) • g - t • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hch, sub_mul, smul_mul_assoc, one_mul, hch]
    module
  rw [hcube] at h3
  have h4 : (t + 1) • ((t - 1) • g - (1 : Matrix (Fin 2) (Fin 2) F)) = 0 := by
    have : (t + 1) • ((t - 1) • g - (1 : Matrix (Fin 2) (Fin 2) F)) =
        (t ^ 2 - 1) • g - t • (1 : Matrix (Fin 2) (Fin 2) F) - 1 := by module
    rw [this, h3, sub_self]
  have h5 : (t - 1) • g - (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rcases smul_eq_zero.mp h4 with h | h
    · exact absurd h h1
    · exact h
  have h6 : (t - 1) • g = 1 := sub_eq_zero.mp h5
  have h7 : t - 1 ≠ 0 := by
    intro h
    rw [h, zero_smul] at h6
    have := congrFun (congrFun h6 0) 0
    simp at this
  have hg : g = (t - 1)⁻¹ • 1 := by
    rw [← h6, smul_smul, inv_mul_cancel₀ h7, one_smul]
  set c : F := (t - 1)⁻¹ with hc
  have hct : c * (t - 1) = 1 := inv_mul_cancel₀ h7
  have hc2 : c ^ 2 = 1 := by
    have h := hdet
    rw [hg, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h
    simpa using h
  have htc : t = 2 * c := by
    have h : t = g.trace := htdef
    rw [h, hg, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    simp [two_mul, mul_comm]
  rw [htc] at hct
  have hc1 : c = 1 := by linear_combination (-1 : F) * hct + 2 * hc2
  apply hne
  rw [hg, hc1, one_smul]

theorem trace_eq_neg_one_of_gl {F : Type*} [Field F] (g : GL (Fin 2) F)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1) (h3 : g ^ 3 = 1) (hne : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) F).trace = -1 := by
  apply trace_eq_neg_one_of_cube _ hdet
  · have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h3
    simpa [pow_succ] using this
  · intro h
    exact hne (Units.ext h)

theorem false_of_nine_in_sl_two {F : Type*} [Field F] (h3 : (3 : F) ≠ 0) {E : Type*} [Group E]
    (hE : Nat.card E = 9) (hE3 : ∀ x : E, x ^ 3 = 1) (f : E →* GL (Fin 2) F)
    (hf : Function.Injective f)
    (hdet : ∀ x : E, ((f x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1) : False := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE]; norm_num)
  obtain ⟨x, hx1⟩ := exists_ne (1 : E)
  have hxcard : Nat.card (Subgroup.zpowers x) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hE3 x))
  obtain ⟨y, hy⟩ : ∃ y : E, y ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.zpowers x = ⊤ := Subgroup.eq_top_iff' _ |>.mpr hall
    rw [htop, Subgroup.card_top, hE] at hxcard
    omega
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hxy : x * y ≠ 1 := by
    intro h
    exact hy (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hxxy : x * x * y ≠ 1 := by
    intro h
    apply hy
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x))
  have hne : ∀ a : E, a ≠ 1 → f a ≠ 1 := fun a ha h => ha (hf (h.trans (map_one f).symm))
  have hpow : ∀ a : E, (f a) ^ 3 = 1 := fun a => by rw [← map_pow, hE3 a, map_one]
  have tx := trace_eq_neg_one_of_gl (f x) (hdet x) (hpow x) (hne x hx1)
  have ty := trace_eq_neg_one_of_gl (f y) (hdet y) (hpow y) (hne y hy1)
  have txy := trace_eq_neg_one_of_gl (f (x * y)) (hdet _) (hpow _) (hne _ hxy)
  have txxy := trace_eq_neg_one_of_gl (f (x * x * y)) (hdet _) (hpow _) (hne _ hxxy)
  have hch := ch_fin_two ((f x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [hdet x, one_smul] at hch
  have hm : ((f (x * x * y) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (f x : Matrix (Fin 2) (Fin 2) F) * (f x) * (f y) := by simp
  rw [hm, hch, sub_mul, smul_mul_assoc, one_mul, Matrix.trace_sub, Matrix.trace_smul] at txxy
  have hxy' : ((f (x * y) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (f x : Matrix (Fin 2) (Fin 2) F) * (f y) := by simp
  rw [hxy'] at txy
  rw [txy, tx, ty] at txxy
  apply h3
  simp only [smul_eq_mul] at txxy
  linear_combination txxy

end CFSG.RankThree.PartTwo.KFacts.KS152
