module

public import CFSG.RankThree.PartOne.KFOUT3.Torus
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K]

theorem eq_one_of_mul_self_eq_one [CharP K 2] {a : K} (h : a * a = 1) : a = 1 := by
  have h2 : (a - 1) * (a - 1) = 0 := by
    linear_combination h + (1 - a) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem eq_of_mul_self_eq [CharP K 2] {a b : K} (h : a * a = b * b) : a = b := by
  have h2 : (a - b) * (a - b) = 0 := by
    linear_combination h + (b * b - a * b) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem ent_one (a b : Fin 3) : ent (1 : SL3 K) a b = if a = b then 1 else 0 := by
  simp [ent, Matrix.one_apply]

theorem sum_ent_sq {x : SL3 K} (hx : x * x = 1) (a b : Fin 3) :
    ∑ k, ent x a k * ent x k b = if a = b then 1 else 0 := by
  rw [← ent_mul, hx, ent_one]

theorem ent_eq_zero_of_diag_commute {v : Fin 3 → Kˣ} {hv : ∏ i, v i = 1} {x : SL3 K}
    (h : diagSL v hv * x = x * diagSL v hv) {a b : Fin 3} (hab : v a ≠ v b) : ent x a b = 0 := by
  have h1 := congrArg (fun y : SL3 K => ent y a b) h
  simp only [ent_diagSL_mul, ent_mul_diagSL] at h1
  have h2 : ((v a : K) - v b) * ent x a b = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Units.ext (sub_eq_zero.mp h3)) hab
  · exact h3

theorem eq_one_of_regular [CharP K 2] {v : Fin 3 → Kˣ} {hv : ∏ i, v i = 1} {x : SL3 K}
    (h : diagSL v hv * x = x * diagSL v hv) (hx : x * x = 1) (h01 : v 0 ≠ v 1) (h02 : v 0 ≠ v 2)
    (h12 : v 1 ≠ v 2) : x = 1 := by
  have hoff : ∀ a b : Fin 3, a ≠ b → ent x a b = 0 := by
    intro a b hab
    apply ent_eq_zero_of_diag_commute h
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | exact Ne.symm ‹_›
  have hdiag : ∀ a : Fin 3, ent x a a = 1 := by
    intro a
    have h1 := sum_ent_sq hx a a
    rw [Finset.sum_eq_single a (fun k _ hk => by rw [hoff a k (Ne.symm hk), zero_mul])
      (by simp)] at h1
    exact eq_one_of_mul_self_eq_one (by simpa using h1)
  apply Subtype.ext
  ext a b
  by_cases hab : a = b
  · subst hab
    simpa [ent] using hdiag a
  · simpa [ent, hab] using hoff a b hab

theorem two_equal [CharP K 2] {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {x : SL3 K} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (h_ac : ent x a c = 0) (h_ca : ent x c a = 0) (h_bc : ent x b c = 0) (h_cb : ent x c b = 0)
    {w : Fin 3 → Kˣ} {hw : ∏ i, w i = 1} (hwab : w a ≠ w b)
    (hcomm : Commute x (diagSL w hw * x * (diagSL w hw)⁻¹)) :
    ∃ (i j : Fin 3) (h : i ≠ j) (s : K), s ≠ 0 ∧ x = rt h s := by
  have hsq : ∀ i j, ent x i a * ent x a j + ent x i b * ent x b j + ent x i c * ent x c j =
      if i = j then 1 else 0 := by
    intro i j
    have := sum_ent_sq hx2 i j
    rwa [sum_three hab hac hbc] at this
  have eaa := hsq a a
  have ebb := hsq b b
  have ecc := hsq c c
  simp only [h_ac, h_ca, h_bc, h_cb, mul_zero, add_zero, ite_true] at eaa ebb ecc
  obtain ⟨y, hy⟩ : ∃ y : SL3 K, y = diagSL w hw * x * (diagSL w hw)⁻¹ := ⟨_, rfl⟩
  rw [← hy] at hcomm
  have hyent : ∀ i j, ent y i j = (w i : K) * ((w j)⁻¹ : Kˣ) * ent x i j := fun i j => by
    rw [hy]
    exact diagSL_conj_ent w hw x i j
  have hcm := congrArg (fun z : SL3 K => ent z a a) hcomm.eq
  simp only [ent_mul, sum_three hab hac hbc, hyent, h_ac, h_ca, mul_zero, add_zero] at hcm
  have hia : (w a : K) * ((w a)⁻¹ : Kˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hib : (w b : K) * ((w b)⁻¹ : Kˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbg : ent x a b * ent x b a = 0 := by
    have key : ent x a b * ent x b a * ((w b : K) * ((w a)⁻¹ : Kˣ) - (w a : K) * ((w b)⁻¹ : Kˣ)) =
        0 := by
      linear_combination hcm
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exfalso
      apply hwab
      apply Units.ext
      refine (eq_of_mul_self_eq ?_).symm
      linear_combination ((w a : K) * (w b : K)) * h - ((w b : K) * (w b : K)) * hia +
        ((w a : K) * (w a : K)) * hib
  have hα : ent x a a = 1 := eq_one_of_mul_self_eq_one (by linear_combination eaa - hbg)
  have hδ : ent x b b = 1 := by
    have : ent x a a = ent x b b := eq_of_mul_self_eq (by linear_combination eaa - ebb)
    rw [← this, hα]
  have hκ : ent x c c = 1 := eq_one_of_mul_self_eq_one (by linear_combination ecc)
  have hxent : ∀ i j, ent x i j = (if i = j then 1 else 0) +
      (if a = i ∧ b = j then ent x a b else 0) + (if b = i ∧ a = j then ent x b a else 0) := by
    intro i j
    rcases cover_three hab hac hbc i with rfl | rfl | rfl <;>
      rcases cover_three hab hac hbc j with rfl | rfl | rfl <;>
      simp [hα, hδ, hκ, h_ac, h_ca, h_bc, h_cb, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  by_cases hβ : ent x a b = 0
  · by_cases hγ : ent x b a = 0
    · exfalso
      apply hx1
      refine ent_ext fun i j => ?_
      have := hxent i j
      simp only [hβ, hγ, ite_self, add_zero] at this
      rw [this, ent_one]
    · refine ⟨b, a, hab.symm, ent x b a, hγ, ?_⟩
      refine ent_ext fun i j => ?_
      rw [hxent i j, ent_rt]
      simp [hβ]
  · have hγ : ent x b a = 0 := (mul_eq_zero.mp hbg).resolve_left hβ
    refine ⟨a, b, hab, ent x a b, hβ, ?_⟩
    refine ent_ext fun i j => ?_
    rw [hxent i j, ent_rt]
    simp [hγ]

theorem eq_rt_of_commute_conj [CharP K 2] {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ)
    {x : SL3 K} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    {t : SL3 K} (ht : t ∈ Tor p K) (htc : t ∉ Subgroup.center (SL3 K)) (htx : t * x = x * t)
    (hcomm : ∀ t' ∈ Tor p K, Commute x (t' * x * t'⁻¹)) :
    ∃ (i j : Fin 3) (h : i ≠ j) (s : K), s ≠ 0 ∧ x = rt h s := by
  obtain ⟨v, -, hv, rfl⟩ := mem_Tor_iff.mp ht
  have key : ∀ {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → v a = v b → v a ≠ v c →
      ∃ (i j : Fin 3) (h : i ≠ j) (s : K), s ≠ 0 ∧ x = rt h s := by
    intro a b c hab hac hbc hvab hvac
    refine two_equal hab hac hbc hx2 hx1 ?_ ?_ ?_ ?_ (tSep_ne hζ hab) (hcomm _ (tSep_mem hζ hab))
    · exact ent_eq_zero_of_diag_commute htx hvac
    · exact ent_eq_zero_of_diag_commute htx (Ne.symm hvac)
    · exact ent_eq_zero_of_diag_commute htx (hvab ▸ hvac)
    · exact ent_eq_zero_of_diag_commute htx (fun h => hvac (hvab.trans h.symm))
  by_cases h01 : v 0 = v 1
  · by_cases h02 : v 0 = v 2
    · exfalso
      apply htc
      apply diagSL_mem_center_of_const
      intro a
      fin_cases a
      · rfl
      · exact h01.symm
      · exact h02.symm
    · exact key (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) h01 h02
  · by_cases h02 : v 0 = v 2
    · exact key (a := 0) (b := 2) (c := 1) (by decide) (by decide) (by decide) h02 h01
    · by_cases h12 : v 1 = v 2
      · exact key (a := 1) (b := 2) (c := 0) (by decide) (by decide) (by decide) h12
          (Ne.symm h01)
      · exact absurd (eq_one_of_regular htx hx2 h01 h02 h12) hx1

end CFSG.RankThree.PartOne.KFOUT3
