module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2Mat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut

open Matrix

variable {F : Type*} [Field F]

theorem sq_eq_trace_smul_sub_det_smul (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem trace_eq_zero_of_mul_self_scalar {A : Matrix (Fin 2) (Fin 2) F}
    (hA : ∀ a : F, A ≠ a • (1 : Matrix (Fin 2) (Fin 2) F)) {s : F}
    (hs : A * A = s • (1 : Matrix (Fin 2) (Fin 2) F)) : A.trace = 0 := by
  by_contra h
  apply hA ((s + A.det) / A.trace)
  have h1 := sq_eq_trace_smul_sub_det_smul A
  rw [hs] at h1
  have h2 : A.trace • A = (s + A.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [add_smul, h1]; abel
  calc A = (A.trace)⁻¹ • (A.trace • A) := by rw [smul_smul, inv_mul_cancel₀ h, one_smul]
    _ = _ := by rw [h2, smul_smul, div_eq_inv_mul]

theorem exists_eq_smul_of_trace_eq_zero {A B : Matrix (Fin 2) (Fin 2) F} (h2 : (2 : F) ≠ 0)
    (hA : ∀ a : F, A ≠ a • (1 : Matrix (Fin 2) (Fin 2) F)) (hAB : A * B = B * A)
    (hA0 : A.trace = 0) (hB0 : B.trace = 0) : ∃ c : F, B = c • A := by
  obtain ⟨α, β, hB⟩ := exists_eq_add_smul_of_commute hA hAB
  refine ⟨β, ?_⟩
  have h3 : B.trace = 2 * α + β * A.trace := by
    rw [hB]; simp [Matrix.trace_fin_two]; ring
  rw [hA0, hB0, mul_zero, add_zero] at h3
  have hα : α = 0 := by
    have : (2 : F) * α = 0 := h3.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  rw [hB, hα, zero_smul, zero_add]


theorem exists_lift_commute {t : GL (Fin 2) F} (h2 : (2 : F) ≠ 0)
    (hx : ProjGenLinGroup.mk t ^ 2 ≠ 1) {h : ProjGenLinGroup (Fin 2) F}
    (hh : h * ProjGenLinGroup.mk t = ProjGenLinGroup.mk t * h) :
    ∃ g : GL (Fin 2) F, ProjGenLinGroup.mk g = h ∧
      (g : Matrix (Fin 2) (Fin 2) F) * t = t * (g : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨g₀, rfl⟩ := ProjGenLinGroup.mk_surjective h
  obtain ⟨a, ha⟩ := exists_normScalar_of_commute hh
  have hdg : (g₀ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]; exact (GeneralLinearGroup.det g₀).ne_zero
  have hdt : (t : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]; exact (GeneralLinearGroup.det t).ne_zero
  have hsq : (a : F) * a = 1 := by
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at this
    have h4 : ((a : F) ^ 2 - 1) * ((t : Matrix (Fin 2) (Fin 2) F).det *
        (g₀ : Matrix (Fin 2) (Fin 2) F).det) = 0 := by linear_combination (-1 : F) * this
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linear_combination h5
    · exact absurd h5 (mul_ne_zero hdt hdg)
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · refine ⟨g₀, rfl, ?_⟩
    rw [h1] at ha
    exact NormScalar.one_iff.mp ha
  · exfalso
    rw [h1] at ha
    unfold NormScalar at ha
    have hg' : (g₀ : Matrix (Fin 2) (Fin 2) F) * ((g₀⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg : ((g₀⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g₀ : Matrix (Fin 2) (Fin 2) F)
        = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e1 := congrArg (fun N => Matrix.trace (N * ((g₀⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F))) ha
    simp only [Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_assoc, hg', Matrix.mul_one] at e1
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hg, Matrix.mul_one] at e1
    have htr : (t : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
      have : (2 : F) * (t : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        simp at e1
        linear_combination e1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · exact h
    apply hx
    have hsq2 := sq_eq_trace_smul_sub_det_smul (t : Matrix (Fin 2) (Fin 2) F)
    rw [htr, zero_smul, zero_sub] at hsq2
    have hne : -(t : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := neg_ne_zero.mpr hdt
    have : t * t = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ hne) := by
      apply Units.ext
      rw [Units.val_mul, coe_scalar_eq_smul_one, Units.val_mk0, hsq2, neg_smul]
    rw [pow_two, ← map_mul, this, ProjGenLinGroup.mk_scalar]

theorem exists_mul_self_scalar_of_sq_eq_one {g : GL (Fin 2) F}
    (h : ProjGenLinGroup.mk g ^ 2 = 1) :
    ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) * g = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [pow_two, ← map_mul, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  rw [← Units.val_mul, ← hu, coe_scalar_eq_smul_one]

theorem eq_of_involutions_of_commute {T : Matrix (Fin 2) (Fin 2) F} (h2 : (2 : F) ≠ 0)
    (hT : ∀ a : F, T ≠ a • (1 : Matrix (Fin 2) (Fin 2) F)) {g g' : GL (Fin 2) F}
    (hg : T * g = g * T) (hg' : T * g' = g' * T)
    (hgg : ProjGenLinGroup.mk g ^ 2 = 1) (hgg' : ProjGenLinGroup.mk g' ^ 2 = 1)
    (hg1 : ProjGenLinGroup.mk g ≠ 1) (hg'1 : ProjGenLinGroup.mk g' ≠ 1) :
    ProjGenLinGroup.mk g = ProjGenLinGroup.mk g' := by
  obtain ⟨s, hs⟩ := exists_mul_self_scalar_of_sq_eq_one hgg
  obtain ⟨s', hs'⟩ := exists_mul_self_scalar_of_sq_eq_one hgg'
  have hA := nonscalar_of_ne_one hg1
  have hA' := nonscalar_of_ne_one hg'1
  have ht := trace_eq_zero_of_mul_self_scalar hA hs
  have ht' := trace_eq_zero_of_mul_self_scalar hA' hs'
  have hcomm : (g : Matrix (Fin 2) (Fin 2) F) * g' = g' * g :=
    commute_of_commute_of_nonscalar hT hg hg'
  obtain ⟨c, hc⟩ := exists_eq_smul_of_trace_eq_zero h2 hA hcomm ht ht'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact g'.ne_zero (by simpa using hc)
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [coe_mul_scalar, Units.val_mk0]
  exact hc.symm


theorem isCyclic_of_unique_involution' {P : Type*} [CommGroup P] [Finite P] (hP : IsPGroup 2 P)
    (h1 : ∀ a b : P, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b) : IsCyclic P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := P) (Monoid.ExponentExists.of_finite)
  by_contra hncyc
  have hne : Subgroup.zpowers g ≠ ⊤ := by
    intro htop
    exact hncyc ⟨g, fun x => by
      have hx : x ∈ Subgroup.zpowers g := htop ▸ Subgroup.mem_top x
      exact hx⟩
  have hex : ∃ h : P, h ∉ Subgroup.zpowers g ∧ h ^ 2 ∈ Subgroup.zpowers g := by
    obtain ⟨y, hy⟩ : ∃ y : P, y ∉ Subgroup.zpowers g := by
      by_contra hall
      push Not at hall
      exact hne (eq_top_iff.mpr fun x _ => hall x)
    obtain ⟨e, he⟩ := hP y
    have hex' : ∃ k : ℕ, y ^ 2 ^ k ∈ Subgroup.zpowers g := ⟨e, by rw [he]; exact one_mem _⟩
    let k := Nat.find hex'
    have hk : y ^ 2 ^ k ∈ Subgroup.zpowers g := Nat.find_spec hex'
    have hk0 : k ≠ 0 := by
      intro h0
      have : y ^ 2 ^ k = y := by rw [h0, pow_zero, pow_one]
      exact hy (this ▸ hk)
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨y ^ 2 ^ k', fun hmem => ?_, ?_⟩
    · have := Nat.find_min hex' (show k' < k by omega)
      exact this hmem
    · rw [← pow_mul, ← pow_succ, show k' + 1 = k by omega]
      exact hk
  obtain ⟨h, hh, hh2⟩ := hex
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hh2
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) g
  have hord_h : h ^ orderOf g = 1 := by
    rw [hg]
    exact Monoid.pow_exponent_eq_one h
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  ·
    rw [pow_zero] at hm
    rw [hm, pow_one] at hord_h
    exact hh (by rw [hord_h]; exact one_mem _)
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hgi : g ^ (i * (2 : ℤ) ^ m') = 1 := by
      have h3 : (h ^ 2) ^ 2 ^ m' = 1 := by
        rw [← pow_mul, show 2 * 2 ^ m' = 2 ^ (m' + 1) by ring, ← hm]
        exact hord_h
      rw [← hi, ← zpow_natCast, ← _root_.zpow_mul] at h3
      push_cast at h3
      exact h3
    have hdvd : ((2 ^ (m' + 1) : ℕ) : ℤ) ∣ i * (2 : ℤ) ^ m' := by
      rw [← hm]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hgi
    obtain ⟨j, hj⟩ : (2 : ℤ) ∣ i := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h2 : (2 : ℤ) ^ m' ≠ 0 := pow_ne_zero _ (by norm_num)
      have : i * 2 ^ m' = (2 * c) * 2 ^ m' := by rw [hc]; push_cast; ring
      exact mul_right_cancel₀ h2 this
    set u := h * (g ^ j)⁻¹ with hu
    have hu2 : u ^ 2 = 1 := by
      rw [hu, mul_pow, inv_pow, ← zpow_natCast (g ^ j), ← _root_.zpow_mul, ← hi, hj]
      rw [show ((j : ℤ) * ((2 : ℕ) : ℤ)) = 2 * j by push_cast; ring]
      exact mul_inv_cancel _
    have hu1 : u ≠ 1 := by
      intro h1'
      apply hh
      have : h = g ^ j := by rw [hu] at h1'; exact (mul_inv_eq_one.mp h1')
      rw [this]
      exact Subgroup.zpow_mem_zpowers g j
    have hu_out : u ∉ Subgroup.zpowers g := by
      intro hmem
      apply hh
      have : h = u * g ^ j := by rw [hu]; group
      rw [this]
      exact mul_mem hmem (Subgroup.zpow_mem_zpowers g j)
    set v := g ^ 2 ^ m' with hv
    have hv2 : v ^ 2 = 1 := by
      rw [hv, ← pow_mul, show 2 ^ m' * 2 = 2 ^ (m' + 1) by ring, ← hm]
      exact pow_orderOf_eq_one g
    have hv1 : v ≠ 1 := by
      intro h1'
      have hdvd' := orderOf_dvd_of_pow_eq_one h1'
      rw [hm] at hdvd'
      have := Nat.le_of_dvd (by positivity) hdvd'
      have : 2 ^ (m' + 1) ≤ 2 ^ m' := this
      have h2 : 2 ^ m' < 2 ^ (m' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have := h1 u v hu2 hv2 hu1 hv1
    exact hu_out (this ▸ Subgroup.npow_mem_zpowers g _)


theorem isCyclic_of_isPGroup_two_of_le_centralizer [Finite F] (h2 : (2 : F) ≠ 0)
    {x : ProjGenLinGroup (Fin 2) F} (hx : x ^ 2 ≠ 1) {Q : Subgroup (ProjGenLinGroup (Fin 2) F)}
    (hQ : IsPGroup 2 Q) (hc : ∀ q ∈ Q, q * x = x * q) : IsCyclic Q := by
  obtain ⟨t, rfl⟩ := ProjGenLinGroup.mk_surjective x
  have hx1 : ProjGenLinGroup.mk t ≠ 1 := fun h => hx (by rw [h, one_pow])
  have hT := nonscalar_of_ne_one hx1
  have hlift : ∀ q ∈ Q, ∃ g : GL (Fin 2) F, ProjGenLinGroup.mk g = q ∧
      (t : Matrix (Fin 2) (Fin 2) F) * g = g * t := fun q hq => by
    obtain ⟨g, hg, hgt⟩ := exists_lift_commute h2 hx (hc q hq)
    exact ⟨g, hg, hgt.symm⟩
  have : Finite (ProjGenLinGroup (Fin 2) F) := Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have hcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    obtain ⟨ga, hga, hga'⟩ := hlift a a.2
    obtain ⟨gb, hgb, hgb'⟩ := hlift b b.2
    apply Subtype.ext
    change (a : ProjGenLinGroup (Fin 2) F) * b = b * a
    rw [← hga, ← hgb, ← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_commute_of_nonscalar hT hga' hgb'
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  refine isCyclic_of_unique_involution' hQ ?_
  intro a b ha hb ha1 hb1
  obtain ⟨ga, hga, hga'⟩ := hlift a a.2
  obtain ⟨gb, hgb, hgb'⟩ := hlift b b.2
  apply Subtype.ext
  have ha' : (a : ProjGenLinGroup (Fin 2) F) ^ 2 = 1 := by
    simpa using congrArg Subtype.val ha
  have hb' : (b : ProjGenLinGroup (Fin 2) F) ^ 2 = 1 := by
    simpa using congrArg Subtype.val hb
  have ha1' : (a : ProjGenLinGroup (Fin 2) F) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : ProjGenLinGroup (Fin 2) F) ≠ 1 := fun h => hb1 (Subtype.ext h)
  rw [← hga] at ha' ha1' ⊢
  rw [← hgb] at hb' hb1' ⊢
  exact eq_of_involutions_of_commute h2 hT hga' hgb' ha' hb' ha1' hb1'

end CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut
