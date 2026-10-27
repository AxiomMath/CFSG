module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolMCalc

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_GrOmega_dvd_of_zpow_eq_one {G : Type*} [Group G] (x : G) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (n : ℤ) (hn : x ^ n = 1) : (3 : ℤ) ∣ n := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have h := orderOf_dvd_iff_zpow_eq_one.mpr hn
  rw [hord] at h
  exact_mod_cast h

theorem aux_GrOmega_pow_three_mul {G : Type*} [Group G] (x : G) (n : ℤ) :
    x ^ (3 * n) = (x ^ 3) ^ n := by
  rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]

theorem aux_GrOmega_zpow_mod {G : Type*} [Group G] (x : G) (hx3 : x ^ 3 = 1) (n : ℤ) :
    x ^ n = x ^ (n % 3) := by
  have hx3' : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hx3
  have hn : n = n % 3 + 3 * (n / 3) := by omega
  conv_lhs => rw [hn]
  rw [zpow_add, zpow_mul, hx3', one_zpow, mul_one]

theorem aux_GrOmega_dvd_of_mem {G : Type*} [Group G] (d f : G) (hf3 : f ^ 3 = 1)
    (hfd : f ∉ Subgroup.zpowers d) (m : ℤ) (hm : f ^ m ∈ Subgroup.zpowers d) :
    (3 : ℤ) ∣ m := by
  have hr : f ^ (m % 3) ∈ Subgroup.zpowers d := by
    rw [← aux_GrOmega_zpow_mod f hf3 m]
    exact hm
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exact Int.dvd_of_emod_eq_zero h
  · rw [h, zpow_one] at hr
    exact absurd hr hfd
  · rw [h] at hr
    have h2 : (f ^ (2 : ℤ)) ^ (2 : ℤ) ∈ Subgroup.zpowers d :=
      (Subgroup.zpowers d).zpow_mem hr 2
    have hff : (f ^ (2 : ℤ)) ^ (2 : ℤ) = f := by
      rw [← zpow_mul, aux_GrOmega_zpow_mod f hf3 (2 * 2)]
      norm_num
    rw [hff] at h2
    exact absurd h2 hfd

theorem mem_A_of_cube_eq_one {G : Type*} [Group G] (A : Subgroup G) (y r d f : G)
    (hAexp : ∀ u ∈ A, u ^ 3 = 1) (hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hdA : d ∈ A) (hfA : f ∈ A) (hd1 : d ≠ 1)
    (hy3 : y ^ 3 ∈ Subgroup.zpowers d) (hy3ne : y ^ 3 ≠ 1)
    (hr3 : r ^ 3 = f) (hfd : f ∉ Subgroup.zpowers d)
    (hyr : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.zpowers d)
    (i j : ℤ) (u : G) (hu : u ∈ A) (h3 : (y ^ i * r ^ j * u) ^ 3 = 1) :
    y ^ i * r ^ j * u ∈ A := by
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hk : y * r * y⁻¹ * r⁻¹ ∈ A := hzA hyr
  have hf3 : f ^ 3 = 1 := hAexp f hfA
  have hz3 : (y ^ 3) ^ 3 = 1 := hAexp (y ^ 3) (hzA hy3)
  have hcube := cube_formula A y r hAexp hAy hAr hk i j u hu
  rw [h3, aux_GrOmega_pow_three_mul y i, aux_GrOmega_pow_three_mul r j, hr3] at hcube
  have hfj : f ^ j ∈ Subgroup.zpowers d := by
    have hzi : (y ^ 3) ^ i ∈ Subgroup.zpowers d := (Subgroup.zpowers d).zpow_mem hy3 i
    rw [eq_inv_of_mul_eq_one_right hcube.symm]
    exact (Subgroup.zpowers d).inv_mem hzi
  obtain ⟨j', rfl⟩ := aux_GrOmega_dvd_of_mem d f hf3 hfd j hfj
  have hfj1 : f ^ (3 * j') = 1 := by
    rw [aux_GrOmega_pow_three_mul f j', hf3, one_zpow]
  rw [hfj1, mul_one] at hcube
  obtain ⟨i', rfl⟩ := aux_GrOmega_dvd_of_zpow_eq_one (y ^ 3) hz3 hy3ne i hcube.symm
  have hyi : y ^ (3 * i') ∈ A := by
    rw [aux_GrOmega_pow_three_mul y i']
    exact hzA ((Subgroup.zpowers d).zpow_mem hy3 i')
  have hrj : r ^ (3 * j') ∈ A := by
    rw [aux_GrOmega_pow_three_mul r j', hr3]
    exact A.zpow_mem hfA j'
  exact A.mul_mem (A.mul_mem hyi hrj) hu

theorem g_r_comm_mem {G : Type*} [Group G] (A : Subgroup G) (y r d f g : G)
    (hAexp : ∀ u ∈ A, u ^ 3 = 1) (hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hdA : d ∈ A) (hfA : f ∈ A) (hd1 : d ≠ 1)
    (hy3 : y ^ 3 ∈ Subgroup.zpowers d) (hr3 : r ^ 3 = f) (hfd : f ∉ Subgroup.zpowers d)
    (hyr : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.zpowers d)
    (t : ℤ) (hgf : g * f * g⁻¹ = d ^ t * f)
    (hgr : ∃ (i j : ℤ) (u : G), u ∈ A ∧ g * r * g⁻¹ = y ^ i * r ^ j * u) :
    ∃ (i : ℤ) (u : G), u ∈ A ∧ g * r * g⁻¹ * r⁻¹ = y ^ i * u := by
  obtain ⟨i, j, u, hu, hgr⟩ := hgr
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hk : y * r * y⁻¹ * r⁻¹ ∈ A := hzA hyr
  have hf3 : f ^ 3 = 1 := hAexp f hfA
  have hcube : (g * r * g⁻¹) ^ 3 = (y ^ 3) ^ i * f ^ j := by
    rw [hgr, cube_formula A y r hAexp hAy hAr hk i j u hu, aux_GrOmega_pow_three_mul y i,
      aux_GrOmega_pow_three_mul r j, hr3]
  have hconj : (g * r * g⁻¹) ^ 3 = g * f * g⁻¹ := by
    rw [conj_pow, hr3]
  have hkey : (y ^ 3) ^ i * f ^ j = d ^ t * f := by
    rw [← hcube, hconj, hgf]
  have hfj1 : f ^ (j - 1) ∈ Subgroup.zpowers d := by
    have e : f ^ (j - 1) = ((y ^ 3) ^ i)⁻¹ * d ^ t := by
      rw [zpow_sub_one, eq_inv_mul_of_mul_eq hkey]
      group
    rw [e]
    exact (Subgroup.zpowers d).mul_mem
      ((Subgroup.zpowers d).inv_mem ((Subgroup.zpowers d).zpow_mem hy3 i))
      ((Subgroup.zpowers d).zpow_mem (Subgroup.mem_zpowers d) t)
  obtain ⟨j', hj'⟩ := aux_GrOmega_dvd_of_mem d f hf3 hfd (j - 1) hfj1
  obtain rfl : j = 1 + 3 * j' := by omega
  have hrj : r ^ (1 + 3 * j') = r * f ^ j' := by
    rw [zpow_add, zpow_one, aux_GrOmega_pow_three_mul r j', hr3]
  rw [hrj] at hgr
  have hw : f ^ j' * u ∈ A := A.mul_mem (A.zpow_mem hfA j') hu
  have hcommw : r * (f ^ j' * u) = f ^ j' * u * r := (hAr _ hw).symm
  refine ⟨i, f ^ j' * u, hw, ?_⟩
  calc g * r * g⁻¹ * r⁻¹ = y ^ i * (r * f ^ j') * u * r⁻¹ := by rw [hgr]
    _ = y ^ i * (r * (f ^ j' * u) * r⁻¹) := by simp only [mul_assoc]
    _ = y ^ i * (f ^ j' * u * r * r⁻¹) := by rw [hcommw]
    _ = y ^ i * (f ^ j' * u) := by group

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
