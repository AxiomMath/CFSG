module

public import CFSG.RankThree.PartOne.NF7J.Model2

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

theorem gl_pow8 : ∀ M : M32, det3 M = 1 → M ^ 8 = 1 → M ^ 4 = 1 := by decide +kernel

theorem gl_pow6 : ∀ M : M32, det3 M = 1 → M ^ 6 = 1 → M ^ 2 ≠ 1 → M ^ 3 = 1 := by decide +kernel

theorem unit_pow8 (x : GL (Fin 3) (ZMod 2)) (h : x ^ 8 = 1) : x ^ 4 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  apply gl_pow8 _ (det3_GL x)
  rw [← Units.val_pow_eq_pow_val, h]
  rfl

theorem unit_pow6 (x : GL (Fin 3) (ZMod 2)) (h : x ^ 6 = 1) (h2 : x ^ 2 ≠ 1) : x ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  apply gl_pow6 _ (det3_GL x)
  · rw [← Units.val_pow_eq_pow_val, h]
    rfl
  · intro h'
    apply h2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact h'

section Hnu

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} (D : Datum p E)

theorem Datum.ν_inv : D.ν⁻¹ = D.ν := inv_eq_of_mul_eq_one_right D.ν_sq

@[expose] def Datum.Hnu : Subgroup (MulAut E) where
  carrier := {g | g ∈ D.H ∨ D.ν * g ∈ D.H}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · left
      exact D.H.mul_mem ha hb
    · right
      have : D.ν * (a * b) = a * (D.ν * b) := by
        rw [← mul_assoc, ← D.ν_comm a, mul_assoc]
      rw [this]
      exact D.H.mul_mem ha hb
    · right
      have : D.ν * (a * b) = (D.ν * a) * b := by rw [mul_assoc]
      rw [this]
      exact D.H.mul_mem ha hb
    · left
      have : a * b = (D.ν * a) * (D.ν * b) := (D.νmul_νmul a b).symm
      rw [this]
      exact D.H.mul_mem ha hb
  one_mem' := Or.inl D.H.one_mem
  inv_mem' := by
    rintro a (ha | ha)
    · left
      exact D.H.inv_mem ha
    · right
      have : D.ν * a⁻¹ = (D.ν * a)⁻¹ := by
        rw [_root_.mul_inv_rev, D.ν_inv, ← D.ν_comm a⁻¹]
      rw [this]
      exact D.H.inv_mem ha

theorem Datum.reflectionGroup_le_Hnu : reflectionGroup p E ≤ D.Hnu := by
  apply (Subgroup.closure_le _).2
  intro t ht
  obtain ⟨a, ha, -, -, rfl⟩ := D.hD t ht
  right
  rw [D.ν_mul_ν_mul]
  exact ha

theorem Datum.mem_Hnu {g : MulAut E} (hg : g ∈ D.Hnu) :
    (g ∈ D.H) ∨ (∃ h ∈ D.H, g = D.ν * h) := by
  rcases hg with h | h
  · exact Or.inl h
  · exact Or.inr ⟨D.ν * g, h, by rw [D.ν_mul_ν_mul]⟩

theorem Datum.pow_eq_one_iff {h : MulAut E} (hh : h ∈ D.H) (n : ℕ) :
    h ^ n = 1 ↔ (D.e ⟨h, hh⟩) ^ n = 1 := by
  rw [← map_pow, map_eq_one_iff _ D.e.injective]
  constructor
  · intro h1
    exact Subtype.ext (by simpa using h1)
  · intro h1
    simpa using congrArg Subtype.val h1

theorem Datum.ν_pow (n : ℕ) : D.ν ^ (2 * n) = 1 := by
  rw [pow_mul, show D.ν ^ 2 = 1 by rw [pow_two]; exact D.ν_sq, one_pow]

theorem Datum.nu_mul_pow (h : MulAut E) (n : ℕ) : (D.ν * h) ^ n = D.ν ^ n * h ^ n :=
  (Commute.mul_pow (show Commute D.ν h from (D.ν_comm h).symm) n)

theorem Datum.nu_mul_pow_even (h : MulAut E) (n : ℕ) : (D.ν * h) ^ (2 * n) = h ^ (2 * n) := by
  rw [D.nu_mul_pow, D.ν_pow, one_mul]

include D in
theorem Datum.exp8 : ∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1 := by
  intro g hg h8
  rcases D.mem_Hnu (D.reflectionGroup_le_Hnu hg) with hH | ⟨h, hh, rfl⟩
  · rw [D.pow_eq_one_iff hH] at h8 ⊢
    exact unit_pow8 _ h8
  · have e8 : (D.ν * h) ^ 8 = h ^ 8 := D.nu_mul_pow_even h 4
    have e4 : (D.ν * h) ^ 4 = h ^ 4 := D.nu_mul_pow_even h 2
    rw [e8] at h8
    rw [e4]
    rw [D.pow_eq_one_iff hh] at h8 ⊢
    exact unit_pow8 _ h8

include D in
theorem Datum.exp6 : ∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = D.ν := by
  intro g hg h6 h3 h2
  rcases D.mem_Hnu (D.reflectionGroup_le_Hnu hg) with hH | ⟨h, hh, rfl⟩
  · exfalso
    apply h3
    rw [D.pow_eq_one_iff hH] at h6 ⊢
    refine unit_pow6 _ h6 ?_
    intro h'
    apply h2
    rw [D.pow_eq_one_iff hH]
    exact h'
  · have e6 : (D.ν * h) ^ 6 = h ^ 6 := D.nu_mul_pow_even h 3
    have e2 : (D.ν * h) ^ 2 = h ^ 2 := D.nu_mul_pow_even h 1
    rw [e6] at h6
    rw [e2] at h2
    have h3' : h ^ 3 = 1 := by
      rw [D.pow_eq_one_iff hh] at h6 ⊢
      refine unit_pow6 _ h6 ?_
      intro h'
      apply h2
      rwa [D.pow_eq_one_iff hh]
    rw [D.nu_mul_pow, h3', mul_one, pow_succ, pow_two, D.ν_sq, one_mul]

end Hnu

section KFRefl

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K) (D : Datum p E) (X : EFacts G p c E)

include X F D in
theorem exists_conj_r₀ {s : MulAut E} (hs : s ∈ reflectionSet p E) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      s = conjAut E w hw * F.r₀ * (conjAut E w hw)⁻¹ := by
  obtain ⟨a, ha, ha2, ha1, hsa⟩ := D.hD s hs
  obtain ⟨h, hh, hconj⟩ := Datum.exists_conj D (a₁_mem F D) ha (a₁_sq F D) (a₁_ne_one F D X) ha2 ha1
  obtain ⟨w, hw, hwe⟩ := D.exists_lift hh
  refine ⟨w, hw, ?_⟩
  rw [hsa, hwe, ← hconj]
  calc D.ν * (h * (D.ν * F.r₀) * h⁻¹) = (D.ν * h) * (D.ν * F.r₀) * h⁻¹ := by simp only [mul_assoc]
    _ = (h * D.ν) * (D.ν * F.r₀) * h⁻¹ := by rw [D.ν_comm h]
    _ = h * (D.ν * (D.ν * F.r₀)) * h⁻¹ := by simp only [mul_assoc]
    _ = h * F.r₀ * h⁻¹ := by rw [D.ν_mul_ν_mul]

include X F D in
theorem kfAt_refl {s : MulAut E} (hs : s ∈ reflectionSet p E) : KFAt p E f s := by
  obtain ⟨w, hw, hs'⟩ := exists_conj_r₀ F D X hs
  rw [hs']
  exact F.kfat₀.conj hw

include X F D in
theorem exists_conj_into_L {s : MulAut E} (hs : s ∈ reflectionSet p E) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L := by
  obtain ⟨w, hw, hs'⟩ := exists_conj_r₀ F D X hs
  refine ⟨w⁻¹, (Subgroup.normalizer (E : Set G)).inv_mem hw, ?_⟩
  rw [hs', Equivariance.conjAut_inv hw]
  have : (conjAut E w hw)⁻¹ * (conjAut E w hw * F.r₀ * (conjAut E w hw)⁻¹) *
      ((conjAut E w hw)⁻¹)⁻¹ = F.r₀ := by group
  rw [this]
  exact F.r₀_L

end KFRefl

end CFSG.RankThree.PartOne.NF7J
