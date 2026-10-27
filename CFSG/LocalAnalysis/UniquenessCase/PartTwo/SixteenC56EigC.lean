module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56EigA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56EigB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaEig

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

@[expose] def AdaptedQuad (A : Matrix OmI OmI K) (c : K) (e₀ f : OmI → K) : Prop :=
  ∃ (u u' : OmI → K) (l m : K), IsHypQuad e₀ u f u' ∧ A *ᵥ u = l • u ∧ A *ᵥ u' = m • u' ∧
    l * m = c

def perpPair (e₀ f : OmI → K) : Submodule K (OmI → K) where
  carrier := {r | pol e₀ r = 0 ∧ pol f r = 0}
  zero_mem' := ⟨pol_zero_right e₀, pol_zero_right f⟩
  add_mem' := by
    intro r s hr hs
    exact ⟨by rw [pol_add_right, hr.1, hs.1, add_zero],
      by rw [pol_add_right, hr.2, hs.2, add_zero]⟩
  smul_mem' := by
    intro t r hr
    exact ⟨by rw [pol_smul_right, hr.1, mul_zero],
      by rw [pol_smul_right, hr.2, mul_zero]⟩

theorem mem_perpPair {e₀ f r : OmI → K} :
    r ∈ perpPair e₀ f ↔ pol e₀ r = 0 ∧ pol f r = 0 := Iff.rfl

theorem pol_zero_left (w : OmI → K) : pol 0 w = 0 := by
  rw [pol_comm, pol_zero_right]

theorem exists_pol_ne_zero_of_mem_perpPair {e₀ f u : OmI → K} (hef : pol e₀ f = 1)
    (hu : u ∈ perpPair e₀ f) (hu0 : u ≠ 0) :
    ∃ s ∈ perpPair e₀ f, pol u s ≠ 0 := by
  have hw : ∃ w, pol u w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (eq_zero_of_pol_eq_zero h)
  obtain ⟨w, hwne⟩ := hw
  refine ⟨w + pol w f • e₀ + pol w e₀ • f, ?_, ?_⟩
  · rw [mem_perpPair]
    refine ⟨?_, ?_⟩
    · rw [pol_add_right, pol_add_right, pol_smul_right, pol_smul_right, pol_self e₀, hef,
        mul_zero, mul_one, add_zero, pol_comm w e₀]
      exact CharTwo.add_self_eq_zero (pol e₀ w)
    · rw [pol_add_right, pol_add_right, pol_smul_right, pol_smul_right, pol_self f,
        pol_comm f e₀, hef, mul_one, mul_zero, add_zero, pol_comm w f]
      exact CharTwo.add_self_eq_zero (pol f w)
  · have hue : pol u e₀ = 0 := by rw [pol_comm]; exact (mem_perpPair.mp hu).1
    have huf : pol u f = 0 := by rw [pol_comm]; exact (mem_perpPair.mp hu).2
    rw [pol_add_right, pol_add_right, pol_smul_right, pol_smul_right, hue, huf, mul_zero,
      mul_zero, add_zero, add_zero]
    exact hwne

theorem mulVec_mem_perpPair {A : Matrix OmI OmI K} {c : K} (hc0 : c ≠ 0)
    (hQ : ∀ v, quad (A *ᵥ v) = c * quad v) {e₀ f : OmI → K} (he₀ : A *ᵥ e₀ = e₀)
    (hf : A *ᵥ f = c • f) {r : OmI → K} (hr : r ∈ perpPair e₀ f) :
    A *ᵥ r ∈ perpPair e₀ f := by
  obtain ⟨hr0, hrf⟩ := mem_perpPair.mp hr
  refine mem_perpPair.mpr ⟨?_, ?_⟩
  · calc pol e₀ (A *ᵥ r) = pol (A *ᵥ e₀) (A *ᵥ r) := by rw [he₀]
      _ = c * pol e₀ r := pol_mulVec_of_similitude hQ e₀ r
      _ = 0 := by rw [hr0, mul_zero]
  · have h : pol (A *ᵥ f) (A *ᵥ r) = c * pol f r := pol_mulVec_of_similitude hQ f r
    rw [hf, pol_smul_left, hrf, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hc0

theorem pol_eq_zero_of_eigen_mul_ne {A : Matrix OmI OmI K} {c a b : K}
    (hQ : ∀ v, quad (A *ᵥ v) = c * quad v) {r s : OmI → K} (hr : A *ᵥ r = a • r)
    (hs : A *ᵥ s = b • s) (h : a * b ≠ c) : pol r s = 0 := by
  have key : c * pol r s = a * b * pol r s := by
    rw [← pol_mulVec_of_similitude hQ r s, hr, hs, pol_smul_left, pol_smul_right]
    ring
  have h2 : (a * b - c) * pol r s = 0 := by
    rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h)

theorem quad_eq_zero_of_eigen_sq_ne {A : Matrix OmI OmI K} {c a : K}
    (hQ : ∀ v, quad (A *ᵥ v) = c * quad v) {r : OmI → K} (hr : A *ᵥ r = a • r)
    (h : a ^ 2 ≠ c) : quad r = 0 := by
  have key : c * quad r = a ^ 2 * quad r := by
    rw [← hQ r, hr, quad_smul]
  have h2 : (a ^ 2 - c) * quad r = 0 := by
    rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h)

theorem sq_ne_of_mul_eq {c a b : K} (hc0 : c ≠ 0) (h : a * b = c) (ha : a ^ 2 ≠ c) :
    b ^ 2 ≠ c := by
  intro hb
  apply ha
  have hsq : (a * b) ^ 2 = c ^ 2 := by rw [h]
  rw [mul_pow, hb] at hsq
  have h2 : c * a ^ 2 = c * c := by rw [mul_comm c, hsq, pow_two]
  exact mul_left_cancel₀ hc0 h2

theorem exists_pol_eq_one_quad_eq_zero {e₀ f ρ : OmI → K} (hef : pol e₀ f = 1)
    (hρ : ρ ∈ perpPair e₀ f) (hQρ : quad ρ = 0) (hρ0 : ρ ≠ 0) :
    ∃ u' ∈ perpPair e₀ f, pol ρ u' = 1 ∧ quad u' = 0 := by
  obtain ⟨u₀, hu₀R, hu₀ne⟩ := exists_pol_ne_zero_of_mem_perpPair hef hρ hρ0
  set b : K := (pol ρ u₀)⁻¹ with hb_def
  have hb : b * pol ρ u₀ = 1 := by rw [hb_def, inv_mul_cancel₀ hu₀ne]
  set a : K := quad u₀ * b ^ 2 with ha_def
  refine ⟨b • u₀ + a • ρ, ?_, ?_, ?_⟩
  · exact (perpPair e₀ f).add_mem ((perpPair e₀ f).smul_mem b hu₀R)
      ((perpPair e₀ f).smul_mem a hρ)
  · rw [pol_add_right, pol_smul_right, pol_smul_right, pol_self, mul_zero, add_zero, hb]
  · rw [quad_add, quad_smul, quad_smul, hQρ, mul_zero, add_zero, pol_smul_left,
      pol_smul_right, pol_comm u₀ ρ]
    have hkey : b * (a * pol ρ u₀) = b ^ 2 * quad u₀ := by
      rw [ha_def, show b * (quad u₀ * b ^ 2 * pol ρ u₀) =
        b ^ 2 * quad u₀ * (b * pol ρ u₀) by ring, hb, mul_one]
    rw [hkey]
    exact CharTwo.add_self_eq_zero (b ^ 2 * quad u₀)

theorem adaptedQuad_of_eigen_ne {A : GL OmI K} (hA : A ^ (Fintype.card K - 1) = 1) {c : K}
    (hc0 : c ≠ 0) (hQ : ∀ v, quad ((A : Matrix OmI OmI K) *ᵥ v) = c * quad v)
    {e₀ f : OmI → K} (he₀ : (A : Matrix OmI OmI K) *ᵥ e₀ = e₀) (hQe : quad e₀ = 0)
    (hf : (A : Matrix OmI OmI K) *ᵥ f = c • f) (hQf : quad f = 0) (hef : pol e₀ f = 1)
    {u₁ : OmI → K} {ν₁ : K} (hu₁e : pol e₀ u₁ = 0) (hu₁f : pol f u₁ = 0) (hu₁ : u₁ ≠ 0)
    (hAu₁ : (A : Matrix OmI OmI K) *ᵥ u₁ = ν₁ • u₁) (hν₁ : ν₁ ^ 2 ≠ c) :
    AdaptedQuad (A : Matrix OmI OmI K) c e₀ f := by
  have hR : u₁ ∈ perpPair e₀ f := mem_perpPair.mpr ⟨hu₁e, hu₁f⟩
  have hQU : quad u₁ = 0 := quad_eq_zero_of_eigen_sq_ne hQ hAu₁ hν₁
  obtain ⟨s, hsR, hsne⟩ := exists_pol_ne_zero_of_mem_perpPair hef hR hu₁
  have hInv : ∀ r ∈ perpPair e₀ f, (A : Matrix OmI OmI K) *ᵥ r ∈ perpPair e₀ f :=
    fun r hr => mulVec_mem_perpPair hc0 hQ he₀ hf hr
  obtain ⟨w, hweig, hwR, hwsum⟩ := eigen_decomp A hA (perpPair e₀ f) hInv hsR
  have hsum : ∑ ν : Kˣ, pol u₁ (w ν) ≠ 0 := by
    rw [← pol_sum_right u₁ Finset.univ w, hwsum]
    exact hsne
  obtain ⟨ν, -, hνne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (f := fun ν : Kˣ => pol u₁ (w ν)) hsum
  have hνc : ν₁ * (ν : K) = c := by
    by_contra h
    exact hνne (pol_eq_zero_of_eigen_mul_ne hQ hAu₁ (hweig ν) h)
  let t : K := (pol u₁ (w ν))⁻¹
  let u' : OmI → K := t • w ν
  have hAu' : (A : Matrix OmI OmI K) *ᵥ u' = (ν : K) • u' := by
    change (A : Matrix OmI OmI K) *ᵥ (t • w ν) = (ν : K) • (t • w ν)
    rw [Matrix.mulVec_smul, hweig ν]
    exact smul_comm t (ν : K) (w ν)
  have hm : (ν : K) ^ 2 ≠ c := sq_ne_of_mul_eq hc0 hνc hν₁
  have hQu' : quad u' = 0 := quad_eq_zero_of_eigen_sq_ne hQ hAu' hm
  have hpol' : pol u₁ u' = 1 := by
    change pol u₁ (t • w ν) = 1
    rw [pol_smul_right]
    exact inv_mul_cancel₀ hνne
  have hu'R : u' ∈ perpPair e₀ f := by
    change t • w ν ∈ perpPair e₀ f
    exact (perpPair e₀ f).smul_mem t (hwR ν)
  have hquad : IsHypQuad e₀ u₁ f u' :=
    ⟨hQe, hQU, hQf, hQu', hef, hpol', (mem_perpPair.mp hR).1, (mem_perpPair.mp hu'R).1,
      (mem_perpPair.mp hR).2, (mem_perpPair.mp hu'R).2⟩
  exact ⟨u₁, u', ν₁, (ν : K), hquad, hAu₁, hAu', hνc⟩

theorem adaptedQuad_of_eigen_sq {A : GL OmI K} (hA : A ^ (Fintype.card K - 1) = 1) {c : K}
    (hc0 : c ≠ 0) (hQ : ∀ v, quad ((A : Matrix OmI OmI K) *ᵥ v) = c * quad v)
    {e₀ f : OmI → K} (he₀ : (A : Matrix OmI OmI K) *ᵥ e₀ = e₀) (hQe : quad e₀ = 0)
    (hf : (A : Matrix OmI OmI K) *ᵥ f = c • f) (hQf : quad f = 0) (hef : pol e₀ f = 1)
    (hall : ∀ (u : OmI → K) (ν : K), pol e₀ u = 0 → pol f u = 0 → u ≠ 0 →
      (A : Matrix OmI OmI K) *ᵥ u = ν • u → ν ^ 2 = c) :
    AdaptedQuad (A : Matrix OmI OmI K) c e₀ f := by
  obtain ⟨ν₀, hν₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have hν₀' : ν₀ ^ 2 = c := by rw [hν₀, pow_two]
  have hAeq : ∀ r ∈ perpPair e₀ f, (A : Matrix OmI OmI K) *ᵥ r = ν₀ • r := by
    intro r hr
    have hInv : ∀ s ∈ perpPair e₀ f, (A : Matrix OmI OmI K) *ᵥ s ∈ perpPair e₀ f :=
      fun s hs => mulVec_mem_perpPair hc0 hQ he₀ hf hs
    obtain ⟨w, hweig, hwR, hwsum⟩ := eigen_decomp A hA (perpPair e₀ f) hInv hr
    have hwν : ∀ ν : Kˣ, (A : Matrix OmI OmI K) *ᵥ (w ν) = ν₀ • w ν := by
      intro ν
      by_cases hν : w ν = 0
      · rw [hν, Matrix.mulVec_zero, smul_zero]
      · have hmem := mem_perpPair.mp (hwR ν)
        have hν2 : (ν : K) ^ 2 = c := hall (w ν) (ν : K) hmem.1 hmem.2 hν (hweig ν)
        have hνeq : (ν : K) = ν₀ := CharTwo.sq_inj.mp (by rw [hν2, hν₀'])
        rw [hweig ν, hνeq]
    calc (A : Matrix OmI OmI K) *ᵥ r
        = (A : Matrix OmI OmI K) *ᵥ (∑ ν : Kˣ, w ν) := by rw [hwsum]
      _ = ∑ ν : Kˣ, (A : Matrix OmI OmI K) *ᵥ w ν := Matrix.mulVec_sum _ Finset.univ _
      _ = ∑ ν : Kˣ, ν₀ • w ν := Finset.sum_congr rfl (fun ν _ => hwν ν)
      _ = ν₀ • ∑ ν : Kˣ, w ν := (Finset.smul_sum).symm
      _ = ν₀ • r := by rw [hwsum]
  have he₀ne : e₀ ≠ 0 := fun h => by
    rw [h, pol_zero_left] at hef
    exact one_ne_zero hef.symm
  obtain ⟨s, hQs, hsorth, hsnotin⟩ := exists_singular_orth_not_mem he₀ne
  set t : K := pol s f with ht_def
  set ρ : OmI → K := s + t • e₀ with hρ_def
  have hρR : ρ ∈ perpPair e₀ f := by
    rw [hρ_def, mem_perpPair]
    refine ⟨?_, ?_⟩
    · rw [pol_add_right, pol_smul_right, pol_self, mul_zero, add_zero]
      exact hsorth
    · rw [pol_add_right, pol_smul_right, pol_comm f e₀, hef, mul_one, ht_def, pol_comm s f]
      exact CharTwo.add_self_eq_zero (pol f s)
  have hQρ : quad ρ = 0 := by
    rw [hρ_def, quad_add, quad_smul, hQe, mul_zero, add_zero, pol_smul_right, pol_comm s e₀,
      hsorth, mul_zero, add_zero]
    exact hQs
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hs : s = (-t) • e₀ := by
      have h' : s + t • e₀ = 0 := by rw [← hρ_def]; exact h
      rw [add_eq_zero_iff_eq_neg.mp h', ← neg_smul]
    exact hsnotin (-t) hs
  obtain ⟨u', hu'R, hpolρu', hQu'⟩ := exists_pol_eq_one_quad_eq_zero hef hρR hQρ hρ0
  have hquad : IsHypQuad e₀ ρ f u' :=
    ⟨hQe, hQρ, hQf, hQu', hef, hpolρu', (mem_perpPair.mp hρR).1, (mem_perpPair.mp hu'R).1,
      (mem_perpPair.mp hρR).2, (mem_perpPair.mp hu'R).2⟩
  have hν₀mul : ν₀ * ν₀ = c := by simpa [pow_two] using hν₀'
  exact ⟨ρ, u', ν₀, ν₀, hquad, hAeq ρ hρR, hAeq u' hu'R, hν₀mul⟩

theorem adaptedQuad_of_eigen {A : GL OmI K} (hA : A ^ (Fintype.card K - 1) = 1) {c : K}
    (hc0 : c ≠ 0) (hQ : ∀ v, quad ((A : Matrix OmI OmI K) *ᵥ v) = c * quad v)
    {e₀ f : OmI → K} (he₀ : (A : Matrix OmI OmI K) *ᵥ e₀ = e₀) (hQe : quad e₀ = 0)
    (hf : (A : Matrix OmI OmI K) *ᵥ f = c • f) (hQf : quad f = 0) (hef : pol e₀ f = 1) :
    AdaptedQuad (A : Matrix OmI OmI K) c e₀ f := by
  by_cases h : ∃ (u : OmI → K) (ν : K), pol e₀ u = 0 ∧ pol f u = 0 ∧ u ≠ 0 ∧
      (A : Matrix OmI OmI K) *ᵥ u = ν • u ∧ ν ^ 2 ≠ c
  · obtain ⟨u, ν, hue, huf, hu, hAu, hν⟩ := h
    exact adaptedQuad_of_eigen_ne hA hc0 hQ he₀ hQe hf hQf hef hue huf hu hAu hν
  · push Not at h
    exact adaptedQuad_of_eigen_sq hA hc0 hQ he₀ hQe hf hQf hef
      (fun u ν hue huf hu hAu => h u ν hue huf hu hAu)

theorem exists_adapted_basis (A : GL OmI K) (hA : A ^ (Fintype.card K - 1) = 1) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hQ : ∀ v, quad ((A : Matrix OmI OmI K) *ᵥ v) = c * quad v)
    {e₀ f : OmI → K} (he₀ : (A : Matrix OmI OmI K) *ᵥ e₀ = e₀) (hQe : quad e₀ = 0)
    (hf : (A : Matrix OmI OmI K) *ᵥ f = c • f) (hQf : quad f = 0) (hef : pol e₀ f = 1) :
    ∃ (γ : GL OmI K) (l m : Kˣ), (∀ v, quad ((γ : Matrix OmI OmI K) *ᵥ v) = quad v) ∧
      l * m = Units.mk0 c hc0 ∧ A * γ = γ * diagGL (diagVals l m) := by
  obtain ⟨u, u', l, m, hquad, hAu, hAu', hlm⟩ :=
    adaptedQuad_of_eigen hA hc0 hQ he₀ hQe hf hQf hef
  have hl0 : l ≠ 0 := left_ne_zero_of_mul (hlm ▸ hc0)
  have hm0 : m ≠ 0 := right_ne_zero_of_mul (hlm ▸ hc0)
  obtain ⟨γ, hγ, hγ1, hγ2, hγ3, hγ4⟩ := exists_isometry_of_isHypQuad hquad
  refine ⟨γ, Units.mk0 l hl0, Units.mk0 m hm0, hγ, Units.ext (by simpa using hlm), ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have hd : ∀ j, ((diagGL (diagVals (Units.mk0 l hl0) (Units.mk0 m hm0)) : GL OmI K) :
      Matrix OmI OmI K) *ᵥ Pi.single j 1 =
      ((diagVals (Units.mk0 l hl0) (Units.mk0 m hm0) j : Kˣ) : K) • (Pi.single j 1 : OmI → K) := by
    intro j
    rw [diagGL_mulVec]
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hd j, Matrix.mulVec_smul]
  rcases j with j | j <;> fin_cases j
  · simp [diagVals, hγ1, he₀]
  · simp [diagVals, hγ2, hAu]
  · simp [diagVals, hγ3, hf, hlm]
  · simp [diagVals, hγ4, hAu']

theorem exists_isometry_diag (A : GL OmI K) (hA : A ^ (Fintype.card K - 1) = 1) {c : K}
    (hQ : ∀ v, quad ((A : Matrix OmI OmI K) *ᵥ v) = c * quad v) {e₀ : OmI → K} (he₀ : e₀ ≠ 0)
    (hQe : quad e₀ = 0)
    (hfix : ∀ v, (A : Matrix OmI OmI K) *ᵥ v = v ↔ ∃ t : K, v = t • e₀) :
    ∃ (γ : GL OmI K) (l m : Kˣ), (∀ v, quad ((γ : Matrix OmI OmI K) *ᵥ v) = quad v) ∧
      l * m ≠ 1 ∧ A * γ = γ * diagGL (diagVals l m) := by
  obtain ⟨hc0, hc1, f, hf, hef, hQf⟩ := exists_dual_eigenvector A hA hQ he₀ hfix
  have hfix₀ : (A : Matrix OmI OmI K) *ᵥ e₀ = e₀ := (hfix e₀).2 ⟨1, (one_smul K e₀).symm⟩
  obtain ⟨γ, l, m, hγ, hlm, hAγ⟩ := exists_adapted_basis A hA hc0 hc1 hQ hfix₀ hQe hf hQf hef
  refine ⟨γ, l, m, hγ, ?_, hAγ⟩
  rw [hlm]
  intro h
  exact hc1 (by simpa using congrArg Units.val h)

end OmegaEig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
