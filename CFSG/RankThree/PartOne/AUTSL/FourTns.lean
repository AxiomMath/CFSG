module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF1514B.Numbers
public import CFSG.RankThree.PartOne.KF1514B.Tns

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open Matrix CFSG.RankThree.PartOne.KF1514B

section TnsFacts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

@[expose] def sT (g : GL (Fin 2) K) : K := (g : Matrix (Fin 2) (Fin 2) K) 1 0

theorem nrm_eq_zero {z : K × K} (h : nrm b c z = 0) : z = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [nrm] at h
  by_cases h1 : z.2 = 0
  · rw [h1] at h
    have : z.1 ^ 2 = 0 := by linear_combination h
    have h0 : z.1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 this
    exact Prod.ext h0 h1
  · exfalso
    apply AnisoPair.hirr (b := b) (c := c) (z.1 / z.2)
    field_simp
    linear_combination h

theorem Mmat_apply00 (z : K × K) : Mmat b c z 0 0 = z.1 := rfl
theorem Mmat_apply01 (z : K × K) : Mmat b c z 0 1 = c * z.2 := rfl
theorem Mmat_apply10 (z : K × K) : Mmat b c z 1 0 = z.2 := rfl
theorem Mmat_apply11 (z : K × K) : Mmat b c z 1 1 = z.1 + b * z.2 := rfl

theorem sT_eq {g : GL (Fin 2) K} {z : K × K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Mmat b c z) : sT g = z.2 := by
  simp only [sT, hg, Mmat_apply10]

theorem eq_one_of_z {g : GL (Fin 2) K} {z : K × K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Mmat b c z) (hz : z = (1, 0)) : g = 1 := by
  refine Units.ext ?_
  rw [hg, hz, Mmat_one, Units.val_one]

theorem Tns_s_ne_zero {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg1 : g ≠ 1) : sT g ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨z, hz, hgz⟩ := hg
  intro h0
  rw [sT_eq hgz] at h0
  apply hg1
  apply eq_one_of_z hgz
  simp only [nrm, h0] at hz
  have h1 : (z.1 + 1) ^ 2 = 0 := by linear_combination hz + (z.1 + 1) * h2
  have : z.1 + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h1
  refine Prod.ext ?_ h0
  show z.1 = 1
  linear_combination this - h2

theorem Tns_eigen {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg1 : g ≠ 1) {l : K} {p : Fin 2 → K}
    (hp : (g : Matrix (Fin 2) (Fin 2) K).mulVec p = l • p) : p = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : sT g ≠ 0 := Tns_s_ne_zero hg hg1
  obtain ⟨z, hz, hgz⟩ := hg
  rw [sT_eq hgz] at hs
  have hw : nrm b c (z.1 + l, z.2) ≠ 0 := by
    intro h
    exact hs (congrArg Prod.snd (nrm_eq_zero h))
  rw [hgz] at hp
  have e0 := congrFun hp 0
  have e1 := congrFun hp 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Mmat_apply00, Mmat_apply01,
    Mmat_apply10, Mmat_apply11, Pi.smul_apply, smul_eq_mul] at e0 e1
  have hp0 : nrm b c (z.1 + l, z.2) * p 0 = 0 := by
    simp only [nrm]
    linear_combination (z.1 + l + b * z.2) * e0 + c * z.2 * e1 +
      (-z.1 * c * p 1 * z.2 + z.1 * l * p 0 - b * c * p 1 * z.2 ^ 2 + b * l * p 0 * z.2 +
        l ^ 2 * p 0) * h2
  have hp1 : nrm b c (z.1 + l, z.2) * p 1 = 0 := by
    simp only [nrm]
    linear_combination z.2 * e0 + (z.1 + l) * e1 +
      (z.1 * l * p 1 - z.1 * p 0 * z.2 + l ^ 2 * p 1) * h2
  funext i
  fin_cases i
  · exact (mul_eq_zero.1 hp0).resolve_left hw
  · exact (mul_eq_zero.1 hp1).resolve_left hw

theorem Tns_fix {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg1 : g ≠ 1) {p : Fin 2 → K}
    (hp : (g : Matrix (Fin 2) (Fin 2) K).mulVec p = p) : p = 0 :=
  Tns_eigen hg hg1 (l := 1) (by rw [hp, one_smul])

theorem Tns_sq_vec {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (v : Fin 2 → K) :
    (g : Matrix (Fin 2) (Fin 2) K).mulVec ((g : Matrix (Fin 2) (Fin 2) K).mulVec v) +
      (b * sT g) • (g : Matrix (Fin 2) (Fin 2) K).mulVec v + v = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨z, hz, hgz⟩ := hg
  rw [sT_eq hgz, hgz]
  simp only [nrm] at hz
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Mmat_apply00, Mmat_apply01,
      Mmat_apply10, Mmat_apply11, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fin.zero_eta, Fin.isValue]
    linear_combination v 0 * hz +
      (z.1 * c * v 1 * z.2 + b * c * v 1 * z.2 ^ 2 + v 0) * h2
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Mmat_apply00, Mmat_apply01,
      Mmat_apply10, Mmat_apply11, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fin.mk_one, Fin.isValue]
    linear_combination v 1 * hz +
      (z.1 * b * v 1 * z.2 + z.1 * v 0 * z.2 + b ^ 2 * v 1 * z.2 ^ 2 + b * v 0 * z.2 ^ 2 +
        v 1) * h2

theorem Tns_inv_val {g : GL (Fin 2) K} {z : K × K} (hz : nrm b c z = 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Mmat b c z) :
    ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Mmat b c (zconj b z) := by
  have h1 : (g : Matrix (Fin 2) (Fin 2) K) * Mmat b c (zconj b z) = 1 := by
    rw [hg, Mmat_mul, zmul_zconj, hz, Mmat_one]
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_right_inv h1

theorem Tns_s_eq {g g' : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg' : g' ∈ Tns b c)
    (h : sT g = sT g') : g' = g ∨ g' = g⁻¹ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨z, hz, hgz⟩ := hg
  obtain ⟨z', hz', hgz'⟩ := hg'
  rw [sT_eq hgz, sT_eq hgz'] at h
  simp only [nrm] at hz hz'
  have hprod : (z'.1 + z.1) * (z'.1 + z.1 + b * z.2) = 0 := by
    rw [← h] at hz'
    linear_combination hz' - hz + (z'.1 * z.1 + z.1 ^ 2 + b * z.1 * z.2) * h2
  rcases mul_eq_zero.1 hprod with h1 | h1
  · left
    refine Units.ext ?_
    have : z' = z := Prod.ext (by linear_combination h1 - z.1 * h2) h.symm
    rw [hgz, hgz', this]
  · right
    refine Units.ext ?_
    have : z' = zconj b z := Prod.ext
      (by show z'.1 = z.1 + b * z.2; linear_combination h1 - (z.1 + b * z.2) * h2)
      (by show z'.2 = z.2; exact h.symm)
    rw [Tns_inv_val (by simpa [nrm] using hz) hgz, hgz', this]

theorem eq_Mmat_of_commutes {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg1 : g ≠ 1)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A * (g : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * A) : A = Mmat b c (A 0 0, A 1 0) := by
  have hs : sT g ≠ 0 := Tns_s_ne_zero hg hg1
  obtain ⟨z, hz, hgz⟩ := hg
  rw [sT_eq hgz] at hs
  rw [hgz] at hA
  have e0 := congrFun (congrFun hA 0) 0
  have e1 := congrFun (congrFun hA 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Mmat_apply00, Mmat_apply01, Mmat_apply10,
    Mmat_apply11] at e0 e1
  have h01 : A 0 1 = c * A 1 0 := by
    apply mul_right_cancel₀ hs
    linear_combination e0
  have h11 : A 1 1 = A 0 0 + b * A 1 0 := by
    apply mul_right_cancel₀ hs
    linear_combination e1
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h01
  · rfl
  · exact h11

theorem comm_of_commutes {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg1 : g ≠ 1)
    {φ ψ : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (hφ : ∀ v, φ ((g : Matrix (Fin 2) (Fin 2) K).mulVec v) =
      (g : Matrix (Fin 2) (Fin 2) K).mulVec (φ v))
    (hψ : ∀ v, ψ ((g : Matrix (Fin 2) (Fin 2) K).mulVec v) =
      (g : Matrix (Fin 2) (Fin 2) K).mulVec (ψ v)) :
    ∀ v, φ (ψ v) = ψ (φ v) := by
  have hcomm : ∀ χ : (Fin 2 → K) →ₗ[K] (Fin 2 → K),
      (∀ v, χ ((g : Matrix (Fin 2) (Fin 2) K).mulVec v) =
        (g : Matrix (Fin 2) (Fin 2) K).mulVec (χ v)) →
      LinearMap.toMatrix' χ * (g : Matrix (Fin 2) (Fin 2) K) =
        (g : Matrix (Fin 2) (Fin 2) K) * LinearMap.toMatrix' χ := by
    intro χ hχ
    have h1 : χ.comp (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K)) =
        (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K)).comp χ :=
      LinearMap.ext fun v => by simpa using hχ v
    have h2 := congrArg LinearMap.toMatrix' h1
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h2
  have hA := eq_Mmat_of_commutes hg hg1 (hcomm φ hφ)
  have hB := eq_Mmat_of_commutes hg hg1 (hcomm ψ hψ)
  have hAB : LinearMap.toMatrix' φ * LinearMap.toMatrix' ψ =
      LinearMap.toMatrix' ψ * LinearMap.toMatrix' φ := by
    rw [hA, hB, Mmat_mul, Mmat_mul, zmul_comm]
  intro v
  have h3 : φ.comp ψ = ψ.comp φ := by
    apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
    exact hAB
  exact congrArg (fun f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => f v) h3

theorem invariant_of_Tns {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg1 : g ≠ 1)
    (M : Submodule K (Fin 2 → K))
    (hM : ∀ v ∈ M, (g : Matrix (Fin 2) (Fin 2) K).mulVec v ∈ M) : M = ⊥ ∨ M = ⊤ := by
  have hle : Module.finrank K M ≤ 2 := by
    have := Submodule.finrank_le M
    simpa using this
  have hcases : Module.finrank K M = 0 ∨ Module.finrank K M = 1 ∨ Module.finrank K M = 2 := by
    omega
  rcases hcases with h | h | h
  · left
    exact Submodule.finrank_eq_zero.1 h
  · exfalso
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h
    obtain ⟨l, hl⟩ := hv ⟨_, hM v.1 v.2⟩
    have : (g : Matrix (Fin 2) (Fin 2) K).mulVec (v : Fin 2 → K) = l • (v : Fin 2 → K) :=
      congrArg Subtype.val hl.symm
    exact hv0 (Subtype.ext (Tns_eigen hg hg1 this))
  · right
    exact Submodule.eq_top_of_finrank_eq (by simpa using h)

theorem Mmat_sub (z w : K × K) : Mmat b c z - Mmat b c w = Mmat b c (z - w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mmat] <;> ring

theorem Mmat_eq_one_of_pow {w : K × K} {m : ℕ} (h : (Mmat b c w) ^ (2 ^ m) = 1) :
    Mmat b c w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (Mmat b c w - 1) ^ (2 ^ m) = 0 := by
    rw [sub_pow_char_pow_of_commute 2 m (Commute.one_right _), h, one_pow, sub_self]
  have h2 : Mmat b c w - 1 = Mmat b c (w - (1, 0)) := by
    rw [← Mmat_one (b := b) (c := c), Mmat_sub]
  rw [h2] at h1
  have h3 : (Mmat b c (w - (1, 0))).det ^ (2 ^ m) = 0 := by
    rw [← Matrix.det_pow, h1, Matrix.det_zero]
  have h4 : (Mmat b c (w - (1, 0))).det = 0 := pow_eq_zero_iff (by positivity) |>.1 h3
  rw [det_Mmat] at h4
  have h5 := nrm_eq_zero h4
  have h6 : Mmat b c (w - (1, 0)) = 0 := by
    rw [h5]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mmat]
  rw [h6] at h2
  exact sub_eq_zero.1 h2

theorem toMatrix'_commute {g : GL (Fin 2) K} {φ : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (hφ : ∀ v, φ ((g : Matrix (Fin 2) (Fin 2) K).mulVec v) =
      (g : Matrix (Fin 2) (Fin 2) K).mulVec (φ v)) :
    LinearMap.toMatrix' φ * (g : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * LinearMap.toMatrix' φ := by
  have h1 : φ.comp (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K)) =
      (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K)).comp φ :=
    LinearMap.ext fun v => by simpa using hφ v
  have h2 := congrArg LinearMap.toMatrix' h1
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h2

end TnsFacts

end CFSG.RankThree.PartOne.AUTSL.Four
