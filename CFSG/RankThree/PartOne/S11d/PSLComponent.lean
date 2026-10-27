module

public import CFSG.RankThree.PartOne.S11d.PSLBlocks

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Polynomial Matrix
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem mul_comm_of_commutator_scalar {n p : ℕ} [NeZero n] {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card Kˣ) {A S : SpecialLinearGroup (Fin n) K} {c : Kˣ}
    (hAp : (SpecialLinearGroup.toGL A) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hcomm : ⁅A, S⁆ ∈ scalars n K) : A * S = S * A := by
  obtain ⟨ν, -, hmat⟩ := mem_scalars.mp hcomm
  set a : GL (Fin n) K := SpecialLinearGroup.toGL A with ha
  set s : GL (Fin n) K := SpecialLinearGroup.toGL S with hs
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ν with hz
  set w : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) c with hw
  have hcomm0 : a * s * a⁻¹ * s⁻¹ = z := by
    have h1 : SpecialLinearGroup.toGL ⁅A, S⁆ = a * s * a⁻¹ * s⁻¹ := by
      rw [map_commutatorElement, commutatorElement_def]
    rw [← h1]
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar]
    exact hmat
  have hzc : z ∈ Subgroup.center (GL (Fin n) K) :=
    Subgroup.mem_center_iff.mpr fun g => (GeneralLinearGroup.scalar_commute ν g).symm
  have hwc : w ∈ Subgroup.center (GL (Fin n) K) :=
    Subgroup.mem_center_iff.mpr fun g => (GeneralLinearGroup.scalar_commute c g).symm
  have hcz : ∀ k : ℕ, ∀ g : GL (Fin n) K, g * z ^ k = z ^ k * g := fun k g =>
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hzc k) g
  have hconj : ∀ k : ℕ, a ^ k * s * (a ^ k)⁻¹ = z ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a ^ (k + 1) * s * (a ^ (k + 1)) ⁻¹ = a * (a ^ k * s * (a ^ k)⁻¹) * a⁻¹ := by
            rw [pow_succ', _root_.mul_inv_rev]; group
        _ = a * (z ^ k * s) * a⁻¹ := by rw [ih]
        _ = z ^ k * (a * s * a⁻¹) := by
            rw [← mul_assoc, ← mul_assoc, hcz k a]
            group
        _ = z ^ k * (z * s) := by
            rw [show a * s * a⁻¹ = z * s by
              calc a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s := by group
                _ = z * s := by rw [hcomm0]]
        _ = z ^ (k + 1) * s := by rw [pow_succ, mul_assoc]
  have h1 : s = z ^ p * s := by
    have := hconj p
    rw [hAp] at this
    have h2 : w * s * w⁻¹ = s := by
      rw [← Subgroup.mem_center_iff.mp hwc s]
      group
    rwa [h2] at this
  have h3 : z ^ p = 1 := by
    have : z ^ p * s = 1 * s := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel this
  have h4 : ν ^ p = 1 := by
    have h5 : GeneralLinearGroup.scalar (Fin n) (ν ^ p) = 1 := by rw [map_pow]; exact h3
    have h6 : ((GeneralLinearGroup.scalar (Fin n) (ν ^ p) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [h5]
    rw [GeneralLinearGroup.coe_scalar, Units.val_one,
      ← map_one (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K)] at h6
    have h7 := Matrix.scalar_inj.mp h6
    exact Units.ext (by rwa [Units.val_pow_eq_pow_val] at h7)
  have h8 : ν = 1 := unit_eq_one_of_pow_eq_one hp hpK h4
  have h9 : a * s * a⁻¹ * s⁻¹ = 1 := by rw [hcomm0, hz, h8, map_one]
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul]
  calc a * s = (a * s * a⁻¹ * s⁻¹) * (s * a) := by group
    _ = s * a := by rw [h9, one_mul]

theorem eq_one_of_pow_two_pow_eq_one {F : Type*} [Field F] [CharP F 2] {u : Fˣ} {k : ℕ}
    (h : u ^ 2 ^ k = 1) : u = 1 := by
  have h1 : ((u : F) - 1) ^ 2 ^ k = 0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [sub_pow_char_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, one_pow, sub_self]
  have := pow_eq_zero_iff (pow_ne_zero k two_ne_zero) |>.mp h1
  exact Units.ext (sub_eq_zero.mp this)

theorem eq_one_of_two_pow_of_lt_two {F : Type*} [Field F] [CharP F 2] {m : ℕ} (hm : m < 2)
    {u : GL (Fin m) F} {k : ℕ} (h : u ^ 2 ^ k = 1) : u = 1 := by
  interval_cases m
  · exact Units.ext (Subsingleton.elim _ _)
  · have h1 : GeneralLinearGroup.det u ^ 2 ^ k = 1 := by rw [← map_pow, h, map_one]
    have h2 := eq_one_of_pow_two_pow_eq_one h1
    have h3 : (u : Matrix (Fin 1) (Fin 1) F) = 1 := by
      have := congrArg (fun v : Fˣ => (v : F)) h2
      simp [GeneralLinearGroup.det, Matrix.det_unique] at this
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      simpa using this
    exact Units.ext h3

open scoped _root_.Classical in
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem mem_blockImage_of_two_power {n p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card Kˣ) {γ : Kˣ} (hγ : γ ^ p = c)
    (hrank : CFSG.pRank p (projectiveSL n K) ≤ 1)
    {hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))}
    (b₀ : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))
    (hb₀ : (b₀ : K[X]) = X - C (γ : K)) {g : GL (Fin n) K}
    (hg : g ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K))) {k : ℕ}
    (hgk : g ^ 2 ^ k = 1) : g ∈ blockImage hsq b₀ := by
  rw [← range_commutantUnitsToGL_eq_centralizer
    (x := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) a rfl, ← range_blockTheta hsq] at hg
  obtain ⟨w, rfl⟩ := hg
  have hw : w ^ 2 ^ k = 1 := by
    apply blockTheta_injective hsq
    rw [map_pow, hgk, map_one]
  have hwb : ∀ b : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)),
      (w b) ^ 2 ^ k = 1 := fun b => by
    have := congrFun hw b
    simpa [Pi.pow_apply] using this
  have hother : ∀ b : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)), b ≠ b₀ →
      w b = 1 := by
    intro b hb
    have hm : mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b < 2 := by
      by_contra hm2
      push Not at hm2
      apply hb
      apply Subtype.ext
      rw [hb₀]
      exact eq_X_sub_C_of_mult_ge_two hap hp hp2 hpK hγ hrank b hm2
    have : CharP (Efac (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b) 2 :=
      charP_of_injective_algebraMap (algebraMap K _).injective 2
    exact eq_one_of_two_pow_of_lt_two hm (hwb b)
  have hdet : GeneralLinearGroup.det (w b₀) = 1 := by
    have h1 : GeneralLinearGroup.det (w b₀) ^ 2 ^ k = 1 := by
      rw [← map_pow, hwb b₀, map_one]
    have : CharP (Efac (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b₀) 2 :=
      charP_of_injective_algebraMap (algebraMap K _).injective 2
    exact eq_one_of_pow_two_pow_eq_one h1
  obtain ⟨s, hs⟩ : w b₀ ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b₀))
        (Efac (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b₀) →* _).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact hdet
  rw [mem_blockImage]
  refine ⟨s, ?_⟩
  congr 1
  funext b
  by_cases hb : b = b₀
  · subst hb
    rw [blockEmbed_apply_self, hs]
  · rw [blockEmbed_apply_of_ne hb, hother b hb]

open scoped _root_.Classical in
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem exists_block_data {n p : ℕ} [NeZero n] {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card Kˣ)
    (hrank : CFSG.pRank p (projectiveSL n K) ≤ 1)
    {A : SpecialLinearGroup (Fin n) K} {c : Kˣ}
    (hAp : (SpecialLinearGroup.toGL A) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    {y : projectiveSL n K} (hxp : (proj n K A) ^ p = 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : proj n K A * y = y * proj n K A) :
    ∃ (hsq : Squarefree (minpoly K (Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)))) (γ : Kˣ)
      (b₀ : primaryFactors (Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))),
      γ ^ p = c ∧ (b₀ : K[X]) = X - C (γ : K) ∧
      2 ≤ mult (Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) b₀ ∧
      ∀ g ∈ Subgroup.centralizer ({SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)), ∀ k : ℕ,
        g ^ 2 ^ k = 1 → g ∈ blockImage hsq b₀ := by
  have hpK' : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hsq := squarefree_minpoly_toLin'_of_pow_scalar hpK' hAp
  obtain ⟨γ, hγ⟩ := (exists_unique_pth_root hp hpK c).exists
  obtain ⟨b, hb⟩ := exists_mult_two_PSL hp hp2 hxp hy2 hy1 hxy
  have hbeq := eq_X_sub_C_of_mult_ge_two hAp hp hp2 hpK hγ hrank b hb
  exact ⟨hsq, γ, b, hγ, hbeq, hb, fun g hg k hgk =>
    mem_blockImage_of_two_power (hsq := hsq) hAp hp hp2 hpK hγ hrank b hbeq hg hgk⟩

end CFSG.RankThree.PartOne
