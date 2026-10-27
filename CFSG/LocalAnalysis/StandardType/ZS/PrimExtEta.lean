module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix

public section

namespace CFSG.StandardType.ZS

@[expose] def EtaOK {p : ℕ} (d : ℕ) (s t : ZMod p) : Prop :=
  (s = 0 ∧ t = 0) ∨ (3 ≤ d ∧ s * t = 1) ∨ (4 ≤ d ∧ s * t = 2) ∨
    (5 ≤ d ∧ (s * t) ^ 2 - 3 * (s * t) + 1 = 0)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
private lemma not_dvd_of_lt {p n : ℕ} (hn0 : 0 < n) (hn : n < p) : ¬ p ∣ n := by
  intro h
  have hle : p ≤ n := Nat.le_of_dvd hn0 h
  omega


theorem apply_mul_apply_sq_sub_of_orderOf_eq_five (hp : p ≠ 2) (hp5 : p ≠ 5) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : orderOf (Module.reflection hφ * Module.reflection hψ) = 5) :
    (φ b * ψ a) ^ 2 - 3 * (φ b * ψ a) + 1 = 0 := by
  have h5 : (Module.reflection hφ * Module.reflection hψ) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (Module.reflection hφ * Module.reflection hψ)
    rwa [h] at this
  have hneq : Module.reflection hφ * Module.reflection hψ ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at h; norm_num at h
  have : NeZero (2 : ZMod p) := ⟨ZMod.prime_ne_zero p 2 hp⟩
  rcases linearIndependent_and_or_exists_transvection (K := ZMod p) hφ hψ with
    ⟨hxy, hfg⟩ | ⟨w, χ, hχw, hN⟩
  · have hcrit := (reflection_mul_reflection_pow_eq_one_iff hφ hψ hxy hfg 5).mp h5
    have hAB : ggCoxA (ZMod p) 5 (φ b * ψ a - 2) + ggCoxB (ZMod p) 5 (φ b * ψ a - 2)
        = ((φ b * ψ a - 2) ^ 2 + (φ b * ψ a - 2) - 1) ^ 2 := by
      simp only [ggCoxA, ggCoxB]
      norm_num
      rw [Polynomial.Chebyshev.S_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      ring
    have hsq : ((φ b * ψ a - 2) ^ 2 + (φ b * ψ a - 2) - 1) ^ 2 = 0 := by
      rw [← hAB]; exact hcrit.1
    have hlin : (φ b * ψ a - 2) ^ 2 + (φ b * ψ a - 2) - 1 = 0 := by
      rw [pow_two] at hsq
      exact mul_self_eq_zero.mp hsq
    linear_combination hlin
  · exfalso
    have h5zero : (5 : ZMod p) = 0 := natCast_eq_zero_of_unipotent hχw hN hneq h5
    have hdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h5zero
    have hpprime : p.Prime := Fact.out
    have hpge : 2 ≤ p := hpprime.two_le
    have hple : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · exact hp rfl
    · norm_num at hdvd
    · norm_num at hpprime
    · exact hp5 rfl

theorem etaOK_of_orderOf_le {d : ℕ} (hd : d ≤ 5) (hdp : d < p) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hne : Module.reflection hφ ≠ Module.reflection hψ)
    (hpos : 0 < orderOf (Module.reflection hφ * Module.reflection hψ))
    (hle : orderOf (Module.reflection hφ * Module.reflection hψ) ≤ d) :
    EtaOK d (φ b) (ψ a) := by
  have hle5 : orderOf (Module.reflection hφ * Module.reflection hψ) ≤ 5 := le_trans hle hd
  interval_cases h : orderOf (Module.reflection hφ * Module.reflection hψ)
  · exfalso
    have hr1 : Module.reflection hφ * Module.reflection hψ = 1 := orderOf_eq_one_iff.mp h
    have hrefl : Module.reflection hφ = Module.reflection hψ := by
      calc Module.reflection hφ
          = Module.reflection hφ * (Module.reflection hψ * Module.reflection hψ) := by
            rw [show Module.reflection hψ * Module.reflection hψ = 1 from by
              rw [← Module.reflection_inv]; exact mul_inv_cancel _, mul_one]
        _ = (Module.reflection hφ * Module.reflection hψ) * Module.reflection hψ := by
            rw [mul_assoc]
        _ = 1 * Module.reflection hψ := by rw [hr1]
        _ = Module.reflection hψ := one_mul _
    exact hne hrefl
  · have hp2 : p ≠ 2 := by omega
    exact Or.inl (apply_eq_zero_of_orderOf_eq_two hp2 hφ hψ h)
  · have hp2 : p ≠ 2 := by omega
    exact Or.inr (Or.inl ⟨by omega, apply_mul_apply_eq_one_of_orderOf_eq_three hp2 hφ hψ h⟩)
  · have hp2 : p ≠ 2 := by omega
    exact Or.inr (Or.inr (Or.inl
      ⟨by omega, apply_mul_apply_eq_two_of_orderOf_eq_four hp2 hφ hψ h⟩))
  · have hp2 : p ≠ 2 := by omega
    have hp5 : p ≠ 5 := by omega
    exact Or.inr (Or.inr (Or.inr
      ⟨by omega, apply_mul_apply_sq_sub_of_orderOf_eq_five hp2 hp5 hφ hψ h⟩))

theorem etaOK_of_dMax [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
    (hG : DMax p G d) (hd : d ≤ 5) (hdp : d < p) (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) (ha : Module.reflection hφ ∈ G)
    (hb : Module.reflection hψ ∈ G) (hne : Module.reflection hφ ≠ Module.reflection hψ) :
    EtaOK d (φ b) (ψ a) := by
  have : Finite U := by
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ZMod p) (M := U)
    have hsurj : Function.Surjective (Fintype.linearCombination (ZMod p) s) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
    exact Finite.of_surjective _ hsurj
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun f : U ≃ₗ[ZMod p] U => (f : U → U))
      (fun f g h => LinearEquiv.ext fun x => congrFun h x)
  have h1 : 0 < orderOf (Module.reflection hφ * Module.reflection hψ) := orderOf_pos _
  have hle : orderOf (Module.reflection hφ * Module.reflection hψ) ≤ d :=
    hG.1 (Module.reflection hφ) ha (Module.reflection hψ) hb
      ((isRefl_iff hp (Module.reflection hφ)).mpr ⟨a, φ, hφ, rfl⟩)
      ((isRefl_iff hp (Module.reflection hψ)).mpr ⟨b, ψ, hψ, rfl⟩)
  exact etaOK_of_orderOf_le hd hdp hφ hψ hne h1 hle

theorem toMatrix_reflection {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ι : Type}
    [Fintype ι] [DecidableEq ι] (f : Module.Basis ι R V) {w : V} {ψ : Module.Dual R V}
    (hψ : ψ w = 2) :
    LinearMap.toMatrix f f (Module.reflection hψ : V →ₗ[R] V) =
      1 - Matrix.vecMulVec (fun i => f.repr w i) (fun i => ψ (f i)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change f.repr (f j - ψ (f j) • w) i =
    (1 - Matrix.vecMulVec (fun i => f.repr w i) (fun i => ψ (f i))) i j
  simp only [map_sub, map_smul, smul_eq_mul, Finsupp.sub_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (fun hji => h hji.symm)]
    ring

private lemma repr_sum_smul {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (ρ : Fin m → ZMod p) (i : Fin m) : f.repr (∑ j, ρ j • f j) i = ρ i := by
  have h1 : f.repr (∑ j, ρ j • f j) = ∑ j, Finsupp.single j (ρ j) := by
    simp [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single]
  rw [h1, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    rw [if_neg hij]
  · intro hi; simp at hi

private lemma sum_smul_coord_apply {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (κ : Fin m → ZMod p) (i : Fin m) : (∑ j, κ j • f.coord j) (f i) = κ i := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    rw [if_neg (fun h : i = j => hij h.symm), mul_zero]
  · intro hi; simp at hi

private lemma dual_apply_sum_smul {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (ψ : Module.Dual (ZMod p) U) (ρ : Fin m → ZMod p) :
    ψ (∑ i, ρ i • f i) = ∑ i, ψ (f i) * ρ i := by
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dual_sum_smul_apply {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (v : U) (κ : Fin m → ZMod p) :
    (∑ i, κ i • f.coord i) v = ∑ i, κ i * f.repr v i := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply]

theorem etaOK_of_toMatrix [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
    (hG : DMax p G d) (hd : d ≤ 5) (hdp : d < p) (hp : p ≠ 2) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {c r : U ≃ₗ[ZMod p] U} (hc : c ∈ G) (hr : r ∈ G)
    (hne : c ≠ r) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hcw : c = Module.reflection hψ) {ρ κ : Fin m → ZMod p}
    (hrk : LinearMap.toMatrix f f (r : U →ₗ[ZMod p] U) = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) :
    EtaOK d (∑ i, ψ (f i) * ρ i) (∑ i, κ i * f.repr w i) := by
  let a : U := ∑ i, ρ i • f i
  let φ : Module.Dual (ZMod p) U := ∑ i, κ i • f.coord i
  have hfa : ∀ i, f.repr a i = ρ i := fun i => repr_sum_smul f ρ i
  have hφf : ∀ i, φ (f i) = κ i := fun i => sum_smul_coord_apply f κ i
  have hφa : φ a = 2 := by
    have h1 : φ a = ∑ i, κ i * f.repr a i := dual_sum_smul_apply f a κ
    rw [h1, show (∑ i, κ i * f.repr a i) = ∑ i, κ i * ρ i from
      Finset.sum_congr rfl (fun i _ => by rw [hfa i])]
    exact hκρ
  have hr_eq : r = Module.reflection hφa := by
    have hlin : (r : U →ₗ[ZMod p] U) = (Module.reflection hφa : U →ₗ[ZMod p] U) := by
      apply (LinearMap.toMatrix f f).injective
      rw [hrk, toMatrix_reflection f hφa]
      congr 1
      ext i j
      simp only [Matrix.vecMulVec_apply]
      rw [hfa i, hφf j]
    exact LinearEquiv.ext (fun v => congrFun (congrArg (fun f : U →ₗ[ZMod p] U => (f : U → U))
      hlin) v)
  have hres : EtaOK d (ψ a) (φ w) :=
    etaOK_of_dMax (G := G) (d := d) hG hd hdp hp (a := w) (b := a) (φ := ψ) (ψ := φ)
      hψ hφa (by rw [← hcw]; exact hc) (by rw [← hr_eq]; exact hr)
      (by rw [hcw, hr_eq] at hne; exact hne)
  have hψa : ψ a = ∑ i, ψ (f i) * ρ i := dual_apply_sum_smul f ψ ρ
  have hφw : φ w = ∑ i, κ i * f.repr w i := dual_sum_smul_apply f w κ
  rw [hψa, hφw] at hres
  exact hres

theorem etaOK_five_iff {α s t : ZMod p} (hα : α ^ 2 = α + 1) :
    EtaOK 5 s t ↔ (s = 0 ∧ t = 0) ∨ s * t = 1 ∨ s * t = 2 ∨ s * t = 1 + α ∨ s * t = 2 - α := by
  have hfac : ∀ x : ZMod p, (x - (1 + α)) * (x - (2 - α)) = x ^ 2 - 3 * x + 1 := by
    intro x
    ring_nf
    linear_combination -hα
  unfold EtaOK
  constructor
  · rintro (⟨hs, ht⟩ | ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨-, h5⟩)
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · right; right; right
      have h0 : (s * t - (1 + α)) * (s * t - (2 - α)) = 0 := by rw [hfac]; exact h5
      rcases mul_eq_zero.mp h0 with h | h
      · left; linear_combination h
      · right; linear_combination h
  · rintro (⟨hs, ht⟩ | h1 | h2 | h3 | h4)
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr (Or.inl ⟨by norm_num, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by norm_num, h2⟩))
    · right; right; right
      refine ⟨by norm_num, ?_⟩
      rw [← hfac (s * t), h3]; ring
    · right; right; right
      refine ⟨by norm_num, ?_⟩
      rw [← hfac (s * t), h4]; ring

theorem seven_lt_of_sq_eq_add_one (hp5 : p ≠ 5) {α : ZMod p} (hα : α ^ 2 = α + 1) : 7 < p := by
  by_contra h
  have hp7 : p ≤ 7 := by omega
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsq : (2 * α - 1) ^ 2 = 5 := by linear_combination 4 * hα
  interval_cases p
  · exact (by decide +revert : ∀ x : ZMod 2, x ^ 2 ≠ x + 1) α hα
  · exact (by decide +revert : ∀ x : ZMod 3, x ^ 2 ≠ 5) (2 * α - 1) hsq
  · exact absurd (Fact.out : (4 : ℕ).Prime) (by norm_num)
  · exact hp5 rfl
  · exact absurd (Fact.out : (6 : ℕ).Prime) (by norm_num)
  · exact (by decide +revert : ∀ x : ZMod 7, x ^ 2 ≠ 5) (2 * α - 1) hsq

theorem seven_lt_of_two_mul_sq_add (hp : p ≠ 2) (hp7 : p ≠ 7) {β : ZMod p}
    (hβ : 2 * β ^ 2 + β + 1 = 0) : 7 < p := by
  by_contra h
  have hp7' : p ≤ 7 := by omega
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  interval_cases p
  · exact hp rfl
  · exact (by decide +revert : ∀ x : ZMod 3, 2 * x ^ 2 + x + 1 ≠ 0) β hβ
  · exact absurd (Fact.out : (4 : ℕ).Prime) (by norm_num)
  · exact (by decide +revert : ∀ x : ZMod 5, 2 * x ^ 2 + x + 1 ≠ 0) β hβ
  · exact absurd (Fact.out : (6 : ℕ).Prime) (by norm_num)
  · exact hp7 rfl

theorem not_etaOK_five_of_mul_eq_quarter (hp7 : 7 < p) {s t : ZMod p} (h : s * t = 1 / 4) :
    ¬ EtaOK 5 s t := by
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hzero
    exact not_dvd_of_lt (by norm_num) (by omega)
      ((CharP.cast_eq_zero_iff (ZMod p) p 4).mp hzero)
  have h4 : (4 : ZMod p) * (s * t) = 1 := by
    rw [h, div_eq_mul_inv, one_mul, mul_inv_cancel₀ h4ne]
  intro hE
  rcases hE with ⟨hs, ht⟩ | ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨-, h5⟩
  · rw [hs, ht, mul_zero, mul_zero] at h4
    norm_num at h4
  · have h3 : (3 : ZMod p) = 0 := by rw [h1, mul_one] at h4; linear_combination h4
    exact not_dvd_of_lt (by norm_num) (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3)
  · have h7 : (7 : ZMod p) = 0 := by rw [h2] at h4; linear_combination h4
    exact not_dvd_of_lt (by norm_num) (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p 7).mp h7)
  · have h41 : (4 : ZMod p) * (s * t) - 1 = 0 := sub_eq_zero.mpr h4
    have h5z : (5 : ZMod p) = 0 := by
      linear_combination 16 * h5 - (4 * (s * t) - 11) * h41
    exact not_dvd_of_lt (by norm_num) (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p 5).mp h5z)

theorem not_etaOK_four_of_mul_eq_half (hp3 : 3 < p) {s t : ZMod p} (h : s * t = 1 / 2) :
    ¬ EtaOK 4 s t := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    exact not_dvd_of_lt (by norm_num) (by omega)
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero)
  have h2 : (2 : ZMod p) * (s * t) = 1 := by
    rw [h, div_eq_mul_inv, one_mul, mul_inv_cancel₀ h2ne]
  intro hE
  rcases hE with ⟨hs, ht⟩ | ⟨-, h1⟩ | ⟨-, h2'⟩ | ⟨h54, -⟩
  · rw [hs, ht, mul_zero, mul_zero] at h2
    norm_num at h2
  · have h1z : (1 : ZMod p) = 0 := by rw [h1, mul_one] at h2; linear_combination h2
    exact one_ne_zero h1z
  · have h3 : (3 : ZMod p) = 0 := by rw [h2'] at h2; linear_combination h2
    exact not_dvd_of_lt (by norm_num) (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3)
  · omega

theorem not_etaOK_four_of_mul_eq_three_halves (hp3 : 3 < p) {s t : ZMod p}
    (h : s * t = 3 / 2) : ¬ EtaOK 4 s t := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    exact not_dvd_of_lt (by norm_num) (by omega)
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero)
  have h2 : (2 : ZMod p) * (s * t) = 3 := by
    rw [h]; field_simp
  intro hE
  rcases hE with ⟨hs, ht⟩ | ⟨-, h1⟩ | ⟨-, h2'⟩ | ⟨h54, -⟩
  · rw [hs, ht, mul_zero, mul_zero] at h2
    have h3 : (3 : ZMod p) = 0 := h2.symm
    exact not_dvd_of_lt (by norm_num) (by omega)
      ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3)
  · have h1z : (1 : ZMod p) = 0 := by
      rw [h1, mul_one] at h2
      have h01 : (0 : ZMod p) = 1 := by
        calc (0 : ZMod p) = 2 - 2 := by ring
          _ = 3 - 2 := by rw [h2]
          _ = 1 := by ring
      exact h01.symm
    exact one_ne_zero h1z
  · have h1z : (1 : ZMod p) = 0 := by
      rw [h2'] at h2
      have h0neg : (0 : ZMod p) = -1 := by
        calc (0 : ZMod p) = 2 * 2 - 2 * 2 := by ring
          _ = 3 - 2 * 2 := by rw [h2]
          _ = -1 := by ring_nf; rfl
      exact neg_eq_zero.mp h0neg.symm
    exact one_ne_zero h1z
  · omega

end CFSG.StandardType.ZS

end
