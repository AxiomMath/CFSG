module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix

section Eig

variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mulVec_cube_of_pow_three {A : Matrix ι ι k} (hA : A ^ 3 = 1) (u : ι → k) :
    A *ᵥ (A *ᵥ (A *ᵥ u)) = u := by
  have h := congrArg (fun B : Matrix ι ι k => B *ᵥ u) hA
  simpa [pow_succ, Matrix.mulVec_mulVec, Matrix.mul_assoc] using h

theorem exists_eigen_aux {ω : k} (hω : ω ^ 2 + ω + 1 = 0) {A : Matrix ι ι k} (hA : A ^ 3 = 1)
    (u : ι → k) (hu : u ≠ 0) :
    ∃ (c : k) (v : ι → k), (c = 1 ∨ c = ω ∨ c = ω ^ 2) ∧ v ≠ 0 ∧ A *ᵥ v = c • v ∧
      ∀ S : Submodule k (ι → k), u ∈ S → (∀ x ∈ S, A *ᵥ x ∈ S) → v ∈ S := by
  have h3 := mulVec_cube_of_pow_three hA u
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  obtain ⟨u1, hu1⟩ : ∃ u1, u1 = A *ᵥ u - u := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2, u2 = A *ᵥ u1 - ω • u1 := ⟨_, rfl⟩
  have hu3 : A *ᵥ u2 - ω ^ 2 • u2 = 0 := by
    rw [hu2, hu1]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [h3]
    match_scalars
    all_goals first
      | ring1
      | linear_combination (-1 : k) * hω3
      | linear_combination (-1 : k) * hω
      | linear_combination hω + hω3
  by_cases h1 : u1 = 0
  · refine ⟨1, u, Or.inl rfl, hu, ?_, fun S hS _ => hS⟩
    rw [one_smul]
    exact sub_eq_zero.mp (hu1 ▸ h1)
  · by_cases h2 : u2 = 0
    · refine ⟨ω, u1, Or.inr (Or.inl rfl), h1, ?_, fun S hS hSA => ?_⟩
      · exact sub_eq_zero.mp (hu2 ▸ h2)
      · rw [hu1]
        exact S.sub_mem (hSA u hS) hS
    · refine ⟨ω ^ 2, u2, Or.inr (Or.inr rfl), h2, sub_eq_zero.mp hu3, fun S hS hSA => ?_⟩
      have hS1 : u1 ∈ S := by
        rw [hu1]
        exact S.sub_mem (hSA u hS) hS
      rw [hu2]
      exact S.sub_mem (hSA u1 hS1) (S.smul_mem ω hS1)

theorem exists_joint_eigenvector {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {M N : Matrix ι ι k} (hM : M ^ 3 = 1) (hN : N ^ 3 = 1) (hMN : M * N = N * M)
    (hM1 : M ≠ 1) :
    ∃ (v : ι → k) (l m : k), v ≠ 0 ∧ M *ᵥ v = l • v ∧ N *ᵥ v = m • v ∧ l ^ 3 = 1 ∧
      m ^ 3 = 1 ∧ l ≠ 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h
    have h' : (ω - 1) * (ω + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact hω1 (sub_eq_zero.mp h'')
    · have : ω = -1 := eq_neg_of_add_eq_zero_left h''
      rw [this] at hω
      norm_num at hω
  obtain ⟨x, hx⟩ : ∃ x : ι → k, (M - 1) *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hM1
    have : M - 1 = 0 := Matrix.toLin'.injective (LinearMap.ext fun x => by
      rw [Matrix.toLin'_apply, hcon x]; simp)
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ : ∃ y, y = M *ᵥ x - x := ⟨_, rfl⟩
  have hy0 : y ≠ 0 := by
    rw [hy]
    intro h
    apply hx
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact h
  have h3x := mulVec_cube_of_pow_three hM x
  obtain ⟨z, hz⟩ : ∃ z, z = M *ᵥ y - ω ^ 2 • y := ⟨_, rfl⟩
  have hzz : M *ᵥ z - ω • z = 0 := by
    rw [hz, hy]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [h3x]
    match_scalars
    all_goals first
      | ring1
      | linear_combination (-1 : k) * hω3
      | linear_combination (-1 : k) * hω
      | linear_combination hω + hω3
  obtain ⟨v₀, l, hv₀, hMv₀, hl3, hl1⟩ : ∃ (v₀ : ι → k) (l : k), v₀ ≠ 0 ∧ M *ᵥ v₀ = l • v₀ ∧
      l ^ 3 = 1 ∧ l ≠ 1 := by
    by_cases hz0 : z = 0
    · refine ⟨y, ω ^ 2, hy0, ?_, ?_, hω21⟩
      · rw [hz] at hz0
        exact sub_eq_zero.mp hz0
      · calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
          _ = 1 := by rw [hω3, one_pow]
    · exact ⟨z, ω, hz0, sub_eq_zero.mp hzz, hω3, hω1⟩
  let E : Submodule k (ι → k) := LinearMap.ker (Matrix.mulVecLin M - l • LinearMap.id)
  have hE : ∀ w, w ∈ E ↔ M *ᵥ w = l • w := by
    intro w
    simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hv₀E : v₀ ∈ E := (hE v₀).mpr hMv₀
  have hNE : ∀ w ∈ E, N *ᵥ w ∈ E := by
    intro w hw
    rw [hE] at hw ⊢
    calc M *ᵥ (N *ᵥ w) = (M * N) *ᵥ w := Matrix.mulVec_mulVec _ _ _
      _ = (N * M) *ᵥ w := by rw [hMN]
      _ = N *ᵥ (M *ᵥ w) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = N *ᵥ (l • w) := by rw [hw]
      _ = l • N *ᵥ w := by rw [Matrix.mulVec_smul]
  obtain ⟨m, v, hm, hv0, hNv, hvS⟩ := exists_eigen_aux hω hN v₀ hv₀
  have hvE := hvS E hv₀E hNE
  refine ⟨v, l, m, hv0, (hE v).mp hvE, hNv, hl3, ?_, hl1⟩
  rcases hm with rfl | rfl | rfl
  · simp
  · exact hω3
  · calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]

theorem exists_joint_eigenvector_fixed {F : Type} [Field F] {σ : F ≃+* F} {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hσω : σ ω = ω) {M N : Matrix ι ι F}
    (hM : M ^ 3 = 1) (hN : N ^ 3 = 1) (hMN : M * N = N * M) (hM1 : M ≠ 1)
    (hMσ : M.map σ = M) (hNσ : N.map σ = N) :
    ∃ (v : ι → F) (l m : F), v ≠ 0 ∧ (∀ i, σ (v i) = v i) ∧ M *ᵥ v = l • v ∧ N *ᵥ v = m • v ∧
      l ^ 3 = 1 ∧ m ^ 3 = 1 ∧ l ≠ 1 := by
  let k : Subfield F := RingHom.eqLocusField σ.toRingHom (RingHom.id F)
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => Iff.rfl
  have hMk : ∀ i j, M i j ∈ k := fun i j => (hk _).mpr (by
    have := congrFun (congrFun hMσ i) j
    simpa using this)
  have hNk : ∀ i j, N i j ∈ k := fun i j => (hk _).mpr (by
    have := congrFun (congrFun hNσ i) j
    simpa using this)
  let M' : Matrix ι ι k := fun i j => ⟨M i j, hMk i j⟩
  let N' : Matrix ι ι k := fun i j => ⟨N i j, hNk i j⟩
  have hM'map : M'.map k.subtype = M := by ext i j; rfl
  have hN'map : N'.map k.subtype = N := by ext i j; rfl
  let ωk : k := ⟨ω, (hk ω).mpr hσω⟩
  have hωk : ωk ^ 2 + ωk + 1 = 0 := Subtype.ext (by simpa [ωk] using hω)
  have hωk1 : ωk ≠ 1 := fun h => hω1 (by simpa [ωk] using congrArg Subtype.val h)
  have hinj : Function.Injective (fun A : Matrix ι ι k => A.map k.subtype) := by
    intro A B h
    exact Matrix.ext fun i j => k.subtype_injective (congrFun (congrFun h i) j)
  have hmapmul : ∀ A B : Matrix ι ι k, (A * B).map k.subtype = A.map k.subtype * B.map k.subtype :=
    fun A B => Matrix.map_mul (f := k.subtype)
  have hM'3 : M' ^ 3 = 1 := by
    apply hinj
    show (M' ^ 3).map k.subtype = (1 : Matrix ι ι k).map k.subtype
    have h := map_pow (k.subtype.mapMatrix : Matrix ι ι k →+* Matrix ι ι F) M' 3
    simp only [RingHom.mapMatrix_apply, hM'map] at h
    rw [h, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN'3 : N' ^ 3 = 1 := by
    apply hinj
    show (N' ^ 3).map k.subtype = (1 : Matrix ι ι k).map k.subtype
    have h := map_pow (k.subtype.mapMatrix : Matrix ι ι k →+* Matrix ι ι F) N' 3
    simp only [RingHom.mapMatrix_apply, hN'map] at h
    rw [h, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hM'N' : M' * N' = N' * M' := by
    apply hinj
    show (M' * N').map k.subtype = (N' * M').map k.subtype
    rw [hmapmul, hmapmul, hM'map, hN'map, hMN]
  have hM'1 : M' ≠ 1 := by
    intro h
    apply hM1
    rw [← hM'map, h, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨v', l', m', hv', hMv', hNv', hl', hm', hl1⟩ :=
    exists_joint_eigenvector hωk hωk1 hM'3 hN'3 hM'N' hM'1
  have hmulVec : ∀ (A : Matrix ι ι k) (w : ι → k), (fun i => ((A *ᵥ w) i : F)) =
      A.map k.subtype *ᵥ (fun i => (w i : F)) := by
    intro A w
    funext i
    simp [Matrix.mulVec, dotProduct]
  refine ⟨fun i => (v' i : F), (l' : F), (m' : F), ?_, fun i => (hk _).mp (v' i).2, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro h
    apply hv'
    funext i
    exact k.subtype_injective (congrFun h i)
  · rw [← hM'map, ← hmulVec, hMv']
    funext i
    simp
  · rw [← hN'map, ← hmulVec, hNv']
    funext i
    simp
  · have := congrArg Subtype.val hl'
    simpa using this
  · have := congrArg Subtype.val hm'
    simpa using this
  · intro h
    apply hl1
    exact Subtype.ext (by simpa using h)

end Eig

section FieldFacts

theorem exists_primitive_cube_root {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ ω ≠ 1 := by
  classical
  have hc : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (hc ▸ h3)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  refine ⟨(ω : K), ?_, fun h => hω1 (Units.ext h)⟩
  have h3K : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have hne : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have h : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by
    have : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = (ω : K) ^ 3 - 1 := by ring
    rw [this, h3K, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

variable {K : Type} [Field K]

theorem ringEquiv_fixes_cube_root {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : σ ω = ω := by
  have hσ3 : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun f : K ≃+* K => f x) hσ
    simpa [pow_succ] using this
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hu : (σ ω) ^ 2 + σ ω + 1 = 0 := by
    have := congrArg σ hω
    simpa [map_add, map_pow, map_one] using this
  have hfac : (σ ω - ω) * (σ ω - ω ^ 2) = 0 := by
    linear_combination hu - (σ ω) * hω + (ω - 1) * hω
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hu2 : σ ω = ω ^ 2 := sub_eq_zero.mp h
    have h1 : σ (σ ω) = ω := by
      rw [hu2, map_pow, hu2]
      calc (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω3, one_mul]
    have h2 : σ ω = ω := by
      have := hσ3 ω
      rwa [h1] at this
    have h3 : ω ^ 2 = ω := hu2.symm.trans h2
    have hω0 : ω ≠ 0 := by
      rintro rfl
      simp at hω
    exact hω1 (by
      have : ω * (ω - 1) = 0 := by linear_combination h3
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hω0
      · exact sub_eq_zero.mp h)

end FieldFacts

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : 2 ^ (m + m) = 4 ^ m := by
    rw [← two_mul, pow_mul]
    norm_num
  have h : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [h4]
  omega

end CFSG.RankThree.PartTwo.Sec21.Hering214
