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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

open Module Module.End Polynomial

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem iSup_iInf_eigenspace_eq_top_of_commute {K V ι : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : ι → Module.End K V)
    (hss : ∀ i, (f i).IsSemisimple) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
  have h1 : ∀ i μ, (f i).maxGenEigenspace μ = (f i).eigenspace μ := fun i μ =>
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcomm i j) (fun i => by
      simp only [h1]; exact (hss i).iSup_eigenspace_eq_top)
  simpa only [h1] using this

theorem iSupIndep_iInf_eigenspace_of_commute {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : ι → Module.End K V) (hss : ∀ i, (f i).IsSemisimple)
    (hcomm : ∀ i j, Commute (f i) (f j)) :
    iSupIndep fun χ : ι → K => ⨅ i, (f i).eigenspace (χ i) := by
  have h1 : ∀ i μ, (f i).maxGenEigenspace μ = (f i).eigenspace μ := fun i μ =>
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  simpa only [h1] using this

theorem pow_eq_one_of_sub_one_pow_eq_zero {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {a : A} (h : (a - 1) ^ (ℓ - 1) = 0) : a ^ ℓ = 1 := by
  have h1 : (a - 1) ^ ℓ = a ^ ℓ - 1 := by
    have := congrArg (aeval a) (sub_pow_char (X : K[X]) 1)
    simpa using this
  have h2 : (a - 1) ^ ℓ = 0 := by
    rw [← Nat.sub_add_cancel (Fact.out : ℓ.Prime).one_le, pow_succ, h, zero_mul]
  rw [h1] at h2
  exact sub_eq_zero.mp h2

theorem inv_mul_mul_mem_of_finite {G : Type*} [Group G] (u : G) (E : Subgroup G) [Finite E]
    (hnorm : ∀ e ∈ E, u * e * u⁻¹ ∈ E) : ∀ e ∈ E, u⁻¹ * e * u ∈ E := by
  intro e he
  let g : E → E := fun x => ⟨u * x * u⁻¹, hnorm x x.2⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [g] at this
    exact Subtype.ext (by simpa using this)
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hginj ⟨e, he⟩
  have h1 := congrArg Subtype.val hx
  simp only [g] at h1
  have hx' : u⁻¹ * e * u = x := by rw [← h1]; group
  rw [hx']
  exact x.2

theorem not_linearIndependent_pow_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ℓ : ℕ} (hℓ : 0 < ℓ) {U : Module.End K V} (hU : (U - 1) ^ (ℓ - 1) = 0) (w : V) :
    ¬ LinearIndependent K (fun k : Fin ℓ => (U ^ (k : ℕ)) w) := by
  intro hli
  let q : K[X] := (X - 1) ^ (ℓ - 1)
  have hqmonic : q.Monic := by
    have := (monic_X_sub_C (1 : K)).pow (ℓ - 1)
    simpa using this
  have hqdeg : q.natDegree = ℓ - 1 := by
    have : (X - 1 : K[X]) = X - C 1 := by simp
    simp [q, this, natDegree_pow]
  have hqcoeff : q.coeff (ℓ - 1) = 1 := by
    rw [← hqdeg]; exact hqmonic.coeff_natDegree
  have haev : aeval U q = 0 := by simp [q, hU]
  have hlt : ℓ - 1 < ℓ := by omega
  have hsum : ∑ k : Fin ℓ, q.coeff k • (U ^ (k : ℕ)) w = 0 := by
    have h1 := aeval_eq_sum_range' (R := K) (p := q) (n := ℓ) (by rw [hqdeg]; exact hlt) U
    rw [haev] at h1
    have h2 := congrArg (fun T : Module.End K V => T w) h1
    simp only [LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h2
    rw [Fin.sum_univ_eq_sum_range (fun k => q.coeff k • (U ^ k) w) ℓ]
    exact h2.symm
  have := Fintype.linearIndependent_iff.mp hli (fun k => q.coeff k) hsum ⟨ℓ - 1, hlt⟩
  exact one_ne_zero (hqcoeff.symm.trans this)

theorem hall_higman_abelian_of_injective {K V G : Type*} [Field K] [IsAlgClosed K] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group G]
    (ρ : G →* Module.End K V) (hρ : Function.Injective ρ) (u : G)
    (hu : (ρ u - 1) ^ (ℓ - 1) = 0) (E : Subgroup G) [Finite E] (hE : IsMulCommutative E)
    (hcop : Nat.Coprime (Nat.card E) ℓ) (hnorm : ∀ e ∈ E, u * e * u⁻¹ ∈ E) :
    ∀ e ∈ E, u * e = e * u := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hpow : u ^ ℓ = 1 := by
    apply hρ
    rw [map_pow, map_one]
    exact pow_eq_one_of_sub_one_pow_eq_zero (K := K) hu
  have hnorm' : ∀ e ∈ E, u⁻¹ * e * u ∈ E := inv_mul_mul_mem_of_finite u E hnorm
  let c : E → E := fun e => ⟨u⁻¹ * e * u, hnorm' e e.2⟩
  have hcval : ∀ (k : ℕ) (e : E), ((c^[k] e : E) : G) = (u⁻¹) ^ k * e * u ^ k := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih =>
      intro e
      rw [Function.iterate_succ_apply']
      show u⁻¹ * ((c^[k] e : E) : G) * u = _
      rw [ih, pow_succ' u⁻¹ k, pow_succ u k]
      group
  have hcℓ : ∀ e : E, c^[ℓ] e = e := by
    intro e
    apply Subtype.ext
    rw [hcval, inv_pow, hpow]
    simp
  let F : (E → K) → (E → K) := fun ψ => ψ ∘ c
  have hF : ∀ (k : ℕ) (ψ : E → K), F^[k] ψ = ψ ∘ c^[k] := by
    intro k
    induction k with
    | zero => intro ψ; rfl
    | succ k ih => intro ψ; rw [Function.iterate_succ_apply, ih, Function.iterate_succ']; rfl
  let f : E → Module.End K V := fun e => ρ (e : G)
  have hm0 : (Nat.card E : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hcop.symm
  have hss : ∀ e : E, (f e).IsSemisimple := by
    intro e
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ Nat.card E - 1) ?_ ?_
    · simpa using (Polynomial.separable_X_pow_sub_C (1 : K) hm0 one_ne_zero).squarefree
    · have h1 : (e : G) ^ Nat.card E = 1 := by
        rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
      have h2 : (ρ (e : G)) ^ Nat.card E = 1 := by rw [← map_pow, h1, map_one]
      simp [f, aeval_X_pow, h2]
  have hcomm : ∀ e₁ e₂ : E, Commute (f e₁) (f e₂) := by
    intro e₁ e₂
    show ρ e₁ * ρ e₂ = ρ e₂ * ρ e₁
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (mul_comm' e₁ e₂)
  intro e₀ he₀
  by_contra hne
  have hne' : c ⟨e₀, he₀⟩ ≠ ⟨e₀, he₀⟩ := by
    intro h
    apply hne
    have h1 : u⁻¹ * e₀ * u = e₀ := congrArg Subtype.val h
    calc u * e₀ = u * (u⁻¹ * e₀ * u) := by rw [h1]
      _ = e₀ * u := by group
  let T : Module.End K V := f (c ⟨e₀, he₀⟩) - f ⟨e₀, he₀⟩
  have hT : T ≠ 0 := sub_ne_zero.mpr (fun h => hne' (Subtype.ext (hρ h)))
  have hspan := iSup_iInf_eigenspace_eq_top_of_commute f hss hcomm
  obtain ⟨χ, w, hw, hTw⟩ :
      ∃ (χ : E → K) (w : V), w ∈ (⨅ e, (f e).eigenspace (χ e)) ∧ T w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hT
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hspan]
    exact iSup_le fun χ w hw => LinearMap.mem_ker.mpr (hcon χ w hw)
  have hev : ∀ e, f e w = χ e • w := fun e =>
    mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hw e)
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hTw (map_zero T)
  have hχ : F χ ≠ χ := by
    intro h
    apply hTw
    have h1 : χ (c ⟨e₀, he₀⟩) = χ ⟨e₀, he₀⟩ := congrFun h ⟨e₀, he₀⟩
    show f (c ⟨e₀, he₀⟩) w - f ⟨e₀, he₀⟩ w = 0
    rw [hev, hev, h1, sub_self]
  have hact : ∀ (ψ : E → K) (v : V), v ∈ (⨅ e, (f e).eigenspace (ψ e)) →
      ρ u v ∈ ⨅ e, (f e).eigenspace (F ψ e) := by
    intro ψ v hv
    rw [Submodule.mem_iInf] at hv ⊢
    intro e
    rw [mem_eigenspace_iff]
    have h1 : f e (ρ u v) = ρ u (f (c e) v) := by
      have : (e : G) * u = u * (c e : G) := by
        show _ = u * (u⁻¹ * e * u)
        group
      show (ρ (e : G) * ρ u) v = (ρ u * ρ (c e : G)) v
      rw [← map_mul, ← map_mul, this]
    rw [h1, mem_eigenspace_iff.mp (hv (c e)), map_smul]
    rfl
  have hit : ∀ k : ℕ, (ρ u ^ k) w ∈ ⨅ e, (f e).eigenspace ((F^[k] χ) e) := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      exact hact _ _ ih
  have hne0 : ∀ k : ℕ, (ρ u ^ k) w ≠ 0 := by
    intro k h
    apply hw0
    have h2 : w = ρ (u⁻¹ ^ k) ((ρ u ^ k) w) := by
      rw [← map_pow, ← Module.End.mul_apply, ← map_mul, inv_pow, inv_mul_cancel, map_one]
      rfl
    rw [h2, h, map_zero]
  have hperiod : Function.IsPeriodicPt F ℓ χ := by
    show F^[ℓ] χ = χ
    rw [hF]
    funext e
    simp [Function.comp, hcℓ]
  have hmp : Function.minimalPeriod F χ = ℓ := by
    rcases (Nat.dvd_prime hℓ).mp hperiod.minimalPeriod_dvd with h | h
    · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h) hχ
    · exact h
  have hinj : Function.Injective (fun k : Fin ℓ => F^[(k : ℕ)] χ) := by
    intro i j hij
    refine Fin.ext (Function.iterate_injOn_Iio_minimalPeriod (f := F) (x := χ) ?_ ?_ hij)
    · show (i : ℕ) < _
      rw [hmp]; exact i.2
    · show (j : ℕ) < _
      rw [hmp]; exact j.2
  have hind : iSupIndep fun k : Fin ℓ => ⨅ e, (f e).eigenspace ((F^[(k : ℕ)] χ) e) :=
    (iSupIndep_iInf_eigenspace_of_commute f hss hcomm).comp hinj
  have hli : LinearIndependent K (fun k : Fin ℓ => (ρ u ^ (k : ℕ)) w) :=
    hind.linearIndependent _ (fun k => hit k) (fun k => hne0 k)
  exact not_linearIndependent_pow_apply hℓ.pos hu w hli

theorem hall_higman_abelian {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {n : ℕ}
    (u : Matrix.GeneralLinearGroup (Fin n) K)
    (hu : ((u : Matrix (Fin n) (Fin n) K) - 1) ^ (ℓ - 1) = 0)
    (E : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) [Finite E] (hE : IsMulCommutative E)
    (hcop : Nat.Coprime (Nat.card E) ℓ)
    (hnorm : ∀ e ∈ E, u * e * u⁻¹ ∈ E) :
    ∀ e ∈ E, u * e = e * u := by
  let Φ : Matrix (Fin n) (Fin n) K →+*
      Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) :=
    (RingHomClass.toRingHom (Matrix.toLinAlgEquiv' (R := AlgebraicClosure K) (n := Fin n))).comp
      (algebraMap K (AlgebraicClosure K)).mapMatrix
  have hΦ : Function.Injective Φ := by
    intro a b h
    have h1 := (Matrix.toLinAlgEquiv' (R := AlgebraicClosure K)).injective h
    exact Matrix.map_injective (algebraMap K (AlgebraicClosure K)).injective h1
  let ρ : Matrix.GeneralLinearGroup (Fin n) K →*
      Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) :=
    (Φ : Matrix (Fin n) (Fin n) K →* _).comp (Units.coeHom _)
  have hρ : Function.Injective ρ := fun a b h => Units.ext (hΦ h)
  have hu' : (ρ u - 1) ^ (ℓ - 1) = 0 := by
    have := congrArg Φ hu
    simpa [ρ, map_pow, map_sub] using this
  exact hall_higman_abelian_of_injective ρ hρ u hu' E hE hcop hnorm

end CFSG.SignalizerFunctorTheorem.CatalogBridge
