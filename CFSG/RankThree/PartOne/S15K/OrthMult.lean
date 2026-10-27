module

public import CFSG.RankThree.PartOne.KC.OrthogonalFactorization
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

theorem two_le_finrank_of_nondegenerate {K : Type*} [Field K] [CharP K 2] {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W] {R : QuadraticForm K W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) : 2 ≤ finrank K W := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < finrank K W := Module.finrank_pos
  have h1 : finrank K W = 1 := by omega
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp h1
  have hww : QuadraticMap.polar R w w = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  apply hw0
  refine hR.1 w fun v => ?_
  obtain ⟨c, rfl⟩ := hw v
  rw [QuadraticMap.polarBilin_apply_apply]
  have : QuadraticMap.polar R w (c • w) = c * QuadraticMap.polar R w w := by
    rw [QuadraticMap.polar_smul_right, smul_eq_mul]
  rw [this, hww, mul_zero]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem oddOrderIsometry_of_order (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ringChar K) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : orderOf x = p) :
    OddOrderIsometry Q p x := by
  refine ⟨hxO, by rw [← hxp]; exact pow_orderOf_eq_one x, ?_, fun v hv =>
    hQ.1 v fun w => by simpa using hv w⟩
  intro h0
  have h1 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
  have h2 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h1
  exact hpl (h2.symm.trans (ringChar.eq K 2).symm)

theorem two_mul_multiplicity_le_finrank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : orderOf x = p) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    2 * primaryMultiplicity x.toLinearMap h ≤ finrank K V := by
  classical
  have hRS := (orthogonal_nontrivial_primary_repeated_quadratic_summands hQ hp hp2 hpl hxO hxp).2.2.2.2.2.2
    h hh hne
  obtain ⟨R, W, instR, instRm, instW, instWm, QR, QW, ψ, -, hWnd, hWnt, -, -, -⟩ := hRS
  set m := primaryMultiplicity x.toLinearMap h with hm
  have hmpos : 0 < m := by
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    exact (oddOrderIsometry_of_order hQ hp hpl hxO hxp).primaryMultiplicity_pos hh
  let ι : (Fin m → W) →ₗ[K] V := ψ.symm.toLinearMap ∘ₗ LinearMap.inr K R (Fin m → W)
  have hιinj : Function.Injective ι := fun a b hab => by
    have := ψ.symm.injective hab
    exact (Prod.mk.injEq _ _ _ _ ▸ this).2
  have hfin : Module.Finite K (Fin m → W) := Module.Finite.of_injective ι hιinj
  let i₀ : Fin m := ⟨0, hmpos⟩
  have hsingle : Function.Injective (LinearMap.single K (fun _ : Fin m => W) i₀) := by
    intro a b hab
    have := congrFun hab i₀
    simpa using this
  have hfinW : Module.Finite K W :=
    Module.Finite.of_injective (LinearMap.single K (fun _ : Fin m => W) i₀) hsingle
  have h2W : 2 ≤ finrank K W := two_le_finrank_of_nondegenerate hWnd
  have hle : finrank K (Fin m → W) ≤ finrank K V := LinearMap.finrank_le_finrank_of_injective hιinj
  have hpi : finrank K (Fin m → W) = m * finrank K W := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [hpi] at hle
  calc 2 * m ≤ m * finrank K W := by rw [mul_comm]; exact Nat.mul_le_mul_left m h2W
    _ ≤ finrank K V := hle

theorem not_dvd_multiplicity (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : orderOf x = p) (hdim : finrank K V = 8)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    ¬ p ∣ primaryMultiplicity x.toLinearMap h := by
  intro hdvd
  have hle := two_mul_multiplicity_le_finrank hQ hp (by omega) hpl hxO hxp hh hne
  have hpos : 0 < primaryMultiplicity x.toLinearMap h := by
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    exact (oddOrderIsometry_of_order hQ hp hpl hxO hxp).primaryMultiplicity_pos hh
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.RankThree.PartOne.S15K
