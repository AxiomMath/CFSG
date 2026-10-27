module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneNumerics
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {K : Type*} [Field K] (hK : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem coeff_zero_ne_zero_of_dvd {p : ℕ} (hp : 0 < p) {a : K[X]} (hdvd : a ∣ X ^ p - C 1) :
    a.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := hdvd
  have h1 := congrArg (Polynomial.eval 0) hg
  rw [eval_mul, ← Polynomial.coeff_zero_eq_eval_zero a, h0, zero_mul] at h1
  simp [zero_pow hp.ne'] at h1

theorem ordNegQ_dvd_natDegree {p : ℕ} (hp : p.Prime) {x : Module.End K V} (hxp : x ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors x) (hD : a ≠ X - C 1) :
    ordNegQ ℓ f p ∣ 2 * a.natDegree ∧
      (dualPoly hK.bar a = a → ordNegQ ℓ f p ∣ a.natDegree) := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hirr : Irreducible a := irreducible_of_mem_primaryFactors ha
  have : Fact (Irreducible a) := ⟨hirr⟩
  have hmonic : a.Monic := monic_of_mem_primaryFactors ha
  have hdvd : a ∣ X ^ p - C 1 := by
    have h1 : a ∣ minpoly K x := (mem_primaryFactors.mp ha).2.2
    have h2 : minpoly K x ∣ X ^ p - C 1 := minpoly.dvd K x (by simp [hxp])
    exact h1.trans h2
  have h0 : a.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_dvd hp.pos hdvd
  set ζ : AdjoinRoot a := AdjoinRoot.root a with hζ
  have hζp : ζ ^ p = 1 := by
    have h1 : AdjoinRoot.mk a (X ^ p - C 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
    simpa [hζ, sub_eq_zero] using h1
  have hζ1 : ζ ≠ 1 := by
    intro h1
    apply hD
    have h2 : AdjoinRoot.mk a (X - C 1) = 0 := by simp [hζ.symm ▸ h1]
    have h3 : a ∣ X - C 1 := AdjoinRoot.mk_eq_zero.mp h2
    have h4 : Associated a (X - C 1) :=
      hirr.associated_of_dvd (Polynomial.irreducible_X_sub_C 1) h3
    exact Polynomial.eq_of_monic_of_associated hmonic (Polynomial.monic_X_sub_C 1) h4
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.pos.ne'] at hζp
    exact zero_ne_one hζp
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  have hfin : Finite K := hK.finite
  have hfinE : Finite (AdjoinRoot a) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot a) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot a) = ℓ ^ (2 * (f * a.natDegree)) := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_adjoinRoot hK
  have hN1 : 1 ≤ Fintype.card (AdjoinRoot a) := Fintype.card_pos
  have hζN : ζ ^ (Fintype.card (AdjoinRoot a) - 1) = 1 := by
    have h1 : ζ ^ Fintype.card (AdjoinRoot a) = ζ := FiniteField.pow_card ζ
    have h2 : ζ ^ (Fintype.card (AdjoinRoot a) - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel hN1, h1, one_mul]
    exact mul_right_cancel₀ hζ0 h2
  have hpN : p ∣ Fintype.card (AdjoinRoot a) - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hζN
  have hmodN : ((ℓ : ZMod p)) ^ (2 * (f * a.natDegree)) = 1 := by
    have h1 : ((Fintype.card (AdjoinRoot a) - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hpN
    have h2 : ((Fintype.card (AdjoinRoot a) : ℕ) : ZMod p) = 1 := by
      have : Fintype.card (AdjoinRoot a) = (Fintype.card (AdjoinRoot a) - 1) + 1 := by omega
      rw [this, Nat.cast_add, h1, zero_add, Nat.cast_one]
    rw [hcard] at h2
    exact_mod_cast h2
  have hu2 : (-((ℓ : ZMod p) ^ f)) ^ (2 * a.natDegree) = 1 := by
    have hneg : (-((ℓ : ZMod p) ^ f)) ^ (2 * a.natDegree) =
        ((ℓ : ZMod p) ^ f) ^ (2 * a.natDegree) := Even.neg_pow (even_two_mul _) _
    rw [hneg, ← pow_mul, show f * (2 * a.natDegree) = 2 * (f * a.natDegree) by ring]
    exact hmodN
  refine ⟨orderOf_dvd_of_pow_eq_one hu2, fun hself => ?_⟩
  have hθ := theta_root h0 hself
  rw [theta_eq_bar hK h0 hself, UnitaryFieldData.bar_apply] at hθ
  have hζinv : ζ ^ (ℓ ^ (f * a.natDegree)) = ζ⁻¹ := hθ
  have hζq : ζ ^ (ℓ ^ (f * a.natDegree) + 1) = 1 := by
    rw [pow_succ', hζinv, mul_inv_cancel₀ hζ0]
  have hpq : p ∣ ℓ ^ (f * a.natDegree) + 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hζq
  have hmod : (ℓ : ZMod p) ^ (f * a.natDegree) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    exact_mod_cast this
  have hodd : Odd a.natDegree := odd_natDegree_of_selfDual hK h0 hself
  have hu1 : (-((ℓ : ZMod p) ^ f)) ^ a.natDegree = 1 := by
    have hneg : (-((ℓ : ZMod p) ^ f)) ^ a.natDegree = -(((ℓ : ZMod p) ^ f) ^ a.natDegree) :=
      Odd.neg_pow hodd _
    rw [hneg, ← pow_mul]
    have : (ℓ : ZMod p) ^ (f * a.natDegree) = -1 := eq_neg_of_add_eq_zero_left hmod
    rw [this]
    exact neg_neg 1
  exact orderOf_dvd_of_pow_eq_one hu1


theorem dualPoly_X_sub_one (σ : K →+* K) : dualPoly σ (X - C 1 : K[X]) = X - C 1 := by
  have h0 : (X - C 1 : K[X]).coeff 0 ≠ 0 := by simp
  have hm : (X - C 1 : K[X]).Monic := Polynomial.monic_X_sub_C 1
  have h1 := (monic_dualPoly (σ := σ) h0).eq_X_add_C (by
    rw [natDegree_dualPoly h0, natDegree_X_sub_C])
  rw [coeff_zero_dualPoly hm] at h1
  rw [h1]
  simp [sub_eq_add_neg]

theorem ker_sub_one_eq_bot {x : Module.End K V} (hD : (X - C 1 : K[X]) ∉ primaryFactors x) :
    LinearMap.ker (x - 1) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  by_contra hv0
  apply hD
  rw [mem_primaryFactors]
  refine ⟨Polynomial.irreducible_X_sub_C 1, Polynomial.monic_X_sub_C 1, ?_⟩
  have hxv : x v = (1 : K) • v := by
    rw [one_smul]
    exact sub_eq_zero.mp hv
  have hev : x.HasEigenvector 1 v := ⟨Module.End.mem_eigenspace_iff.mpr hxv, hv0⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := minpoly K x) hev
  rw [minpoly.aeval, LinearMap.zero_apply] at h1
  have h2 : (minpoly K x).eval 1 = 0 := (smul_eq_zero.mp h1.symm).resolve_right hv0
  exact Polynomial.dvd_iff_isRoot.mpr h2

theorem finrank_ker_sub_one {x : Module.End K V} :
    Module.finrank K (LinearMap.ker (x - 1)) =
      (X - C 1 : K[X]).natDegree * primaryMultiplicity x (X - C 1 : K[X]) := by
  have : Fact (Irreducible (X - C 1 : K[X])) := ⟨Polynomial.irreducible_X_sub_C 1⟩
  have h := finrank_primaryComponent x (X - C 1 : K[X])
  have e : primaryComponent x (X - C 1 : K[X]) = LinearMap.ker (x - 1) := by
    unfold primaryComponent
    simp
  exact (congrArg (fun s : Submodule K V => Module.finrank K s) e.symm).trans h

theorem ordNegQ_dvd_finrank_sub {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {B : V →ₛₗ[hK.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {x : LinearMap.GeneralLinearGroup K V} (hx : x ∈ sesqUnitaryGroup B)
    (hxp : (x : Module.End K V) ^ p = 1) :
    ordNegQ ℓ f p ∣
      Module.finrank K V - Module.finrank K (LinearMap.ker ((x : Module.End K V) - 1)) := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hsq : Squarefree (minpoly K (x : Module.End K V)) := by
    have : Fact ℓ.Prime := ⟨hK.prime⟩
    have : CharP K ℓ := hK.charP
    have hp0 : (p : K) ≠ 0 := by
      intro h0
      have h1 := (CharP.cast_eq_zero_iff K ℓ p).mp h0
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hK.prime hp).mp h1).symm
    exact squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C 1)
      (Polynomial.separable_X_pow_sub_C 1 hp0 one_ne_zero).squarefree (by simp [hxp])
  have A := r3e_unitary_semisimple_primary_algebra_and_full_centralizer hK B hB hBl x hx hsq
  obtain ⟨P, hP⟩ := A.dimension.1
  have hdim := A.dimension.2 P hP
  obtain ⟨hP1, -, -⟩ := hP
  set fac := primaryFactors (x : Module.End K V) with hfac
  set D : K[X] := X - C 1 with hDdef
  set c := Module.finrank K (LinearMap.ker ((x : Module.End K V) - 1)) with hc
  set T := fac.filter (fun a => dualPoly hK.bar a = a) with hT
  set g : K[X] → ℕ := fun a => a.natDegree * primaryMultiplicity (x : Module.End K V) a with hg
  have hDself : dualPoly hK.bar D = D := dualPoly_X_sub_one hK.bar
  have hTsum : ∑ a ∈ T, g a = c + ∑ a ∈ T.erase D, g a := by
    by_cases hD : D ∈ fac
    · have hDT : D ∈ T := Finset.mem_filter.mpr ⟨hD, hDself⟩
      rw [← Finset.add_sum_erase T g hDT, hc, finrank_ker_sub_one]
    · have hDT : D ∉ T := fun h => hD (Finset.mem_filter.mp h).1
      rw [Finset.erase_eq_of_notMem hDT, hc, ker_sub_one_eq_bot hD, finrank_bot, zero_add]
  have hsub : Module.finrank K V - c = ∑ a ∈ P, 2 * g a + ∑ a ∈ T.erase D, g a := by
    have h1 : Module.finrank K V = ∑ a ∈ P, 2 * g a + (c + ∑ a ∈ T.erase D, g a) := by
      rw [← hTsum]
      exact hdim
    omega
  rw [hsub]
  refine dvd_add (Finset.dvd_sum fun a ha => ?_) (Finset.dvd_sum fun a ha => ?_)
  · have hmem := hP1 a ha
    have hne : a ≠ D := fun h => hmem.2 (by rw [h, hDself])
    have := (ordNegQ_dvd_natDegree hK hp hxp hmem.1 hne).1
    rw [hg]
    show ordNegQ ℓ f p ∣ 2 * (a.natDegree * primaryMultiplicity (x : Module.End K V) a)
    rw [← mul_assoc]
    exact Dvd.dvd.mul_right this _
  · have hmem := Finset.mem_erase.mp ha
    have hT' := Finset.mem_filter.mp hmem.2
    have := (ordNegQ_dvd_natDegree hK hp hxp hT'.1 hmem.1).2 hT'.2
    exact Dvd.dvd.mul_right this _

end CFSG.RankThree.PartOne.KCUnitaryPlane
