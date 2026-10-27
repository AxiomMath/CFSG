module

public import CFSG.Sporadic.Schreier.Co1OddTransport
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co1.Module.TwoB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.Sporadic.Co1Schreier.OddCore

open CFSG.Blueprint CFSG.Sporadic.Co1Schreier.OddGen

theorem all_involution_centralizers_odd_core_free_of_inputs
    (hCo2odd : ∀ (a : CFSG.Sporadic.Co2Cert.co2P), orderOf a = 2 →
      CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥) :
    ∀ x : NativeSporadic.Co1, orderOf x = 2 →
      (∀ R : Subgroup (Subgroup.centralizer ({x} : Set NativeSporadic.Co1)), R.Normal →
        Odd (Nat.card R) → R = ⊥) ∧
      CFSG.piCore {p : Nat.Primes | p.1 ≠ 2}
        (Subgroup.centralizer ({x} : Set NativeSporadic.Co1)) = ⊥ ∧
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set NativeSporadic.Co1)) = ⊥ ∧
      CFSG.oddCore (Subgroup.centralizer ({x} : Set NativeSporadic.Co1)) = ⊥ := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := CFSG.Monster.GMS.co1_involution_classes
  intro x hx
  have h := (centOddFreeIn_of_classes hCo2odd hrep hcls x hx).noOddNormal
  have := CFSG.Sporadic.Co1.Module.finite_co1
  exact ⟨h, cores_of_noOddNormal h⟩

theorem fstar_eq_top_of_inner {X : Type*} [Group X] {F : Subgroup X} [F.Normal]
    (hC : Subgroup.centralizer (F : Set X) ≤ F)
    (hinner : ∀ φ : MulAut F, ∃ f : F, φ = MulAut.conj f) : F = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, hf⟩ := hinner (MulAut.conjNormal x)
  have hact : ∀ y ∈ F, x * y * x⁻¹ = (f : X) * y * (f : X)⁻¹ := by
    intro y hy
    have h := congrArg (fun φ : MulAut F => ((φ ⟨y, hy⟩ : F) : X)) hf
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using h
  have hcent : (f : X)⁻¹ * x ∈ Subgroup.centralizer (F : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hact y hy
    calc y * ((f : X)⁻¹ * x) = (f : X)⁻¹ * ((f : X) * y * (f : X)⁻¹) * x := by group
      _ = (f : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = (f : X)⁻¹ * x * y := by group
  have := F.mul_mem f.2 (hC hcent)
  rwa [mul_inv_cancel_left] at this

theorem inner_of_mulEquiv {F K : Type*} [Group F] [Group K] (e : F ≃* K)
    (h : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g) :
    ∀ φ : MulAut F, ∃ f : F, φ = MulAut.conj f := by
  intro φ
  obtain ⟨g, hg⟩ := h (MulAut.congr e φ)
  refine ⟨e.symm g, MulEquiv.ext fun y => ?_⟩
  have h1 := congrArg (fun χ : MulAut K => χ (e y)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem fstar_exclusion_of {K : Type*} [Group K]
    (hinner : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g)
    (hcent : ∀ x : K, orderOf x = 2 → CentOddFreeIn (⊤ : Subgroup K) x)
    {X : Type*} [Group X] [Finite X] (hiso : Nonempty (CFSG.generalizedFitting X ≃* K)) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      (∀ R : Subgroup (Subgroup.centralizer ({t} : Set X)), R.Normal → Odd (Nat.card R) →
        R = ⊥) ∧
      CFSG.piCore {p : Nat.Primes | p.1 ≠ 2} (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨e⟩ := hiso
  have hFn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have htop : CFSG.generalizedFitting X = ⊤ :=
    fstar_eq_top_of_inner (CFSG.centralizer_generalizedFitting_le X) (inner_of_mulEquiv e hinner)
  refine ⟨htop, fun t ht => ?_⟩
  let ψ : X ≃* K := (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans e
  have h2 : orderOf (ψ t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  have hfree := (hcent (ψ t) h2).map_equiv ψ.symm
  rw [MulEquiv.symm_apply_apply] at hfree
  have h := hfree.noOddNormal
  exact ⟨h, cores_of_noOddNormal h⟩

theorem model_simple_generalized_fitting_centralizer_exclusion_of_inputs
    (hCo2inner : ∀ α : MulAut CFSG.Sporadic.Co2Cert.co2P, ∃ g : CFSG.Sporadic.Co2Cert.co2P,
      α = MulAut.conj g)
    (hCo2odd : ∀ (a : CFSG.Sporadic.Co2Cert.co2P), orderOf a = 2 →
      CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥)
    {X : Type*} [Group X] [Finite X] (_hsimple : IsSimpleGroup (CFSG.generalizedFitting X))
    (_hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hiso : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.Co1)) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      (∀ R : Subgroup (Subgroup.centralizer ({t} : Set X)), R.Normal → Odd (Nat.card R) →
        R = ⊥) ∧
      CFSG.piCore {p : Nat.Primes | p.1 ≠ 2} (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := CFSG.Monster.GMS.co1_involution_classes
  exact @fstar_exclusion_of NativeSporadic.Co1 Units.instGroup
    (full_automorphisms_inner_of_inputs hCo2inner) (centOddFreeIn_of_classes hCo2odd hrep hcls)
    X _ _ hiso

theorem sporadicOddCoreFree_Co1_of_inputs
    (hCo2inner : ∀ α : MulAut CFSG.Sporadic.Co2Cert.co2P, ∃ g : CFSG.Sporadic.Co2Cert.co2P,
      α = MulAut.conj g)
    (hCo2odd : ∀ (a : CFSG.Sporadic.Co2Cert.co2P), orderOf a = 2 →
      CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥) :
    CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree .Co1 :=
  fun _ _ _ hF hnc hJ t ht =>
    ((model_simple_generalized_fitting_centralizer_exclusion_of_inputs hCo2inner hCo2odd hF hnc
      hJ).2 t ht).2.2.2

end CFSG.Sporadic.Co1Schreier.OddCore
