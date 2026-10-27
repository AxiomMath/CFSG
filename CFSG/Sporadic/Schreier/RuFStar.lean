module

public import CFSG.Sporadic.Schreier.RuOddCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

theorem eq_top_of_inner {X : Type*} [Group X] {F : Subgroup X} [F.Normal]
    (hC : Subgroup.centralizer (F : Set X) ≤ F)
    (hinner : ∀ φ : MulAut F, ∃ f : F, φ = MulAut.conj f) :
    F = ⊤ := by
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

def centralizerEquivOfMulEquiv {X : Type*} [Group X] (ψ : X ≃* ruP) (t : X) :
    Subgroup.centralizer ({t} : Set X) ≃*
      (ruP ⊓ Subgroup.centralizer {((ψ t : ruP) : Equiv.Perm (Fin 4060))} : Subgroup _) where
  toFun c := ⟨ψ c, Subgroup.mem_inf.2 ⟨(ψ c).2, Subgroup.mem_centralizer_singleton_iff.2 (by
      have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
      have := congrArg (fun y => ((ψ y : ruP) : Equiv.Perm (Fin 4060))) h
      simpa only [map_mul, Subgroup.coe_mul] using this)⟩⟩
  invFun d := ⟨ψ.symm ⟨d, (Subgroup.mem_inf.1 d.2).1⟩,
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 d.2).2
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext h)⟩
  left_inv c := Subtype.ext (by simp)
  right_inv d := Subtype.ext (by simp)
  map_mul' c d := Subtype.ext (by simp)

theorem ru_fstar_exclusion
    {X : Type*} [Group X] [Finite X]
    (hiso : Nonempty (CFSG.generalizedFitting X ≃* CFSG.Blueprint.NativeSporadic.Ru)) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      NoOddNormal (Subgroup.centralizer ({t} : Set X)) := by
  obtain ⟨e⟩ := hiso
  have hFn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  set θ : CFSG.generalizedFitting X ≃* ruP := e.trans ruEquivP
  have hinner : ∀ φ : MulAut (CFSG.generalizedFitting X), ∃ f, φ = MulAut.conj f := by
    intro φ
    obtain ⟨g, hg⟩ := mulAut_inner (MulAut.congr θ φ)
    refine ⟨θ.symm g, MulEquiv.ext fun y => ?_⟩
    have h := congrArg (fun χ : MulAut ruP => χ (θ y)) hg
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply] at h
    rw [MulAut.conj_apply]
    apply θ.injective
    rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have htop : CFSG.generalizedFitting X = ⊤ :=
    eq_top_of_inner (CFSG.centralizer_generalizedFitting_le X) hinner
  refine ⟨htop, fun t ht => ?_⟩
  set ψ : X ≃* ruP := (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans θ
  have h2 : orderOf ((ψ t : ruP) : Equiv.Perm (Fin 4060)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  exact NoOddNormal.of_mulEquiv (centralizerEquivOfMulEquiv ψ t).symm
    (noOddNormal_centralizer (ψ t).2 h2)

theorem CTUC_Ru_model_simple_generalized_fitting_centralizer_exclusion
    {X : Type*} [Group X]
    [Finite X] (_hsimple : IsSimpleGroup (CFSG.generalizedFitting X))
    (_hnonab : ∃ x y : CFSG.generalizedFitting X, x * y ≠ y * x)
    (hiso : Nonempty (CFSG.generalizedFitting X ≃* CFSG.Blueprint.NativeSporadic.Ru)) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      (∀ R : Subgroup (Subgroup.centralizer ({t} : Set X)), R.Normal → Odd (Nat.card R) →
        R = ⊥) ∧
      CFSG.piCore {p : Nat.Primes | p.1 ≠ 2} (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨htop, hcent⟩ := ru_fstar_exclusion hiso
  exact ⟨htop, fun t ht => ⟨hcent t ht, (hcent t ht).cores⟩⟩

end CFSG.Sporadic.RuSchreier
