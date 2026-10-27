module

public import CFSG.LocalAnalysis.StandardType.GGK0LEGammaTw
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem twE6_coe_mul_fieldActor_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (g : twistedE6RootGroup K σ)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (y : twistedE6RootGroup K σ) :
    (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom v *
        fieldActor (t := TwistTag.E6) σ (1 : K ≃+* K)) y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((g : ModGL TwistTag.E6.tag K) * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
          TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v)) *
        (y : ModGL TwistTag.E6.tag K) *
          (((g : ModGL TwistTag.E6.tag K) *
            CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
              TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v))⁻¹) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, fieldActor_one, MulAut.one_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_compatDiagAutHom]
  group

private theorem twE6_coe_mul_fieldActor_sigma
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (g : twistedE6RootGroup K σ)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hσ0 : ∀ z : twistedE6RootGroup K σ,
      ((fieldActor (t := TwistTag.E6) σ σ z : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * (z : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹)
    (y : twistedE6RootGroup K σ) :
    (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom v *
        fieldActor (t := TwistTag.E6) σ σ) y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((g : ModGL TwistTag.E6.tag K) * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
          TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v) *
            diagramMap TwistTag.E6 K) * (y : ModGL TwistTag.E6.tag K) *
        (((g : ModGL TwistTag.E6.tag K) *
          CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
            TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v) *
              diagramMap TwistTag.E6 K)⁻¹) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_compatDiagAutHom, hσ0]
  group

private theorem twE6_baseChange_mem_twistedFixed
    {K L : Type} [Field K] [Field L] [IsAlgClosed L] [Algebra K L] {σ : K ≃+* K}
    {Fr : L →+* L} (hcomm : ∀ c, Fr (algebraMap K L c) = algebraMap K L (σ c))
    (g : twistedE6RootGroup K σ) :
    baseChangeGL (algebraMap K L) (g : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 L Fr :=
  graphFixedRootGroup_le TwistTag.E6 L Fr
    (map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) σ.toRingHom.surjective hcomm
      ⟨g, g.2, rfl⟩)

private theorem twE6_baseChange_rootDiagUnit_mem_twistedFixed
    {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L] {σ : K ≃+* K}
    {Fr : L →+* L} (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L))
    (v : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    baseChangeGL (algebraMap K L)
        (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
          (compatDiag TwistTag.E6 σ.toRingHom v)) ∈
      twistedFixedGroup TwistTag.E6 L Fr :=
  CFSG.StandardType.RecipeExcLang.baseChangeGL_rootDiagUnit_mem_twistedFixed hcomm
    (compatDiag_perm v)

private theorem twE6_mem_model_conj
    {L : Type} [Field L] {Fr : L →+* L} (D : LangDatum TwistTag.E6.tag L)
    (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    {Z : ModGL TwistTag.E6.tag L} (hZ : Z ∈ twistedFixedGroup TwistTag.E6 L Fr) :
    D.g0⁻¹ * Z * D.g0 ∈ D.model := by
  rw [model_eq_map_twistedFixedGroup D hΦ]
  exact ⟨Z, hZ, by simp⟩

private theorem twE6_conj_transport
    {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K ≃+* K}
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L} {g0 : ModGL TwistTag.E6.tag L}
    {ψ : R ≃* twistedE6RootGroup K σ}
    (hψ : ∀ r, baseChangeGL (algebraMap K L) (ψ r) = g0 * iota r * g0⁻¹)
    (u : MulAut R) (W : ModGL TwistTag.E6.tag K)
    (hW : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      W * ((ψ r : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * W⁻¹) :
    ∀ r, iota (u r) = (g0⁻¹ * baseChangeGL (algebraMap K L) W * g0) * iota r *
      (g0⁻¹ * baseChangeGL (algebraMap K L) W * g0)⁻¹ := by
  intro r
  have h1 : baseChangeGL (algebraMap K L) (ψ (u r)) =
      baseChangeGL (algebraMap K L) W * baseChangeGL (algebraMap K L) (ψ r) *
        (baseChangeGL (algebraMap K L) W)⁻¹ := by
    rw [hW r, map_mul, map_mul, map_inv]
  rw [hψ (u r), hψ r] at h1
  calc iota (u r) = g0⁻¹ * (g0 * iota (u r) * g0⁻¹) * g0 := by group
    _ = g0⁻¹ * (baseChangeGL (algebraMap K L) W * (g0 * iota r * g0⁻¹) *
          (baseChangeGL (algebraMap K L) W)⁻¹) * g0 := by rw [h1]
    _ = (g0⁻¹ * baseChangeGL (algebraMap K L) W * g0) * iota r *
          (g0⁻¹ * baseChangeGL (algebraMap K L) W * g0)⁻¹ := by group

private theorem twE6_exists_mulEquiv_conj
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    {K : Type} [Field K] [Algebra K L] {σ : K ≃+* K}
    (hmap : S.Γ.map (MulAut.conj S.D.g0).toMonoidHom =
      (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)))
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (iota_inj : Function.Injective iota) (iota_range : iota.range = S.Γ) :
    ∃ ψ : R ≃* twistedE6RootGroup K σ,
      ∀ r, baseChangeGL (algebraMap K L) (ψ r) = S.D.g0 * iota r * S.D.g0⁻¹ := by
  classical
  let bc : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag L := baseChangeGL (algebraMap K L)
  have hbc : Function.Injective bc := baseChangeGL_injective (algebraMap K L)
  let cj : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L := (MulAut.conj S.D.g0).toMonoidHom
  have hcj : Function.Injective cj := (MulAut.conj S.D.g0).injective
  let eΓ : R ≃* S.Γ := (MonoidHom.ofInjective iota_inj).trans (MulEquiv.subgroupCongr iota_range)
  let eC : S.Γ ≃* S.Γ.map cj := Subgroup.equivMapOfInjective S.Γ cj hcj
  let eS : S.Γ.map cj ≃* (twistedE6RootGroup K σ).map bc := MulEquiv.subgroupCongr hmap
  let eK : (twistedE6RootGroup K σ).map bc ≃* twistedE6RootGroup K σ :=
    (Subgroup.equivMapOfInjective (twistedE6RootGroup K σ) bc hbc).symm
  let ψ : R ≃* twistedE6RootGroup K σ := eΓ.trans (eC.trans (eS.trans eK))
  refine ⟨ψ, fun r => ?_⟩
  have hΓr : (eΓ r : ModGL TwistTag.E6.tag L) = iota r := MonoidHom.ofInjective_apply iota_inj
  have hCr : (eC (eΓ r) : ModGL TwistTag.E6.tag L) = cj (iota r) := by
    rw [Subgroup.coe_equivMapOfInjective_apply, hΓr]
  have hSr : (eS (eC (eΓ r)) : ModGL TwistTag.E6.tag L) = (eC (eΓ r) : ModGL TwistTag.E6.tag L) :=
    MulEquiv.subgroupCongr_apply hmap (eC (eΓ r))
  have hKr : bc (eK (eS (eC (eΓ r)))) = (eS (eC (eΓ r)) : ModGL TwistTag.E6.tag L) := by
    have h := Subgroup.coe_equivMapOfInjective_apply (twistedE6RootGroup K σ) bc hbc
      (eK (eS (eC (eΓ r))))
    dsimp only [eK] at h
    simpa using h.symm
  calc bc (ψ r) = bc (eK (eS (eC (eΓ r)))) := rfl
    _ = (eS (eC (eΓ r)) : ModGL TwistTag.E6.tag L) := hKr
    _ = (eC (eΓ r) : ModGL TwistTag.E6.tag L) := hSr
    _ = cj (iota r) := hCr
    _ = S.D.g0 * iota r * S.D.g0⁻¹ := MulAut.conj_apply _ _

private theorem twE6_exists_modelAction_of_conj
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    {Fr : L →+* L} (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (iota_inj : Function.Injective iota)
    {modelAction : (S.D.model : Type) →* MulAut R}
    (modelAction_compat : ∀ g r, iota (modelAction g r) =
      (g : ModGL TwistTag.E6.tag L) * iota r * (g : ModGL TwistTag.E6.tag L)⁻¹)
    (u : MulAut R) {K : Type} [Field K] [Algebra K L] {σ : K ≃+* K}
    {ψ : R ≃* twistedE6RootGroup K σ}
    (hψ : ∀ r, baseChangeGL (algebraMap K L) (ψ r) = S.D.g0 * iota r * S.D.g0⁻¹)
    (W : ModGL TwistTag.E6.tag K)
    (hW : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      W * ((ψ r : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * W⁻¹)
    (hZ : baseChangeGL (algebraMap K L) W ∈ twistedFixedGroup TwistTag.E6 L Fr) :
    ∃ g : S.D.model, modelAction g = u := by
  have hm : S.D.g0⁻¹ * baseChangeGL (algebraMap K L) W * S.D.g0 ∈ S.D.model :=
    twE6_mem_model_conj S.D hΦ hZ
  refine ⟨⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) W * S.D.g0, hm⟩, ?_⟩
  ext r
  apply iota_inj
  rw [modelAction_compat]
  exact (twE6_conj_transport hψ u W hW r).symm

private theorem twE6_diagram_action_of_conj
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (u : MulAut R) {K : Type} [Field K] [Algebra K L] {σ : K ≃+* K}
    {ψ : R ≃* twistedE6RootGroup K σ}
    (hψ : ∀ r, baseChangeGL (algebraMap K L) (ψ r) = S.D.g0 * iota r * S.D.g0⁻¹)
    (Z : ModGL TwistTag.E6.tag L) (W : ModGL TwistTag.E6.tag K)
    (hbcW : baseChangeGL (algebraMap K L) W = Z * diagramMap TwistTag.E6 L)
    (hW : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      W * ((ψ r : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * W⁻¹) :
    ∀ r, iota (u r) = (S.D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * S.D.g0) * iota r *
      (S.D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * S.D.g0)⁻¹ := by
  intro r
  have h := twE6_conj_transport hψ u W hW r
  rwa [hbcW] at h

private theorem twE6_case_one
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    {Fr : L →+* L} (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (iota_inj : Function.Injective iota)
    {modelAction : (S.D.model : Type) →* MulAut R}
    (modelAction_compat : ∀ g r, iota (modelAction g r) =
      (g : ModGL TwistTag.E6.tag L) * iota r * (g : ModGL TwistTag.E6.tag L)⁻¹)
    (u : MulAut R) {K : Type} [Field K] [Finite K] [Algebra K L] {σ : K ≃+* K}
    {ψ : R ≃* twistedE6RootGroup K σ}
    (hψ : ∀ r, baseChangeGL (algebraMap K L) (ψ r) = S.D.g0 * iota r * S.D.g0⁻¹)
    (g : twistedE6RootGroup K σ)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hα : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom v *
        fieldActor (t := TwistTag.E6) σ (1 : K ≃+* K)) (ψ r) : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K))
    (hcommFun : ∀ c, Fr (algebraMap K L c) = algebraMap K L (σ c))
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L)) :
    ∃ g : S.D.model, modelAction g = u := by
  let d : ModGL TwistTag.E6.tag K :=
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
      (compatDiag TwistTag.E6 σ.toRingHom v)
  let W : ModGL TwistTag.E6.tag K := (g : ModGL TwistTag.E6.tag K) * d
  have hW : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      W * ((ψ r : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * W⁻¹ := by
    intro r
    rw [hα r]
    exact twE6_coe_mul_fieldActor_one g v (ψ r)
  refine twE6_exists_modelAction_of_conj S hΦ iota_inj modelAction_compat u hψ W hW ?_
  rw [show W = (g : ModGL TwistTag.E6.tag K) * d from rfl, map_mul]
  exact mul_mem (twE6_baseChange_mem_twistedFixed hcommFun g)
    (twE6_baseChange_rootDiagUnit_mem_twistedFixed hcomm v)

private theorem twE6_case_sigma
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    {Fr : L →+* L}
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (u : MulAut R) {K : Type} [Field K] [Finite K] [Algebra K L] {σ : K ≃+* K}
    {ψ : R ≃* twistedE6RootGroup K σ}
    (hψ : ∀ r, baseChangeGL (algebraMap K L) (ψ r) = S.D.g0 * iota r * S.D.g0⁻¹)
    (g : twistedE6RootGroup K σ)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hσ0 : ∀ z : twistedE6RootGroup K σ,
      ((fieldActor (t := TwistTag.E6) σ σ z : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * (z : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹)
    (hα : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom v *
        fieldActor (t := TwistTag.E6) σ σ) (ψ r) : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K))
    (hcommFun : ∀ c, Fr (algebraMap K L c) = algebraMap K L (σ c))
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L)) :
    ∃ Z ∈ twistedFixedGroup TwistTag.E6 L Fr, ∀ r, iota (u r) =
      (S.D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * S.D.g0) * iota r *
        (S.D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * S.D.g0)⁻¹ := by
  let d : ModGL TwistTag.E6.tag K :=
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
      (compatDiag TwistTag.E6 σ.toRingHom v)
  let Z : ModGL TwistTag.E6.tag L :=
    baseChangeGL (algebraMap K L) ((g : ModGL TwistTag.E6.tag K) * d)
  let W : ModGL TwistTag.E6.tag K :=
    ((g : ModGL TwistTag.E6.tag K) * d) * diagramMap TwistTag.E6 K
  have hW : ∀ r, ((ψ (u r) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      W * ((ψ r : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * W⁻¹ := by
    intro r
    rw [hα r]
    exact twE6_coe_mul_fieldActor_sigma g v hσ0 (ψ r)
  have hbcW : baseChangeGL (algebraMap K L) W = Z * diagramMap TwistTag.E6 L := by
    rw [show W = ((g : ModGL TwistTag.E6.tag K) * d) * diagramMap TwistTag.E6 K from rfl,
      map_mul, baseChangeGL_diagramMap]
  refine ⟨Z, ?_, twE6_diagram_action_of_conj S u hψ Z W hbcW hW⟩
  rw [show Z = baseChangeGL (algebraMap K L) ((g : ModGL TwistTag.E6.tag K) * d) from rfl, map_mul]
  exact mul_mem (twE6_baseChange_mem_twistedFixed hcommFun g)
    (twE6_baseChange_rootDiagUnit_mem_twistedFixed hcomm v)

theorem exists_modelAction_eq_or_diagram_twE6
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    (hq : S.D.q = 2) (hAlg : S.IsAlgebraic) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (iota_inj : Function.Injective iota) (iota_range : iota.range = S.Γ)
    {modelAction : (S.D.model : Type) →* MulAut R}
    (modelAction_compat : ∀ g r, iota (modelAction g r) =
      (g : ModGL TwistTag.E6.tag L) * iota r * (g : ModGL TwistTag.E6.tag L)⁻¹)
    (u : MulAut R) :
    (∃ g : S.D.model, modelAction g = u) ∨
      ∃ Z ∈ twistedFixedGroup TwistTag.E6 L Fr, ∀ r, iota (u r) =
        (S.D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * S.D.g0) * iota r *
          (S.D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * S.D.g0)⁻¹ := by
  classical
  obtain ⟨K, hKfield, hKfinite, hKalgebra, σ, hKcard, hσq, hmap⟩ :=
    langGamma_conj_eq_map_twistedE6RootGroup (S := S) hAlg hFr hΦ
  let : Field K := hKfield
  let : Finite K := hKfinite
  let : Algebra K L := hKalgebra
  obtain ⟨ψ, hψ⟩ := twE6_exists_mulEquiv_conj S hmap iota_inj iota_range
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hKcard, hq]; norm_num
  have hσ21 : ∀ c, σ c = c ^ (2 ^ 1) := by intro c; rw [hσq, hq]; norm_num
  have hcommFun : ∀ c, Fr (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [hFr, hσq, map_pow]
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    ext c
    exact (hcommFun c).symm
  have horder : orderOf σ = 2 := by
    obtain ⟨σ', hσ', hord, -⟩ :=
      finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two le_rfl K hK2
    have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ21]
    rwa [hσσ'] at hord
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    exact absurd horder (by decide)
  have hσ2 : σ ^ 2 = 1 := by rw [← pow_orderOf_eq_one σ, horder]
  let α : MulAut (twistedE6RootGroup K σ) := ψ.symm.trans (u.trans ψ)
  have hαψ : ∀ r, α (ψ r) = ψ (u r) := by
    intro r
    simp [α, MulEquiv.trans_apply]
  obtain ⟨-, -, -, -, -, -, -, hnf, -, hσ0, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (p := 2) (f := 1)
      Nat.prime_two le_rfl K hK2 σ hσ21
  obtain ⟨g, v, δ, hαgvd⟩ := hnf α
  have hδ2 : δ ^ 2 = 1 := by
    have hcardAut : Nat.card (RingAut K) = 2 := by
      have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (p := 2) (n := 2)
        Nat.prime_two K hK2).1
      simpa using h
    simpa [hcardAut] using pow_card_eq_one' (x := δ)
  rcases eq_one_or_eq_of_sq_eq_one (p := 2) (n := 2) Nat.prime_two hK2 hσ1 hσ2 hδ2 with hδ | hδ
  · rw [hδ] at hαgvd
    refine Or.inl (twE6_case_one S hΦ iota_inj modelAction_compat u hψ g v ?_ hcommFun hcomm)
    intro r
    rw [← hαψ r, hαgvd]
  · rw [hδ] at hαgvd
    refine Or.inr (twE6_case_sigma S u hψ g v hσ0 ?_ hcommFun hcomm)
    intro r
    rw [← hαψ r, hαgvd]

end CFSG.StandardType.LangRat
