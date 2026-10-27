module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetLang
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
import CFSG.LieType.Steinberg.Isogeny.TwistedE6
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRet_innerDiag_E6
    {f : ℕ} (hf : f ≠ 0) {σ : GGL ≃+* GGL} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : GaloisField 2 f →+* GGL)
    {zh t : ModGL Tag.E6 GGL} (hzh : zh ∈ adjointGroup Tag.E6 GGL)
    (ht : t ∈ adjointGroup Tag.E6 GGL) {w' : WeylGroup Tag.E6}
    (hlang : frobGL σ zh⁻¹ = zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w')
    (htfix : canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ t *
      (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ = t)
    {ψ : (ggU .E6 0 f).K →* ModGL Tag.E6 GGL}
    (hψ : ∀ (i : Fin Tag.E6.rank) (c : GaloisField 2 f),
      ψ (e6Data_valid.xm (GaloisField 2 f) (Pi.single i 1) c) =
        zh * pinnedX Tag.E6 GGL (Pi.single i 1) (e c) * zh⁻¹ ∧
      ψ (e6Data_valid.xm (GaloisField 2 f) (-Pi.single i 1) c) =
        zh * pinnedX Tag.E6 GGL (-Pi.single i 1) (e c) * zh⁻¹) :
    GGPsiInnerDiag (ggU .E6 0 f).D ψ t := by
  classical
  letI : Algebra (GaloisField 2 f) GGL := e.toAlgebra
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hFrf : ∀ c, σ.toRingHom c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hcard]; exact hσ c
  have hFzh : frobGL σ zh = (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ * zh := by
    have h := congrArg (fun m => m⁻¹) hlang
    simpa using h
  have ht' : frobGL σ (zh⁻¹ * t * zh) = zh⁻¹ * t * zh := by
    calc frobGL σ (zh⁻¹ * t * zh) = frobGL σ zh⁻¹ * frobGL σ t * frobGL σ zh := by
          rw [map_mul, map_mul]
      _ = (zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w') * frobGL σ t *
            ((canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ * zh) := by rw [hlang, hFzh]
      _ = zh⁻¹ * (canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ t *
            (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹) * zh := by group
      _ = zh⁻¹ * t * zh := by rw [htfix]
  have hadj' : zh⁻¹ * t * zh ∈ adjointGroup Tag.E6 GGL :=
    mul_mem (mul_mem (inv_mem hzh) ht) hzh
  obtain ⟨a, j, hj, hdec⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.exists_rootDiagUnit_mul_of_frobenius_fixed
      (K := GaloisField 2 f) (L := GGL) σ.toRingHom hFrf σ.bijective hadj' ht'
  have htdec : t = zh * baseChangeGL (algebraMap (GaloisField 2 f) GGL)
      (rootDiagUnit Tag.E6 a * j) * zh⁻¹ := by
    rw [← hdec]; group
  let χ : adjointGroup Tag.E6 (GaloisField 2 f) →* ModGL Tag.E6 GGL :=
    (MulAut.conj zh).toMonoidHom.comp
      ((baseChangeGL (algebraMap (GaloisField 2 f) GGL)).comp
        (adjointGroup Tag.E6 (GaloisField 2 f)).subtype)
  have hχval : ∀ u, χ u = zh * baseChangeGL (algebraMap (GaloisField 2 f) GGL)
      (u : ModGL Tag.E6 (GaloisField 2 f)) * zh⁻¹ := fun u => rfl
  have hχ : Function.Injective χ := by
    intro x y hxy
    rw [hχval, hχval] at hxy
    have h1 : baseChangeGL (algebraMap (GaloisField 2 f) GGL) (x : ModGL Tag.E6 (GaloisField 2 f)) =
        baseChangeGL (algebraMap (GaloisField 2 f) GGL) (y : ModGL Tag.E6 (GaloisField 2 f)) :=
      mul_left_cancel (mul_right_cancel hxy)
    exact Subtype.ext (baseChangeGL_injective _ h1)
  have hval : ∀ u, ψ u = χ (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f) u) := by
    have hcomp : ψ = χ.comp (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f)) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top e6Data_valid
          (GaloisField 2 f)) ?_
      rintro _ ⟨i, c, rfl | rfl⟩
      · refine ((hψ i c).1).trans ?_
        rw [MonoidHom.comp_apply, hχval,
          CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm (IsRoot.basis i) c, baseChangeGL_pinnedX]
        rfl
      · refine ((hψ i c).2).trans ?_
        rw [MonoidHom.comp_apply, hχval,
          CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm (IsRoot.neg (IsRoot.basis i)) c,
          baseChangeGL_pinnedX]
        rfl
    exact fun u => DFunLike.congr_fun hcomp u
  have hker : ψ.ker ≤ Subgroup.center (ggU .E6 0 f).K := by
    intro x hx
    rw [MonoidHom.mem_ker, hval] at hx
    have h1 : CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f) x = 1 :=
      hχ (by rw [hx, map_one])
    exact CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
      (GaloisField 2 f) (MonoidHom.mem_ker.2 h1)
  have hrange : ψ.range = χ.range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      rw [hval]
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, rfl⟩ := CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective (GaloisField 2 f) v
      exact ⟨u, hval u⟩
  let g : ↥(adjointGroup Tag.E6 (GaloisField 2 f)) := ⟨j⁻¹, inv_mem hj⟩
  let a' : Fin Tag.E6.rank → (GaloisField 2 f)ˣ := a⁻¹
  have hact : ∀ u : ↥(adjointGroup Tag.E6 (GaloisField 2 f)),
      t⁻¹ * χ u * t = χ ((MulAut.conj g * rootDiagAut Tag.E6 (GaloisField 2 f) a') u) := by
    intro u
    rw [hχval, hχval, htdec]
    have hR : (((MulAut.conj g * rootDiagAut Tag.E6 (GaloisField 2 f) a') u :
        ↥(adjointGroup Tag.E6 (GaloisField 2 f))) : ModGL Tag.E6 (GaloisField 2 f)) =
        j⁻¹ * ((rootDiagUnit Tag.E6 a)⁻¹ * (u : ModGL Tag.E6 (GaloisField 2 f)) *
          rootDiagUnit Tag.E6 a) * j := by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut]
      change j⁻¹ * (rootDiagUnit Tag.E6 a⁻¹ * (u : ModGL Tag.E6 (GaloisField 2 f)) *
        (rootDiagUnit Tag.E6 a⁻¹)⁻¹) * j⁻¹⁻¹ = _
      rw [← rootDiagUnit_inv, inv_inv, inv_inv]
    rw [hR]
    simp only [map_mul, map_inv]
    group
  have hc : t ∈ Subgroup.normalizer (ψ.range : Set (ModGL Tag.E6 GGL)) := by
    rw [Subgroup.mem_normalizer_iff'', hrange]
    intro y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, (hact u).symm⟩
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu⟩ : ∃ u, (MulAut.conj g * rootDiagAut Tag.E6 (GaloisField 2 f) a') u = v :=
        ⟨_, MulEquiv.apply_symm_apply _ v⟩
      refine ⟨u, ?_⟩
      have h1 := hact u
      rw [hu] at h1
      have h2 : t⁻¹ * χ u * t = t⁻¹ * y * t := h1.trans hv
      calc χ u = t * (t⁻¹ * χ u * t) * t⁻¹ := by group
        _ = t * (t⁻¹ * y * t) * t⁻¹ := by rw [h2]
        _ = y := by group
  exact CFSG.StandardType.ExcFieldAutCentRankE6.ggPsiInnerDiag_of_induced_conj_diag hχ hval hker
    hc hact

end CFSG.StandardType.RCKRP

end
