module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenSelected
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenFixed
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenContracts
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs

public section

namespace CFSG.StandardType.GGInnerD4DGenParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCOrthogonal

theorem dgenComposition_holds :
    S2MathAs51600DGenSelected.DGenSelectedMarking.{0} →
    S2MathAs51600DGenFixed.CentralizerImageRewrite →
    S2MathAs51600Contracts.OrthogonalInnerRepresentatives →
    S2MathAs51600Contracts.OrthogonalD4ComponentInner →
    GGLabelRigidInput →
    S2MathAs51600.CentralFixedComponentTransfer →
    GGInnerOnD4DGen := by
  intro hSel hFix hReps hComp hRig hTr
  intro X _instGroupX _instFiniteX A σ J hA hσ hJ hN hmark labJ hΛ htag hrk hlab a ha
  obtain ⟨hX, lab, hΛlab, hraw⟩ := @hSel X _instGroupX _instFiniteX A hmark
  obtain ⟨R, hR, I, F, hsimple, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hregimeInn, hmodel⟩ := hP
  obtain ⟨⟨hlabD, hrkD⟩, hInd⟩ := hregimeInn
  obtain ⟨K, hK, hKf, hKc, V, hV1, hV2, hV3, Q, e, hcard, hreg, hsing, hInd', hcongr⟩ := hmodel
  obtain ⟨t, _ht_inj, ht_conj, ht3, ht4, _ht5⟩ :=
    @hReps K hK hKf hKc V hV1 hV2 hV3 Q hreg hsing X _instGroupX hX (θ.trans e) A hA hInd'
  let θ' : X ⧸ Subgroup.center X ≃* ProjOrthDerived Q := θ.trans e
  let x : orthDerived Q := t ⟨σ, hσ⟩
  have hrep : MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) =
      ggInducedAut θ' σ := ht_conj ⟨σ, hσ⟩
  let π : X →* ProjOrthDerived Q := θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  let β : MulAut (ProjOrthDerived Q) := ggInducedAut θ' σ
  have hsurj : Function.Surjective π := by
    simpa [π] using θ'.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : π.ker ≤ Subgroup.center X := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hy' : (QuotientGroup.mk' (Subgroup.center X)) y = 1 := by
      apply θ'.injective
      simpa [π] using hy
    rw [← QuotientGroup.ker_mk' (Subgroup.center X)]
    exact MonoidHom.mem_ker.mpr hy'
  have hcomm : ∀ y, π (σ y) = β (π y) := fun y => by
    simp only [π, β, MonoidHom.comp_apply]
    exact (ggInducedAut_apply θ' σ y).symm
  obtain ⟨hJcomp, hquot⟩ := hTr π hsurj hker σ β hcomm J hJ
  have hJcompOpen : CFSG.Open.IsComponentOf (J.map π) (ggAutFixedSubgroup β) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hJcomp
  have hfix : ggAutFixedSubgroup β = centralizerImage Q (x : V ≃ₗ[K] V) :=
    @hFix K hK hKf hKc V hV1 hV2 hV3 Q hreg hsing X _instGroupX θ' σ x hrep
  have hIcomp : CFSG.Open.IsComponentOf (J.map π) (centralizerImage Q (x : V ≃ₗ[K] V)) := by
    rw [← hfix]
    exact hJcompOpen
  have hlabJ_eq : labJ = ⟨.D, 4, labJ.n⟩ := by
    cases labJ
    simp_all
  obtain ⟨eiso⟩ := hquot
  have hlabI : GGHasLabel labJ (↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨eiso.symm.trans f⟩) hlab
  rw [hlabJ_eq] at hlabI
  have hxodd : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) :=
    { mem := orthDerived_le_orthogonalGroup x.2
      pow_eq_one := by
        have h3 := ht3 ⟨σ, hσ⟩
        simpa [x, Subgroup.coe_pow] using congrArg (Subtype.val) h3
      cast_ne_zero := by
        intro h3
        have hdvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h3
        omega
      regular := fun v hv => hreg.1 v (fun w => by simpa using hv w) }
  let c : orthDerived Q := t ⟨a, ha⟩
  have hc3 : c ^ 3 = 1 := ht3 ⟨a, ha⟩
  have hcx : Commute c x := ht4 ⟨a, ha⟩ ⟨σ, hσ⟩
  obtain ⟨u, huI, hconj⟩ :=
    @hComp hRig K hK hKf hKc V hV1 hV2 hV3 lab.n labJ.n hΛlab.1 hΛ.1 hcard Q hreg hsing
      x c hxodd hc3 hcx (J.map π) hIcomp hlabI
  refine S2MathAs51600Contracts.liftInnerOnPerfectComponent (Φ := π) (Q := J) (F := J.map π)
    (τ := (a : MulAut X).toMonoidHom) (x := u) hker ?_ rfl huI ?_
  · have hJperf : ⁅J, J⁆ = J := by
      have hcommJ : commutator ↥J = ⊤ := hJ.2.2.1
      have h := congrArg (Subgroup.map (Subgroup.subtype J)) hcommJ
      simpa [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        Subgroup.range_subtype] using h
    exact hJperf
  · intro y hy
    have h1 : π ((MulEquiv.toMonoidHom a) y) = ggInducedAut θ' a (π y) := by
      simp only [π, MonoidHom.comp_apply]
      exact (ggInducedAut_apply θ' a y).symm
    have h2 : ggInducedAut θ' a (π y) =
        MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) c) (π y) := by
      rw [← ht_conj ⟨a, ha⟩]
    rw [h1, h2, MulAut.conj_apply]
    exact hconj (π y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

end CFSG.StandardType.GGInnerD4DGenParts

end
