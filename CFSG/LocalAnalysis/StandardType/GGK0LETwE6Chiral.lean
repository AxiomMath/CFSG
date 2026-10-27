module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem twistHom_id_eq_diagramMap_conj {L : Type} [Field L]
    (g : ModGL TwistTag.E6.tag L) :
    diagramMap TwistTag.E6 L * g * (diagramMap TwistTag.E6 L)⁻¹ =
      twistHom TwistTag.E6 L (RingHom.id L) g := by
  rw [← conj_diagramMap_eq_twistHom]
  rfl

private theorem diagramMap_mul_rootDiagUnit_mul_inv
    {L : Type} [Field L] (a : Fin TwistTag.E6.tag.rank → Lˣ) :
    diagramMap TwistTag.E6 L * rootDiagUnit TwistTag.E6.tag a *
        (diagramMap TwistTag.E6 L)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => a (TwistTag.E6.perm.symm i)) := by
  rw [twistHom_id_eq_diagramMap_conj, twistHom_rootDiagUnit_eq]
  congr 1

private theorem diagramMap_conj_mem_twistedFixedGroup
    {L : Type} [Field L] {Fr : L →+* L} {y : ModGL TwistTag.E6.tag L}
    (hy : y ∈ twistedFixedGroup TwistTag.E6 L Fr) :
    diagramMap TwistTag.E6 L * y * (diagramMap TwistTag.E6 L)⁻¹ ∈
      twistedFixedGroup TwistTag.E6 L Fr := by
  obtain ⟨hy_adj, hy_fix⟩ :=
    (mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := L) (σ := Fr)).1 hy
  have hP : twistHom TwistTag.E6 L Fr (diagramMap TwistTag.E6 L) =
      diagramMap TwistTag.E6 L := by
    rw [twistHom_apply, units_map_entrywiseHom_diagramMap]
    group
  rw [mem_twistedFixedGroup_iff_twistHom]
  refine ⟨?_, ?_⟩
  · rw [twistHom_id_eq_diagramMap_conj]
    exact twistHom_mem_adjointGroup TwistTag.E6 L (RingHom.id L) hy_adj
  · rw [map_mul, map_mul, map_inv, hP, hy_fix]

private theorem mulAut_conj_eq_modelAction
    {L : Type} [Field L] (D : LangDatum TwistTag.E6.tag L)
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (iota_inj : Function.Injective iota)
    {modelAction : (D.model : Type) →* MulAut R}
    (modelAction_compat : ∀ g r, iota (modelAction g r) =
      (g : ModGL TwistTag.E6.tag L) * iota r * (g : ModGL TwistTag.E6.tag L)⁻¹)
    {N d : ModGL TwistTag.E6.tag L} {u : MulAut R}
    (hu : ∀ r, iota (u r) = N * iota r * N⁻¹)
    (hd : d ∈ D.model) (hNd : N * d * N⁻¹ ∈ D.model) :
    u * modelAction ⟨d, hd⟩ * u⁻¹ = modelAction ⟨N * d * N⁻¹, hNd⟩ := by
  refine MulEquiv.ext fun r => iota_inj ?_
  rw [modelAction_compat (⟨N * d * N⁻¹, hNd⟩ : D.model) r]
  have hu_inv : ∀ s, iota (u⁻¹ s) = N⁻¹ * iota s * N := by
    intro s
    have h := hu (u⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  calc iota ((u * modelAction ⟨d, hd⟩ * u⁻¹) r)
      = iota (u (modelAction ⟨d, hd⟩ (u⁻¹ r))) := by
        rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = N * iota (modelAction ⟨d, hd⟩ (u⁻¹ r)) * N⁻¹ := hu _
    _ = N * (d * iota (u⁻¹ r) * d⁻¹) * N⁻¹ := by rw [modelAction_compat]
    _ = N * (d * (N⁻¹ * iota r * N) * d⁻¹) * N⁻¹ := by rw [hu_inv]
    _ = (N * d * N⁻¹) * iota r * (N * d * N⁻¹)⁻¹ := by group
    _ = ((⟨N * d * N⁻¹, hNd⟩ : D.model) : ModGL TwistTag.E6.tag L) * iota r *
          ((⟨N * d * N⁻¹, hNd⟩ : D.model) : ModGL TwistTag.E6.tag L)⁻¹ := rfl

theorem exists_conj_rootDiagUnit_perm_of_commute_twE6
    {L : Type} [Field L] (D : LangDatum TwistTag.E6.tag L) {Fr : L →+* L}
    (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    {R : Type} [Group R] {iota : R →* ModGL TwistTag.E6.tag L}
    (iota_inj : Function.Injective iota)
    {modelAction : (D.model : Type) →* MulAut R}
    (modelAction_inj : Function.Injective modelAction)
    (modelAction_compat : ∀ g r, iota (modelAction g r) =
      (g : ModGL TwistTag.E6.tag L) * iota r * (g : ModGL TwistTag.E6.tag L)⁻¹)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} (a_model : rootDiagUnit TwistTag.E6.tag a ∈ D.model)
    {Z : ModGL TwistTag.E6.tag L} (hZ : Z ∈ twistedFixedGroup TwistTag.E6 L Fr)
    {u : MulAut R}
    (hu : ∀ r, iota (u r) =
      (D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * D.g0) * iota r *
        (D.g0⁻¹ * (Z * diagramMap TwistTag.E6 L) * D.g0)⁻¹)
    (hcomm : Commute u (modelAction ⟨rootDiagUnit TwistTag.E6.tag a, a_model⟩)) :
    ∃ X ∈ adjointGroup TwistTag.E6.tag L,
      X * rootDiagUnit TwistTag.E6.tag (fun i => a (TwistTag.E6.perm.symm i)) * X⁻¹ =
        rootDiagUnit TwistTag.E6.tag a := by
  set P : ModGL TwistTag.E6.tag L := diagramMap TwistTag.E6 L with hP
  set d : ModGL TwistTag.E6.tag L := rootDiagUnit TwistTag.E6.tag a with hd
  set N : ModGL TwistTag.E6.tag L := D.g0⁻¹ * (Z * P) * D.g0 with hN
  obtain ⟨hZ_adj, -⟩ :=
    (mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := L) (σ := Fr)).1 hZ
  have ha_model : d ∈ (twistedFixedGroup TwistTag.E6 L Fr).map
      (MulAut.conj D.g0⁻¹).toMonoidHom := by
    simpa [model_eq_map_twistedFixedGroup D hΦ] using a_model
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 ha_model
  have hy_d : y = D.g0 * d * D.g0⁻¹ := by
    rw [← hyeq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hPy : P * y * P⁻¹ ∈ twistedFixedGroup TwistTag.E6 L Fr := by
    simpa [hP] using diagramMap_conj_mem_twistedFixedGroup hy
  have hNd_model : N * d * N⁻¹ ∈ D.model := by
    rw [model_eq_map_twistedFixedGroup D hΦ]
    refine Subgroup.mem_map.2 ⟨Z * (P * y * P⁻¹) * Z⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hZ hPy) (inv_mem hZ)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hy_d, hN]
      group
  have hAut : u * modelAction ⟨d, a_model⟩ * u⁻¹ =
      modelAction ⟨N * d * N⁻¹, hNd_model⟩ :=
    mulAut_conj_eq_modelAction D iota_inj modelAction_compat hu a_model hNd_model
  have hcomm' : Commute u (modelAction ⟨d, a_model⟩) := by
    simpa [hd] using hcomm
  have hNd_eq : N * d * N⁻¹ = d := by
    have h1 : modelAction ⟨N * d * N⁻¹, hNd_model⟩ = modelAction ⟨d, a_model⟩ := by
      rw [← hAut, hcomm'.eq]
      group
    exact congrArg Subtype.val (modelAction_inj h1)
  refine ⟨N * P⁻¹, ?_, ?_⟩
  · have hPg : P * D.g0 * P⁻¹ ∈ adjointGroup TwistTag.E6.tag L := by
      simpa [hP] using diagramMap_conj_mem_adjointGroup D.g0_mem
    rw [show N * P⁻¹ = D.g0⁻¹ * Z * (P * D.g0 * P⁻¹) by rw [hN]; group]
    exact mul_mem (mul_mem (inv_mem D.g0_mem) hZ_adj) hPg
  · have hPd : P * d * P⁻¹ =
        rootDiagUnit TwistTag.E6.tag (fun i => a (TwistTag.E6.perm.symm i)) := by
      rw [hd]
      simpa [hP] using diagramMap_mul_rootDiagUnit_mul_inv a
    calc N * P⁻¹ * rootDiagUnit TwistTag.E6.tag (fun i => a (TwistTag.E6.perm.symm i)) *
          (N * P⁻¹)⁻¹
        = N * (P⁻¹ * rootDiagUnit TwistTag.E6.tag (fun i => a (TwistTag.E6.perm.symm i)) *
            P) * N⁻¹ := by group
      _ = N * (P⁻¹ * (P * d * P⁻¹) * P) * N⁻¹ := by rw [← hPd]
      _ = N * d * N⁻¹ := by group
      _ = d := hNd_eq

end CFSG.StandardType.LangRat
