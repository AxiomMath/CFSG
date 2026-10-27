module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCGraphDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCLift
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCOrthCore
import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLin
import CFSG.LocalAnalysis.StandardType.GGE6DepFrameCentral
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.Adapters.RankTwoModelTransports
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.Open.StatedZModTwo
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.Classical2 CFSG.LieType.Universal.Spin
  CFSG.GroupTheory.WeirSylow CFSG.Open
open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjCongr glCongr_statedScalars)

theorem ggQ2TBCGraph_D {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) [Fact p.Prime]
    {labL : LargeEvenLabel} (hmk : GGQ2TBMarked p L labL) (htag : labL.tag = .D)
    (M : GGQ2LDatum p Bs L x) (hLW : GGQ2LabelWeyl labL M.coxeter) (hshape : M.Shape)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer L Bs) (hr : GGIsReflection p φ)
    (hfix : ∀ b : ↥Bs, (b : G) ∈ D → φ b = b) :
    φ ∈ ggAutomizer J Bs ∨ ∀ ψ ∈ ggAutomizer J Bs, φ * ψ = ψ * φ := by
  subst hp
  obtain ⟨hQ2, hlab, hmark⟩ := hmk
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  have heq : lab' = labL := GGDichotomy.rawDatum_elim_const
    (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, -, h⟩ := hq
      exact h) hraw)
  subst heq
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hfull : M.ShapeFull := ggQ2_shapeFull_of_graph M hLW hlab (Or.inl htag) hx1 hshape
  have hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) := ggE6Dep_hZ hcfg hfull.1
  obtain ⟨tag, rank, n⟩ := lab'
  obtain rfl : tag = .D := htag
  have hn1 : 1 ≤ n := hlab'.1
  have hn2 : n < 2 := hQ2
  obtain rfl : n = 1 := by omega
  have hrk : Even rank ∧ 4 ≤ rank := by simpa [GGQ2TBLabel] using hlab
  have hΛ : Fintype.card M.Λ = rank := by
    obtain ⟨e, -⟩ := hLW
    exact (Fintype.card_congr e).symm.trans (Fintype.card_fin rank)
  dsimp only [LargeEvenRawDatum, CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [if_neg (by omega : rank ≠ 3)] at hraw
  obtain ⟨K, hKf, hKfin, hK, -, -, θ, -⟩ := hraw
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK2
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  let e1 : StatedProj (StatedOmega (StatedQuadPlus rank K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus rank (ZMod 2))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp σ))
      (glCongr_statedScalars σ)
  let e2 : StatedProj (StatedOmega (StatedQuadPlus rank (ZMod 2))) ≃*
      ↥(StatedOmega (StatedQuadPlus rank (ZMod 2))) :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hZ2, Subgroup.bot_subgroupOf])).trans
      QuotientGroup.quotientBot
  let e3 : ↥(StatedOmega (StatedQuadPlus rank (ZMod 2))) ≃*
      ↥(orthDerived (quadPlus rank (ZMod 2))) :=
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 2)).subgroupMap _).trans
      (MulEquiv.subgroupCongr (by
        rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadPlus rank (ZMod 2))]
        exact Subgroup.map_comap_eq_self_of_surjective
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 2)).surjective _))
  have hcore : GGTBCReflCoreIn rank L :=
    ggTBCReflCoreIn_of_quotient_orthDerived (nondegenerate_polarBilin_quadPlus rank (ZMod 2))
      (finrank_quadPlus_space rank) ⟨fun _ => hrk.1, fun _ => isPlusType_quadPlus (ZMod 2) rank⟩
      (((θ.trans e1).trans e2).trans e3) hZ
  exact ggQ2_tbc_of_coreIn hS M hfull (by rw [hΛ]; exact hcore) hφ hr hfix

theorem ggQ2TBCGraphInput_of_F4 (hF4 : GGQ2TBCGraphF4Input) : GGQ2TBCGraphInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hCav _ labL hmk htag M hLW hshape φ hφ hr hfix
  rcases htag with hD | hF
  · exact ggQ2TBCGraph_D hS hp hmk hD M hLW hshape hφ hr hfix
  · exact hF4 hS hp hI1 hCav hmk hF M hLW hshape φ hφ hr hfix

end CFSG.StandardType

end
