module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Aut
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem tcCard_le_of_perfect_action {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {B J : Subgroup X} (hJ : Group.IsPerfect ↥J) (hB : IsPGroup p ↥B)
    (hn : B ≤ Subgroup.normalizer (J : Set X)) {m e : ℕ}
    (hm : Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) = m) (he : ∀ k, p ^ k ∣ m → k ≤ e) :
    Nat.card B ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) * p ^ e := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥J := hJ
  set ψ : ↥B →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    (actCenterQuot J).comp (Subgroup.inclusion hn) with hψ
  have hker : ψ.ker ≤ (B ⊓ Subgroup.centralizer (J : Set X)).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf]
    refine ⟨b.2, ?_⟩
    show (b : X) ∈ Subgroup.centralizer (J : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (commute_of_actCenterQuot_eq_one J ⟨b, hn b.2⟩ hb j hj).symm
  have hcardB : Nat.card ↥B = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      mul_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker]
  have hrange : IsPGroup p ψ.range :=
    hB.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hrdvd : Nat.card ψ.range ∣ m := by
    rw [← hm]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  obtain ⟨k, hk⟩ := hrange.exists_card_eq
  have hkle : k ≤ e := he k (hk ▸ hrdvd)
  have hker_card : Nat.card ψ.ker ≤
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) := by
    have h1 := Subgroup.card_le_of_le hker
    have h2 : Nat.card ↥((B ⊓ Subgroup.centralizer (J : Set X)).subgroupOf B) =
        Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    omega
  rw [hcardB, hk]
  exact Nat.mul_le_mul hker_card (Nat.pow_le_pow_right hp.pos hkle)

theorem tcFalse_of_L2Four {X : Type} [Group X] [Finite X] {B D J : Subgroup X}
    (hJ : Group.IsPerfect ↥J) (hB : IsElemAbelian 3 B) (hcard : 3 ^ 4 ≤ Nat.card B)
    (hn : B ≤ Subgroup.normalizer (J : Set X)) (hc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hD : Nat.card D = 3 ^ 2) (hmod : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 2) : False := by
  have h120 : Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) = 120 := by
    rw [CFSG.Quasithin.H13.card_mulAut_of_lieModel_L2 (by norm_num) hmod]
    norm_num
  have he : ∀ k, 3 ^ k ∣ 120 → k ≤ 1 := by
    intro k hk
    by_contra hlt
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h9.trans hk
    norm_num at this
  have h := tcCard_le_of_perfect_action Nat.prime_three hJ hB.isPGroup hn h120 he
  rw [hc, hD] at h
  omega

end CFSG.StandardType.TableCRes

end
