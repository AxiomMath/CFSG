module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue
import CFSG.LocalAnalysis.UniquenessCase.UC22P22vd
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wi
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.GroupTheory.PCore.Transport
import CFSG.Blueprint.LieModelAPI
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.Background.SmithC27Star
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
import CFSG.RankThree.PartOne.Q1327T.Defs
import CFSG.RankThree.PartOne.Q1327T.ThetaLift
import CFSG.RankThree.PartTwo.KFacts.KS116Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115
import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
import CFSG.RankThree.PartTwo.Sec11.Transitivity
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.Bender1970.S3.OStar
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213t_not_thin_sp4 {K : Subgroup G} {n : ℕ} (h : IsSp4 (Bar2 K) n) :
    ¬ F08.Thin8 K := by
  intro hthin
  have h1 : CFSG.Open.pRank 3 K ≤ 1 := hthin 3 Nat.prime_three (by norm_num)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)] at h1
  have h2 := uc22p2214_two_le_pRank_sp4 h
  omega

theorem uc22p2213t_not_le_centralizer (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hthin : ¬ F08.Thin8 K) : ¬ K ≤ centralizer (c.V : Set G) := by
  intro hKV
  have hKX : K ∈ calC (F11.CTilde D.M ⊥ c.V) := by
    rw [uc22p22u_cTilde_bot]
    exact uc22p22u_calC_of_le hK (le_inf (uc22p22a_le_of_isSubnormal hK.1) hKV) inf_le_left
  exact hthin (h117 c.V (uc22p22vd_hyp11 D Ch h1930 hV c) K hKX).2

theorem uc22p2213t_onto {M V K : Subgroup G} (hVM : M ≤ normalizer (V : Set G)) (hKM : K ≤ M)
    (hO : ∀ x ∈ CFSG.pCore 2 ↥K, (x : G) ∈ centralizer (V : Set G))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hKV : ¬ K ≤ centralizer (V : Set G)) :
    ∃ ψ : Bar2 K →* ↥(mbarImage M V K), Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Bar2 K) ∧
      ∀ k : ↥K, (ψ (QuotientGroup.mk k) : MBar M V) =
        QuotientGroup.mk (Subgroup.inclusion hKM k) := by
  set φ := uc22br4_phi M V K hKM with hφ
  have hle : CFSG.pCore 2 ↥K ≤ φ.ker := fun x hx => by
    rw [hφ, uc22br4_ker_phi M V K hVM hKM, Subgroup.mem_subgroupOf]
    exact hO x hx
  have hmem : ∀ z, QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hle z ∈ mbarImage M V K := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.lift_mk, ← uc22br4_range_phi M V K hKM]
    exact ⟨k, rfl⟩
  set ψ := (QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hle).codRestrict _ hmem with hψ
  have hs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← uc22br4_range_phi M V K hKM] at hz
    obtain ⟨k, rfl⟩ := hz
    exact ⟨QuotientGroup.mk k, rfl⟩
  refine ⟨ψ, hs, P22sj.le_center_of_quasisimple hq inferInstance fun htop => hKV ?_,
    fun _ => rfl⟩
  rw [← uc22br4_mbarImage_eq_bot_iff M V K hVM hKM, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw⟩ := hs ⟨z, hz⟩
  have h1 : ψ w = 1 := (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top w)
  have h2 : (ψ w : MBar M V) = z := congrArg Subtype.val hw
  rw [Subgroup.mem_bot, ← h2, h1, OneMemClass.coe_one]

theorem uc22p2213t_diag {M V K : Subgroup G} (hKM : K ≤ M) (e : Bar2 K ≃* ↥(mbarImage M V K))
    (he : ∀ k : ↥K, (e (QuotientGroup.mk k) : MBar M V) =
      QuotientGroup.mk (Subgroup.inclusion hKM k))
    {t : G} (htM : t ∈ M) (ht : ActsNontrivOnDiagram K t) :
    ActsNontrivOnDiagramIn (mbarImage M V K) (QuotientGroup.mk ⟨t, htM⟩ : MBar M V) := by
  obtain ⟨htN, θ, hθ, hθn⟩ := ht
  have htN' : (⟨t, htM⟩ : ↥M) ∈ normalizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 htN (h : G)
  refine ⟨le_normalizer_map _ (mem_map_of_mem _ htN'), ?_⟩
  set ε : (Bar2 K ⧸ center (Bar2 K)) ≃* (↥(mbarImage M V K) ⧸ center ↥(mbarImage M V K)) :=
    QuotientGroup.congr _ _ e (map_center_eq e) with hε
  refine ⟨MulAut.congr ε θ, fun a a' haa' => ?_, by rwa [uc22p22wi_isInnDiagFieldAut_congr]⟩
  obtain ⟨y, rfl⟩ := e.surjective a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hk' : t * (k : G) * t⁻¹ ∈ K := (mem_normalizer_iff.1 htN _).1 k.2
  have ha' : a' = e (QuotientGroup.mk ⟨_, hk'⟩) := by
    apply Subtype.ext
    rw [haa', he, he]
    rfl
  subst ha'
  have hs : ε.symm (QuotientGroup.mk (e (QuotientGroup.mk k))) =
      QuotientGroup.mk (QuotientGroup.mk k) := by
    rw [MulEquiv.symm_apply_eq, hε, QuotientGroup.congr_mk]
  show ε (θ (ε.symm (QuotientGroup.mk (e (QuotientGroup.mk k))))) =
    QuotientGroup.mk (e (QuotientGroup.mk ⟨_, hk'⟩))
  rw [hs, hθ k ⟨_, hk'⟩ rfl, hε, QuotientGroup.congr_mk]

end CFSG.LocalAnalysis.UniquenessCase.UC22
