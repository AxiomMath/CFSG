module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxMBound
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxU33Cen
public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.U3

namespace GoldCMax

theorem u33_noncomm : u33GenP 0 * u33GenP 3 ≠ u33GenP 3 * u33GenP 0 := by decide +kernel

theorem comm_of_mem_zpowers {G : Type*} [Group G] {g z h : G} (hgz : g * z = z * g)
    (hh : h ∈ Subgroup.zpowers z) : h * g = g * h := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ((Commute.symm (show Commute g z from hgz)).zpow_left k).eq


theorem centralizer_ne_top_u33 {W : Subgroup U33G} (hW : W ≠ ⊥) :
    Subgroup.centralizer (W : Set U33G) ≠ ⊤ := by
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  intro htop
  have hWc : W ≤ Subgroup.center U33G := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (W : Set U33G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg w hw).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h | h
  · exact hW (le_bot_iff.mp (h ▸ hWc))
  · have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (u33GenPG 0)) (u33GenPG 3)
    apply u33_noncomm
    have h' := congrArg u33PresHom hc.symm
    simpa only [map_mul, u33PresHom_genPG] using h'

theorem isMaxSubgroupIn_centralizer_u33 {W : Subgroup U33G} (hW : W ≤ centerOf u33Data.T)
    (hW0 : W ≠ ⊥) : IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set U33G)) := by
  have hWz : W ≤ Subgroup.zpowers u33zc := hW.trans centerOf_T_le
  have hBC : u33Data.B ≤ Subgroup.centralizer (W : Set U33G) := by
    unfold OvergroupData.B
    rw [Subgroup.closure_le]
    intro g hg
    have hgz : g * u33zc = u33zc * g := by
      rcases hg with rfl | rfl | rfl | rfl
      · exact (zc_comm_gen (n := 0) (by norm_num) (by norm_num)).symm
      · exact (zc_comm_gen (n := 1) (by norm_num) (by norm_num)).symm
      · exact (zc_comm_gen (n := 2) (by norm_num) (by norm_num)).symm
      · exact (zc_comm_gen (n := 4) (by norm_num) (by norm_num)).symm
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => comm_of_mem_zpowers hgz (hWz hw)
  have hcard : 96 ≤ Nat.card (Subgroup.centralizer (W : Set U33G)) :=
    card_u33_B ▸ Subgroup.card_le_of_le hBC
  refine isMaxSubgroupIn_of_overgroup_bound (B := 96) (centralizer_ne_top_u33 hW0) hcard
    fun Y hY => ?_
  have hTY : u33Data.T ≤ Y := u33Data.T_le_B.trans (hBC.trans hY)
  rcases u33Data.lattice Y hTY with rfl | rfl | rfl | rfl
  · right
    rw [u33_card_T]
    norm_num
  · right
    rw [card_u33_A]
  · right
    rw [card_u33_B]
  · left
    rfl

end GoldCMax

open GoldCMax in
theorem centMaxProp_u33 :
    CentMaxProp U33G :=
  centMaxProp_of_sylow (S := u33Data.T) u33_syl.1 u33_syl.2 fun _ hW hW0 =>
    isMaxSubgroupIn_centralizer_u33 hW hW0

theorem centMax_u33
    (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q)
    (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) (hQ : IsPSU 3 3 1 Q) (W : Subgroup Q)
    (hW : W ≤ centerOf P) (hW0 : W ≠ ⊥) :
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) := by
  have hLie : CFSG.Blueprint.LieModel Q .PSU 3 3 1 := Or.inl ⟨by decide, hQ⟩
  let eU : Q ≃* U33G := (CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hLie).some.trans
    u33Pres_mulEquiv_PSU3.some.symm
  exact (centMaxProp_u33.of_mulEquiv eU.symm) P hP2 hPi W hW hW0

end CFSG.Quasithin
