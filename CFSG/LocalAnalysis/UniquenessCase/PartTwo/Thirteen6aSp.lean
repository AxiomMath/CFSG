module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
import CFSG.GroupTheory.IsCyclicOfPRankLeOne
import CFSG.GroupTheory.TPermutingTorus
import CFSG.Quasithin.Background.C1PackImage

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s136a_hyp1754 {D : Data G} (hS : Setting13 D) {p : ℕ} (hp : p ∈ D.sig) :
    S17.Hyp1754 D p :=
  ⟨hp, fun L hL => ⟨hS.hyp131.normal L hL,
    (hS.hyp131.thinOrU3 L hL).imp id fun ⟨n, _, hU⟩ => Or.inl ⟨n, hU⟩⟩⟩

private theorem s136a_isCyclic_barImage_Sp {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (hS : Setting13 D)
    (h638 : UC6.R6_38 D) (h332 : S17.R17_33_2At D V₀ V) (h22 : S17.R17_2_2At D V₀ V hV)
    (h23 : S17.R17_2_3At D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) :
    IsCyclic ↥(barImage D.M (F13.Sp D.M p)) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hle := S17.barImage_Sp_le_pCore D hV (s136a_hyp1754 hS hp) hThin hCyc h638 h332 h22 h23
  rw [S17.sp_eq_f13Sp] at hle
  refine CFSG.isCyclic_of_pRank_le_one hpp hp2 (CFSG.pCore_isPGroup.to_le hle) ?_
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    s13_pRank_barImage hpp hp2 (s13_Sp_le D.M p)]
  exact hS.hyp131.smallS p hp

private theorem s136a_comm_of_isCyclic {M P : Subgroup G} (hPM : P ≤ M)
    [((pCoreOf 2 M).subgroupOf (P ⊔ pCoreOf 2 M)).Normal]
    (hcyc : IsCyclic ↥(barImage M P)) :
    ∀ a b : ↥(P ⊔ pCoreOf 2 M) ⧸ (pCoreOf 2 M).subgroupOf (P ⊔ pCoreOf 2 M), a * b = b * a := by
  have hO2M : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hBM : P ⊔ pCoreOf 2 M ≤ M := sup_le hPM hO2M
  have hcomm : ⁅barImage M (P ⊔ pCoreOf 2 M), barImage M (P ⊔ pCoreOf 2 M)⁆ = ⊥ := by
    rw [s13_barImage_sup hPM hO2M, uc22p22u_barImage_pCore, sup_bot_eq,
      Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.le_centralizer_iff_isMulCommutative]
    exact IsCyclic.isMulCommutative
  have hmem := CFSG.Quasithin.C1Pack.commutator_mem_pCoreOf_of_barImage hBM hBM hcomm
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((x * y)⁻¹ * (y * x) : ↥(P ⊔ pCoreOf 2 M)) : G) =
      (y : G)⁻¹ * (x : G)⁻¹ * ((y : G)⁻¹)⁻¹ * ((x : G)⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact hmem _ (inv_mem y.2) _ (inv_mem x.2)

theorem s136a_exists_permutes_of_Sp {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hThin : ThinList13) (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hS : Setting13 D) (h638 : UC6.R6_38 D) (h332 : S17.R17_33_2At D V₀ V)
    (h22 : S17.R17_2_2At D V₀ V hV) (h23 : S17.R17_2_3At D V₀ V hV) {p : ℕ}
    (hp : p ∈ D.sig) (hSp : F13.Sp D.M p ≠ ⊥) :
    ∃ E ≤ F13.Sp D.M p ⊔ pCoreOf 2 D.M, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧
      Permutes E D.T := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hO2M : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hBM : F13.Sp D.M p ⊔ pCoreOf 2 D.M ≤ D.M := sup_le (s13_Sp_le D.M p) hO2M
  have hMn : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M)
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hBn : ((F13.Sp D.M p ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal := by
    rw [subgroupOf_sup (s13_Sp_le D.M p) hO2M]
    exact sup_normal (H := (F13.Sp D.M p).subgroupOf D.M) (K := (pCoreOf 2 D.M).subgroupOf D.M)
      (hH := s13_Sp_normal D.M p) (hK := (normal_subgroupOf_iff_le_normalizer hO2M).mpr hMn)
  have : ((pCoreOf 2 D.M).subgroupOf (F13.Sp D.M p ⊔ pCoreOf 2 D.M)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (hBM.trans hMn)
  obtain ⟨E, hEB, hE, hEcard, hEperm⟩ := exists_elemAbelian_permutes_of_abelian_quotient
    (s136a_comm_of_isCyclic (s13_Sp_le D.M p)
      (s136a_isCyclic_barImage_Sp hV hThin hCyc hS h638 h332 h22 h23 hp))
    le_sup_right
    (CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM))
    (hTM.trans ((normal_subgroupOf_iff_le_normalizer hBM).mp hBn)) (hTM.trans hMn) hpp hp2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  obtain ⟨s, hs, hso⟩ := s13_exists_orderOf_of_pElementSubgroup_ne_bot hpp hSp
  have hB1 : 1 ≤ CFSG.Open.pRank p (F13.Sp D.M p ⊔ pCoreOf 2 D.M) := by
    refine s13_one_le_pRank_of_dvd _ hpp ?_
    have h := Subgroup.orderOf_dvd_natCard (F13.Sp D.M p ⊔ pCoreOf 2 D.M) (mem_sup_left hs)
    rwa [hso] at h
  refine ⟨E, hEB, hE, s13_one_le_pRank_of_dvd E hpp ?_, hEperm⟩
  rw [hEcard]
  exact dvd_pow_self p (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
