module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeCalW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem seventeen_fiftyfive_natural_of_min (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (h143 : Inputs1719.W4Thm14_3)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀)
    {V : Subgroup G} (hW : InCalW D.M D.T V) (hV : IsElemAbelian 2 V)
    (hB : IsBasicModule (Mbar D.M ⊥ V hV)) (hO2 : O2Trivial (Mbar D.M ⊥ V hV))
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKN : D.M ≤ normalizer (K : Set G))
    (hK2 : pCoreOf 2 K ≤ centralizer (V : Set G)) (hKV : barSub ⊥ V hV K ≠ ⊥)
    (hUT : UniqueMax D.M (K ⊔ D.T)) {n : ℕ} (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (hshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n) :
    IsL2 ↥(barSub ⊥ V hV K) n ∧
      (BinaryNaturalSL (barSub ⊥ V hV K) ⊤ (fixV (barSub ⊥ V hV K)) 2 n ∨
        (Even n ∧ NatOmegaMinus (barSub ⊥ V hV K) ⊤ ⊥ 4 (n / 2))) := by
  have hV1 : InCalV1 D.M D.T V := hW.1
  have hMN : D.M ≤ normalizer (V : Set G) := hV1.1.2.2.1
  have hbot : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hMN hbot
  have hKM : K ≤ D.M := hK.1.le
  have hNorm : (K.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hKN
  have hKsub : CFSG.Open.IsSubnormal K D.M := .step hKM hNorm (.refl D.M)
  have hU : UniqueMax D.M (UC22.conjClosure D.M K ⊔ D.T) := by
    rw [uc22p2214_conjClosure_eq_of_normal hKM hNorm]
    exact hUT
  have h1223 := twelve_twentyThree_one_of_inCalW D hx h61 h126 h111 h124 hW hV hKsub
    hK.2.2 hKV hU
  rw [uc22p2214_conjClosure_eq_of_normal hKM hNorm] at h1223
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split <;> omega
  have hbm : bParam (barSub (⊥ : Subgroup G) V hV K) (Mbar D.M (⊥ : Subgroup G) V hV) + 2 ≥
      E3.mParam (Mbar D.M (⊥ : Subgroup G) V hV) := by
    rw [mBar, bBar] at h1223
    omega
  have hKgroup : CFSG.Open.IsKGroup ↥(Mbar D.M (⊥ : Subgroup G) V hV) :=
    isKGroup_mbar D hV hMs
  have hKall : CFSG.IsKGroup ↥(Mbar D.M (⊥ : Subgroup G) V hV) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKgroup
  have hLY : barSub (⊥ : Subgroup G) V hV K ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
    barSub_mono (⊥ : Subgroup G) V hV hKM
  have hNormBar : ((barSub (⊥ : Subgroup G) V hV K).subgroupOf
      (Mbar D.M (⊥ : Subgroup G) V hV)).Normal :=
    barSub_subgroupOf_mbar_normal hV hKM hKN
  have hKS : K ≤ stabTil (⊥ : Subgroup G) V := hKM.trans hMs
  have h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 K) = ⊥ := by
    rw [CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hMN hbot
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM), uc22p22u_cTilde_bot]
    exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM) hK2
  have hsimple : IsSimpleGroup (Bar2 K) := isSimpleGroup_bar2_of_isL2_or_isSz hshape
  obtain ⟨eKB⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV hKS h2 hKV hsimple
  have hshape' : IsL2 ↥(barSub (⊥ : Subgroup G) V hV K) n ∨
      IsSz ↥(barSub (⊥ : Subgroup G) V hV K) n := by
    rcases hshape with h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eKB h)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eKB h)
  exact h143 (Vtil (⊥ : Subgroup G) V hV) (s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV)
    (Mbar D.M (⊥ : Subgroup G) V hV) (barSub (⊥ : Subgroup G) V hV K) n
    hKall hO2 hB hLY hNormBar hshape' hn hn4 hbm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
