module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W7NineOne
public import CFSG.RankThree.PartTwo.Sec19.Statements
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims126b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims121
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.UC6Grp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

section Bridge

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
  {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem ctx19_14_asc81bHyp_and (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx) :
    CFSG.AGLEmbedding.Asc81bHyp H S ∧ H ⊓ normalizer (S : Set G) = H ⊓ D.M := by
  have hLcal : L ∈ calC D.M := S17.calLp_subset_calC D p h.ctx.hyp.hL
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p hLcal.1.le
  have hInorm : ((IOf D p L).subgroupOf D.M).Normal := IOf_normal D p hLcal
  have hBI : B ≤ IOf D p L := by
    rw [h.ctx.hB]
    exact sup_le h.ctx.hA (Subgroup.zpowers_le.mpr h.ctx.htA)
  have hBM : B ≤ D.M := hBI.trans hIM
  have heta : ∀ R : Subgroup G, R ≤ D.M → IsPGroup 2 R → B ≤ normalizer (R : Set G) →
      pCoreOf 2 (IOf D p L) ≤ R → calMOf (D.M ⊓ normalizer (R : Set G)) = {D.M} :=
    fun R hRM hR2 hBR hOR => (h11 R ⟨hRM, hR2, hOR, hBR⟩).2
  have hYmem : Y ∈ muSet D B := h.hY.1
  have hYN : Y ≤ N := h.hN.1.2
  have hNmax : IsMaxTwoLocalSubgroup N := h.hN.1.1
  have hNM : ¬ N ≤ D.M := fun hle => h.hN.2 (hNmax.2 D.M D.maxLocal.1 hle).symm
  have hNne : pCoreOf 2 N ≠ ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.pCoreOf_ne_bot_of_isTwoLocal hNmax.1
  have hmaxY : ∀ Z : Subgroup G, Z ≤ D.M → Z = B ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {D.M} → Y ≤ Z → Z = Y :=
    fun Z hZM hZ hZne hZcal hYZ => h.hY.2 Z ⟨hZM, hZ, hZne, hZcal⟩ hYZ
  have hYH : Y ≤ H := by rw [h.hH]; exact le_sup_right
  have hHN : H ≤ N := by rw [h.hH]; exact sup_le h.hD.1.1.le hYN
  have hHM : ¬ H ≤ D.M := fun hle => h.hD.2 (le_trans le_sup_left (h.hH ▸ hle))
  have hO2NY : pCoreOf 2 N ≤ pCoreOf 2 Y :=
    w7_9_1_4_le_pCore hYmem.1 hYmem.2.1 hYmem.2.2.1
      (w7_9_1_4_normalizer_pCore_le hIM hInorm hBM heta hYmem.1 hYmem.2.1 hYmem.2.2.1 hmaxY)
      hmaxY hYN hNM hNne (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hYN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
  have hO2Hne : pCoreOf 2 H ≠ ⊥ := by
    intro hbot
    apply hNne
    have hO2NH : pCoreOf 2 N ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hO2NY.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH))
        (hHN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [hbot] at hO2NH
    exact le_bot_iff.mp hO2NH
  rw [h.hS]
  exact w7_asc81bHyp D.standing.charTwo hIM hInorm hBM heta hYmem.1 hYmem.2.1 hYmem.2.2.1
    hmaxY hYH hHM hO2Hne

theorem ctx19_14_inf_normalizer (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx) : H ⊓ normalizer (S : Set G) = H ⊓ D.M :=
  (ctx19_14_asc81bHyp_and h h11).2

theorem ctx19_14_asc81bHyp (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx) : CFSG.AGLEmbedding.Asc81bHyp H S :=
  (ctx19_14_asc81bHyp_and h h11).1

theorem ctx19_14_isKGroup (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) :
    CFSG.Open.IsKGroup ↥H := by
  have hYN : Y ≤ N := h.hN.1.2
  have hHN : H ≤ N := by rw [h.hH]; exact sup_le h.hD.1.1.le hYN
  refine CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper D.standing.kProper ?_
  intro hH
  have hMN : D.M ≤ N := le_top.trans (hH ▸ hHN)
  exact h.hN.2 (D.maxLocal.2 N h.hN.1.1.1 hMN)

theorem ctx19_14_isWeakSBlock (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx) : CFSG.AGLEmbedding.IsWeakSBlock H S Dsub := by
  have hYN : Y ≤ N := h.hN.1.2
  have hHN : H ≤ N := by rw [h.hH]; exact sup_le h.hD.1.1.le hYN
  have hDsubH : Dsub ≤ H := by rw [h.hH]; exact le_sup_left
  have hDsubN : Dsub ≤ N := h.hD.1.1.le
  have hSubN : (Dsub.subgroupOf N).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hDsubN).mp h.hD.1.1
  have hSubH : (Dsub.subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hHN hSubN
  have hDsubSubH : CFSG.Open.IsSubnormal Dsub H :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hDsubH).mpr hSubH
  refine ⟨CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims121.isTwoPrimeComponent_of_comp
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126b.isTwoPrimeComp_of hDsubH hDsubSubH
      h.hD.1.2.1 h.hD.1.2.2), ?_⟩
  intro hle
  have hle' : Dsub ≤ H ⊓ normalizer (S : Set G) := le_inf hDsubH hle
  rw [ctx19_14_inf_normalizer h h11] at hle'
  exact h.hD.2 (hle'.trans inf_le_right)

theorem ctx19_14_pRank_le (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) : CFSG.Open.pRank q H ≤ 3 := by
  have hYN : Y ≤ N := h.hN.1.2
  have hHN : H ≤ N := by rw [h.hH]; exact sup_le h.hD.1.1.le hYN
  have he := CFSG.Quasithin.A1b.pRank_le_evenRank hq hq2 h.hN.1.1.1
  rw [h.ctx.h1910.1] at he
  exact (CFSG.SectionRank.pRank_mono hq.one_lt hHN).trans he

theorem ctx19_14_not_inClassXBlock (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h) :
    ¬ CFSG.AGLEmbedding.InClassXBlock Dsub := by
  intro hX
  have hDsubN : Dsub ≤ N := h.hD.1.1.le
  have hSubN : (Dsub.subgroupOf N).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hDsubN).mp h.hD.1.1
  exact h15 (Dsub.subgroupOf N) ((CFSG.CGT.PushingUpLit.isBlockInX_subgroupOf_iff hDsubN).mpr
    ⟨hDsubN, hSubN, CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hX⟩)

theorem ctx19_14_barOfInter_eq (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx) :
    barOfInter D.M Dsub = CFSG.RankThree.PartTwo.Sec19.starIm Dsub (normalizer (S : Set G)) := by
  have hDsubH : Dsub ≤ H := by rw [h.hH]; exact le_sup_left
  have hinf := ctx19_14_inf_normalizer h h11
  have heq : Dsub ⊓ D.M = Dsub ⊓ normalizer (S : Set G) := by
    calc Dsub ⊓ D.M = Dsub ⊓ (H ⊓ D.M) := by rw [← inf_assoc, inf_eq_left.mpr hDsubH]
      _ = Dsub ⊓ (H ⊓ normalizer (S : Set G)) := by rw [hinf]
      _ = Dsub ⊓ normalizer (S : Set G) := by rw [← inf_assoc, inf_eq_left.mpr hDsubH]
  unfold barOfInter CFSG.RankThree.PartTwo.Sec19.starIm
  rw [heq, Subgroup.inf_subgroupOf_left]

end Bridge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
