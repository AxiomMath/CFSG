module

public import CFSG.Quasithin.Vol2.Ch11SecOE1D
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch11

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Open (pCoreOf)

namespace OE1

variable {G : Type} [Group G]

theorem conjClosure_bot (M : Subgroup G) : conjClosure (⊥ : Subgroup G) M = ⊥ :=
  le_bot_iff.mp (conjClosure_le fun m _ z hz => by
    rw [mem_bot.mp hz, mul_one, mul_inv_cancel]
    exact one_mem _)

theorem exists_ne_one_mem_centralizer [Finite G] {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hYT : Y ≤ T) (hTY : T ≤ normalizer (Y : Set G)) (hY : Y ≠ ⊥) :
    ∃ z ∈ Y, z ≠ 1 ∧ z ∈ centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have : (Y.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYT).mpr hTY
  have hne : Y.subgroupOf T ≠ ⊥ := by
    intro h
    refine hY (eq_bot_iff.mpr fun y hy => ?_)
    have hy' : (⟨y, hYT hy⟩ : ↥T) ∈ Y.subgroupOf T := mem_subgroupOf.mpr hy
    rw [h, mem_bot] at hy'
    exact mem_bot.mpr (congrArg Subtype.val hy')
  obtain ⟨⟨a, haY, haZ⟩, ha1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(a : G), mem_subgroupOf.mp haY, fun h => ha1 (Subtype.ext (Subtype.ext h)),
    mem_centralizer_iff.mpr fun t ht => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨t, ht⟩)

end OE1

theorem tmpL6_3_2_2_six_of (hC58 : TheoremC58) (h317 : AS317Sylow) (h331 : Stmt3_3_1)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h4 : TmpL6_3_2_2_four) : TmpL6_3_2_2_six := by
  intro G _ _ T L I hfsu hne hU
  obtain ⟨hVH, hVred, hOC⟩ := h3228 G T L I hfsu
  have hLc : L ∈ cComp (L ⊔ T) := cComp_of_isLocal hfsu.maximal.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have hred : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVH, hVred⟩
  have hyp : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) :=
    { inM := ⟨hU.1.1, le_sup_right.trans hU.1.2⟩
      nonempty := ((h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L
        hfsu.maximal hfsu.quasisimple).2.2.1
      perfect := eq_oTwoUpper_of_perfect (perfect_conjClosure hperf)
      le_M := le_normalizer
      normal := le_rfl
      unique := hU
      reduced := hred
      centralizer := hOC }
  rcases theorem318_three hC58 h317 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow hyp with
    ⟨hJ, hFF⟩ | ⟨-, -, hZ⟩
  ·
    refine ⟨?_, ⟨hred.2.2.1.1, hFF⟩⟩
    have hL₀L : fsuL0 T L ≤ normalizer (L : Set G) := conjClosure_le fun t ht l hl =>
      LocDbl.le_normalizer_of_mem_cComp hLc
        (LocDbl.map_conj_mem_cComp hLc (le_normalizer (mem_sup_right ht))) ⟨l, hl, rfl⟩
    have hL₀n : ((fsuL0 T L).subgroupOf (fsuL0 T L ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le le_normalizer (le_normalizer_conjClosure L T))
    have hOT : pCoreOf 2 (fsuL0 T L) ≤ T :=
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ le_sup_left
        hL₀n).trans (pCoreOf_two_le_of_isSylowTwoOf
          (isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow le_sup_right))
    exact OE1.eq_commutator_thompsonJ hperf hfsu.quasisimple hT2 hL₀L hOT
      (by rw [hOC]; exact hJ)
  ·
    exfalso
    have hVT : fsuV T I ≤ T := (A4.le_pCoreOf_of_isTwoReducedIn hred).trans (by
      rw [hOC]
      exact inf_le_left)
    have hYne : fsuV T I ⊓ centralizer (fsuL0 T L : Set G) ≠ ⊥ := by
      intro h
      apply hne
      rw [(h4 G T L I hfsu).2, h, OE1.conjClosure_bot]
    have hTY : T ≤ normalizer
        ((fsuV T I ⊓ centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) :=
      OE1.le_normalizer_inf (le_normalizer_conjClosure I T)
        ((le_normalizer_conjClosure L T).trans (OE1.normalizer_le_normalizer_centralizer _))
    obtain ⟨z, hzY, hz1, hzT⟩ :=
      OE1.exists_ne_one_mem_centralizer hT2 (inf_le_left.trans hVT) hTY hYne
    have hle : fsuL0 T L ⊔ T ≤ centralizer ({z} : Set G) := sup_le
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzY.2 l hl))
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzT t ht))
    have hzc : z ∈ CFSG.Quasithin.centerOf (fsuL0 T L ⊔ T) :=
      ⟨hVH hzY.1, mem_centralizer_iff.mpr fun g hg =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hg)⟩
    rw [hZ, mem_bot] at hzc
    exact hz1 hzc

end CFSG.Quasithin.Vol2.Ch11
