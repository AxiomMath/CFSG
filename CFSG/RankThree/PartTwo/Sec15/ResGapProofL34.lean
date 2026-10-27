module

public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProof
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

namespace ResGapL34

variable {G : Type} [Group G] [Finite G]

theorem card_map_mk_subgroupOf {A Y : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    Nat.card ((A.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) =
      Nat.card (A ⊓ Y : Subgroup G) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  have hT : Nat.card (A.subgroupOf Y) = Nat.card (A ⊓ Y : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ Y ≤ Y)).toEquiv
  rw [← hT]
  refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap (A.subgroupOf Y))
    ⟨fun x y hxy => ?_, π.subgroupMap_surjective _⟩).symm
  have hxy' : π (x : ↥Y) = π (y : ↥Y) := congrArg Subtype.val hxy
  have h1 : (x : ↥Y)⁻¹ * y ∈ CFSG.pCore 2 ↥Y := by
    rw [← QuotientGroup.eq_one_iff]
    change π ((x : ↥Y)⁻¹ * y) = 1
    rw [map_mul, map_inv, hxy', inv_mul_cancel]
  have h3 : (((x : ↥Y)⁻¹ * y : ↥Y) : G) ^ 3 = 1 :=
    hA.2 _ (Subgroup.mem_subgroupOf.mp (mul_mem (inv_mem x.2) y.2))
  have h1' : (((x : ↥Y)⁻¹ * y : ↥Y) : G) ∈ CFSG.Open.pCoreOf 2 Y :=
    Proof1520.mem_pCore_two_iff.mp h1
  have he : (x : ↥Y)⁻¹ * y = 1 := Subtype.ext (Proof1520.eq_one_of_mem_pCoreOf_two h1' h3)
  exact Subtype.ext (eq_of_inv_mul_eq_one he)

theorem le_pCoreOf_of_l34 {A Y Q : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* projSL 3 (GaloisField 2 2))
    (h9 : Nat.card (A ⊓ Y : Subgroup G) = 9) (hQY : Q ≤ Y) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ CFSG.Open.pCoreOf 2 Y := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have hE9 : Nat.card ((A.subgroupOf Y).map π) = 9 := (card_map_mk_subgroupOf hA).trans h9
  have hQcard : Nat.card (Q.subgroupOf Y) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQY).toEquiv
  have hQb3 : ¬ 3 ∣ Nat.card ((Q.subgroupOf Y).map π) := fun h3 =>
    hQ3 (hQcard ▸ h3.trans (Subgroup.card_map_dvd _ _))
  have hEN : (A.subgroupOf Y).map π ≤
      Subgroup.normalizer (((Q.subgroupOf Y).map π : Subgroup _) : Set _) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map _)
    intro a ha
    exact Subgroup.le_normalizer_comap Y.subtype (show (a : G) ∈ _ from hAQ ha)
  set ψ := φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hψ
  have hbot : ((Q.subgroupOf Y).map π).map ψ.toMonoidHom = ⊥ := by
    refine KFacts.L34.eq_bot_of_le_normalizer KFacts.L34.card_galoisField_two_two
      (E := ((A.subgroupOf Y).map π).map ψ.toMonoidHom) ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective ψ.injective, hE9]
    · rwa [Subgroup.card_map_of_injective ψ.injective]
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hEN
  have hQb : (Q.subgroupOf Y).map π = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp hbot
  have hker : Q.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
    have h := (Subgroup.map_eq_bot_iff _).mp hQb
    rwa [hπ, QuotientGroup.ker_mk'] at h
  intro q hq
  exact Proof1520.mem_pCore_two_iff.mp
    (hker (Subgroup.mem_subgroupOf.mpr hq : (⟨q, hQY hq⟩ : ↥Y) ∈ Q.subgroupOf Y))

theorem false_of_l34 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* projSL 3 (GaloisField 2 2))
    (h9 : Nat.card (A ⊓ Y : Subgroup G) = 9) (hY : Y = delta A LB Y) : False := by
  have hYO : Y ≤ CFSG.Open.pCoreOf 2 Y := by
    calc Y = delta A LB Y := hY
      _ ≤ CFSG.Open.pCoreOf 2 Y := sSup_le fun Q hQ =>
          le_pCoreOf_of_l34 hA φ h9 hQ.2
            ((isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1) hQ.1.1.2.2
  have hbot : A ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr
      (Proof1520.eq_one_of_mem_pCoreOf_two (hYO hx.2) (hA.2 x hx.1))
  rw [hbot, Subgroup.card_bot] at h9
  exact absurd h9 (by norm_num)

end ResGapL34

open ResGapL34

theorem step1522HypNotL34_of_meet (hmeet : Step1522HypMeet) : Step1522HypNotL34 := by
  intro G _ _ A c L h Y hctx p P hP
  refine ⟨fun φ => ?_⟩
  exact false_of_l34 (LB := lB A) h.toSec13Data.isElemAbelian φ
    (hmeet G A c L h Y hctx p P hP) hctx.mem_y0Star.prop.1.2.2.1

theorem step1522HypNotL34_of_item138N (h1517 : Step1517R) (h1518 : Step1518R)
    (h138 : Item138N) : Step1522HypNotL34 :=
  step1522HypNotL34_of_meet (step1522HypMeet_of_item138N h1517 h1518 h138)

theorem step1522Hyp_of_item138N (h1517 : Step1517R) (h1518 : Step1518R) (h138 : Item138N) :
    Step1522Hyp :=
  step1522Hyp_of_hessSub h1517 h1518 h138 ks1522HessSub
    (step1522HypNotL34_of_item138N h1517 h1518 h138)

end CFSG.RankThree.PartTwo.Sec15
