module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsComp
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152CompJNT (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, ∀ M ∈ scriptY2 A, Y ≤ M → generalizedFitting ↥M = CFSG.pCore 2 ↥M →
    Y ≤ deltaZero A LB M →
    (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≠ ⊥ →
    ¬ IsQuasisimple ↥(((deltaZero A LB M).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) →
      ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
        (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J

@[expose] noncomputable def Step152CompJNTR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152CompJNT A (lB A)

theorem map_ne_bot_of_mem_scriptY4 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hYM : Y ≤ M) :
    (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≠ ⊥ := by
  intro hbot
  apply ne_bot_of_mem_scriptY4 hY
  have hle : Y.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥M)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M)
  rw [eq_bot_iff, hY.2.1, oPrimeResidualOf, oPrimeResidual, Subgroup.map_le_iff_le_comap,
    Subgroup.closure_le]
  rintro y ⟨k, hk⟩
  have hyM : (y : G) ∈ M := hYM y.2
  have hyO : (⟨y, hyM⟩ : ↥M) ∈ CFSG.pPrimeCore 3 ↥M := hle (Subgroup.mem_subgroupOf.mpr y.2)
  have hk' : (⟨⟨y, hyM⟩, hyO⟩ : CFSG.pPrimeCore 3 ↥M) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hk
    simpa using h
  have hord : orderOf (⟨⟨y, hyM⟩, hyO⟩ : CFSG.pPrimeCore 3 ↥M) = 1 :=
    Nat.dvd_one.mp ((Nat.Coprime.pow_left k hcop).gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_natCard _))
  rw [orderOf_eq_one_iff] at hord
  have h1 : (y : G) = 1 := by
    have h := congrArg (fun z : CFSG.pPrimeCore 3 ↥M => ((z : ↥M) : G)) hord
    simpa using h
  change y ∈ Subgroup.comap Y.subtype ⊥
  rw [Subgroup.mem_comap, Subgroup.mem_bot]
  exact h1

theorem le_deltaZero_of_mem_scriptY4 (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y M : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) (hYM : Y ≤ M) :
    Y ≤ deltaZero A (lB A) M := by
  have h151 := rank3II_15_1_of' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415
    (KFacts.KS14.center_nativeJ2_eq_bot h415) h hY
  rw [h151]
  exact deltaZero_mono hYM

theorem step152CompJ_of (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hJ : Step152CompJNT A (lB A)) : Step152CompJ A (lB A) :=
  fun Y hY M hM hYM hF hq => hJ Y hY M hM hYM hF
    (le_deltaZero_of_mem_scriptY4 h134 h48 h415 h hY hYM) (map_ne_bot_of_mem_scriptY4 hY hYM) hq

theorem step152CompJR_of (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hJ : Step152CompJNTR) : Step152CompJR :=
  fun G _ _ A c L hR => step152CompJ_of h134 h48 h415 hR.toSec14Std (hJ G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
