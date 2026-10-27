module

public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigDefs
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL227
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item14Hyperplanes
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan154Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem eight_dvd_card_of_isLThreeEpsAt {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (h : IsLThreeEpsAt X p f) : 8 ∣ Nat.card X := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_projSL_three _
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_projSU_three p f hf

theorem eight_dvd_card_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) : 8 ∣ Nat.card X := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_projSL_three _
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_projSU_three p e he

theorem eight_dvd_card_of_types136 {X : Type} [Group X]
    (hT : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    8 ∣ Nat.card X := by
  rcases hT with ⟨⟨φ⟩⟩ | ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_J2
  · exact eight_dvd_card_of_isoLThreePi he hiso
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_alternating_seven
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_M22
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_M12

variable {G : Type} [Group G] [Finite G]

theorem eight_dvd_card_img148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {e : G} {K Le : Subgroup G}
    (hkt : KType148 A Y e K Le) : 8 ∣ Nat.card (img148 A Y K) := by
  rcases hkt.2 with ⟨he, hLe, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hL3⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact eight_dvd_card_of_types136 (h.chosen136.2 e he Le hLe).1
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_alternating_seven
  · exact eight_dvd_card_of_isLThreeEpsAt hf hL3
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_alternating_seven
  · rw [Nat.card_congr φ.toEquiv]
    exact RonanStep131b.L227.eight_dvd_card_projSL_three _

section Certificates


theorem big152_of_not_allPointsHJ (h134 : Item134) (h48 : Sec4.Item4_8)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) {X : Subgroup G}
    (hX : X ∈ scriptY4 A (lB A)) : Big152 X := by
  have hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
  have hXp : Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) := hq.1
  have hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
    lB_eq_bot_of_not_allPointsHJ' h134 h48 h hNHJ hB
  have hAc : IsMulCommutative ↥A := h.toSec13Data.isElemAbelian.1
  have hYB : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) X B := fun B hB =>
    yBOne_of_lB_eq_bot hAc hB (hLB B hB)
  obtain ⟨f, -, hf⟩ := exists_hyperplanes_thirteen h.isE27
  have hXΔ : X = deltaZero A (lB A) X :=
    rank3II_15_1_lB h.isE27 ⟨f 0, hf 0, hLB _ (hf 0)⟩ hX
  have hXs : ¬ Group.IsSolvable ↥X := by
    intro hsol
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have : Nontrivial (↥X ⧸ CFSG.pCore 2 ↥X) := ⟨⟨a', b', fun hab' => hab (by rw [hab'])⟩⟩
    exact Group.IsPerfect.not_isSolvable (↥X ⧸ CFSG.pCore 2 ↥X) inferInstance
  have hcore : ¬ ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ X ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({b} : Set G)) := by
    intro hc
    have h1 : Case148One A (lB A) X := case148One_of_core hCore h hX.1 hXs hYB hc
    have h1' : deltaZero A (lB A) X ≤ pPrimeCoreOf 3 X := h1
    rw [← hXΔ] at h1'
    apply Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hX
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1' y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h X hX.1 hXs hYB B hB Q hQ hQY b hb hb1 hQb
  let := ker148_normal hX.1.2
  have hkt : KType148 A X e K Le := hKT G A c L h X hX.1 hXs hYB B Q e K Le hP
  have h8 : 8 ∣ Nat.card ↥(img148 A X K) := eight_dvd_card_img148 h hkt
  have hK : K ∈ thetaComponentsIn (X ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKX : K ≤ X := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  obtain ⟨eK⟩ := Y4Core.nonempty_img148_equiv_map hX.1.2 hKX
  have h1 : Nat.card ↥(img148 A X K) ∣ Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
    rw [Nat.card_congr eK.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) :=
    Subgroup.index_dvd_of_le
      (CFSG.GroupTheory.pCore_le_pPrimeCore Nat.prime_two Nat.prime_three (by norm_num) ↥X)
  exact h8.trans (h1.trans h2)

theorem y4BigNHJR_of (h134 : Item134) (h48 : Sec4.Item4_8) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) : Y4BigNHJR :=
  fun _ _ _ _ _ _ hR hNHJ _ hX =>
    big152_of_not_allPointsHJ h134 h48 hCore hPoint hKT hR.toSec14Std hNHJ hX

end Certificates

end CFSG.RankThree.PartTwo.Sec15.Ronan154Big
