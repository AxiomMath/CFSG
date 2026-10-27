module

public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def SevenRank189 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x : Y), IsPGroup 2 P →
    x ∈ Subgroup.normalizer (P : Set Y) → orderOf x = 7 →
    ¬ P ≤ Subgroup.centralizer ({x} : Set Y) →
      ∃ E : Subgroup Y, E ≤ P ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 8

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_s189 (h186 : Item186H) {A M H : Subgroup G} {c : G} (h : Sec18H G A M H c)
    (h7 : Hyp187 A M H c) : CFSG.Open.pCoreOf 2 H ≤ s189 M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 H with hP
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hSH : s189 M H ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hPS : IsPGroup 2 ↥(s189 M H ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_s189 M H)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) (hSH.trans hHP)
  have hAN : A ≤ Subgroup.normalizer ((s189 M H ⊔ P : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_s189 h ha, hHP (le_of_sec18H189 h ha)⟩
  have hmem : s189 M H ⊔ P ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hPS, hAN⟩
  have heq := (mem_maxInvariantPiSubgroups_iff.mp (s189_mem_maxInvariant h186 h h7)).2 _ hmem
    le_sup_left
  rw [← heq]
  exact le_sup_right

theorem three_le_pRank_of_le189 {S E : Subgroup G} (hES : E ≤ S) (hE : IsElementaryAbelian 2 E)
    (hcard : Nat.card E = 8) : 3 ≤ CFSG.pRank 2 ↥S := by
  have hbdd : BddAbove {r : ℕ | ∃ B : Subgroup S, IsElementaryAbelian 2 B ∧
      Nat.card B = 2 ^ r} := by
    refine ⟨Nat.card S, fun r hr => ?_⟩
    obtain ⟨B, -, hB⟩ := hr
    calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card S := Subgroup.card_le_card_group B
  refine le_csSup hbdd ⟨E.subgroupOf S, ?_, ?_⟩
  · have hcomm : ∀ a b : ↥(E.subgroupOf S), a * b = b * a := fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      show ((a : S) : G) * ((b : S) : G) = ((b : S) : G) * ((a : S) : G)
      have := hE.1.is_comm.comm (⟨((a : S) : G), a.2⟩ : E) ⟨((b : S) : G), b.2⟩
      exact congrArg Subtype.val this
    have hexp : ∀ a : ↥(E.subgroupOf S), a ^ 2 = 1 := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) ((a : S) : G) a.2
      simpa using this
    exact
      { toIsMulCommutative := ⟨⟨hcomm⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv, hcard]
    norm_num

theorem step189TwoRank_of (h184 : Item184_1) (h186 : Item186H) (h7 : SevenRank189) :
    Step189TwoRank := by
  intro G _ _ A M H c h hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set L := inSubgroup perfectResidual H with hL
  obtain ⟨e⟩ := (h184 G A M h.toSec18Std H h.mem_scriptH).1
  have h7L : 7 ∣ Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L),
      Nat.card_congr e.toEquiv, KFacts.L34.card_projSL]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 h7L
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hxH : (x : G) ∈ H := hLH x.2
  have hxo : orderOf (x : G) = 7 := by rw [Subgroup.orderOf_coe, hx]
  have hnc : ¬ CFSG.Open.pCoreOf 2 H ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro hle
    have hF := generalizedFitting_eq_of_mem_scriptHStar h.toSec18Std hyp.1 hyp.2.1
    have hxC : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
      rw [hF, Subgroup.mem_centralizer_iff]
      intro y hy
      have hyP : (y : G) ∈ CFSG.Open.pCoreOf 2 H := (mem_pCore_iff_mem_pCoreOf y).mp hy
      have hcomm := Subgroup.mem_centralizer_iff.mp (hle hyP) (x : G) rfl
      exact Subtype.ext hcomm.symm
    have hxF := CFSG.centralizer_generalizedFitting_le ↥H hxC
    rw [hF] at hxF
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hxF⟩
    have hx2 : (x : G) ^ (2 ^ k) = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥H) => ((y : ↥H) : G)) hk
      simpa using this
    have h72 : 7 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one hx2
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h72)
    omega
  obtain ⟨E, hEP, hE, hcard⟩ := h7 G (CFSG.Open.pCoreOf 2 H) (x : G)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hxH) hxo hnc
  exact three_le_pRank_of_le189 (hEP.trans (pCoreOf_le_s189 h186 h hyp)) hE hcard

end CFSG.RankThree.PartTwo.Sec18
