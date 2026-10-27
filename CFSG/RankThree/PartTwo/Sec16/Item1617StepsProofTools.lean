module

public import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1617

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_bot_of_isSimpleGroup {L : Subgroup G} (hL : IsSimpleGroup ↥L) {n : ℕ}
    (hn : 1 ≤ n) (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  have h3 := Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hiso
  have := Sec4.aschbacherSolvableCore_characteristic ↥L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with
    hbot | htop
  · exact hbot
  · exfalso
    have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 := by
      change (aschbacherSolvableCore 3 ↥L).index = 1
      rw [htop, Subgroup.index_top]
    rw [h1] at h3
    omega

theorem isoLThreePi_of_isSimpleGroup {L : Subgroup G} (hL : IsSimpleGroup ↥L) {n : ℕ}
    (hn : 1 ≤ n) (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n) :
    Sec4.IsoLThreePi ↥L 2 n := by
  have hθ := theta_eq_bot_of_isSimpleGroup hL hn hiso
  exact Proof169.isoLThreePi_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot) hiso

theorem facts_of_isZ3 {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {n : ℕ}
    (hz : IsZ3LThreeTwo A c L n) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A ≤ Subgroup.zpowers c ⊔ L := by
  obtain ⟨hn, hiso, hprod⟩ := hz
  have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
  obtain ⟨hsimp, h2⟩ := Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hiso
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := exists_projImage_model hn hiso
    have hq2 : 2 < 2 ^ n := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
      omega
    exact center_eq_bot_of_mulEquiv φ (center_projImage_slPi hKf hq hq2)
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) hprod.some
  exact ⟨hcL, h9, Sec16.le_sup_of_card_inf h.toSec15R hcL h9⟩

omit [Finite G] in
theorem eq_zpowers_sup_inf {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hAle : A ≤ Subgroup.zpowers c ⊔ L) (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  refine le_antisymm (fun a ha => ?_) (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  have ha' : a ∈ (Subgroup.zpowers c : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN]
    exact hAle ha
  obtain ⟨_, hw, l, hl, rfl⟩ := ha'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hlA : l ∈ A := by
    have : l = (c ^ k)⁻¹ * (c ^ k * l) := by group
    rw [this]
    exact A.mul_mem (A.inv_mem (A.zpow_mem hcA k)) ha
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers c k) ⟨hlA, hl⟩

theorem not_three_dvd_of_isZ3 {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h138 : Item138N) {n : ℕ} (hz : IsZ3LThreeTwo A c L n) : ¬ 3 ∣ n := fun h3 =>
  Sec15.not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hz.1 hz.2.1 hz.2.2
    (Sec15.two_pow_mod_nine_of_three_dvd h3)

omit [Finite G] in
theorem three_dvd_card_L {A L : Subgroup G} {c : G} {n : ℕ} (hz : IsZ3LThreeTwo A c L n) :
    3 ∣ Nat.card L :=
  (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hz.1 hz.2.1).trans
    (Subgroup.card_quotient_dvd_card _)

theorem centralizer_le_normalizer_L {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {n : ℕ}
    (hz : IsZ3LThreeTwo A c L n) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  Sec17.Sec15R.centralizer_le_normalizer_L h.toSec15R (three_dvd_card_L hz)

end CFSG.RankThree.PartTwo.Sec16.Proof1617
