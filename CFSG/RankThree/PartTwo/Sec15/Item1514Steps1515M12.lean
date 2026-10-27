module

public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
public import CFSG.RankThree.PartTwo.KFacts.KS1515M12Cover
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.Certificates.CosetTableShort
import CFSG.RankThree.S4Free.SuzukiEight
import Certificates.Certificate2326
import Certificates.Certificate3171
import Certificates.Certificate3171Base

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem claim1515M12_of
    (hK : KFacts.KS1515M12Cover) (h131 : Item131) :
    Claim1515M12 := by
  intro G _ _ A c L h hM X hX4 hXL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨hcL, h9, ⟨eA⟩⟩ := facts_of_m12 h131 sporadicModels131 hD hM
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hD.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := eq_sup_of_card_nine hD h9 fun hc => hcL hc.2
  have hBp : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set B := ((A ⊓ L).subgroupOf L).map π with hBdef
  set Xb := (X.subgroupOf L).map π with hXbdef
  have hBaut : Nonempty (Sec4.autIn ⊤ B ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc hBL hBp
    rw [← hAB] at e
    exact ⟨e.symm.trans eA⟩
  have hB'p : IsPGroup 3 ((A ⊓ L).subgroupOf L) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  have hB9 : Nat.card B = 9 := by
    rw [← Nat.card_congr (mkEquivOfIsPGroup hB'p).toEquiv, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      apply Subtype.ext
      change π a * π b = π b * π a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp ha).1
        (Subgroup.mem_subgroupOf.mp hb).1)
    · obtain ⟨a, ha, rfl⟩ := hx
      have ha3 : a ^ 3 = 1 :=
        Subtype.ext (by simpa using hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp ha).1)
      rw [← map_pow, ha3, map_one]
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX4
  have hXp' : Group.IsPerfect ↥(X.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXL).symm.surjective
  have hXbp : Group.IsPerfect ↥Xb :=
    Group.IsPerfect.ofSurjective (f := π.subgroupMap (X.subgroupOf L))
      (π.subgroupMap_surjective _)
  have hXbne : Xb ≠ ⊥ := by
    intro hbot
    have hXθ : X.subgroupOf L ≤ aschbacherSolvableCore 3 ↥L := by
      intro x hx
      have hx' : π x ∈ Xb := Subgroup.mem_map_of_mem π hx
      rw [hbot, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).mp hx'
    have hsolv : Group.IsSolvable ↥(X.subgroupOf L) := by
      have : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) :=
        (solvable_prime_complement_core_characterization Nat.prime_three).1
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXθ)
        (Subgroup.inclusion_injective hXθ)
    have hnt : Nontrivial ↥(X.subgroupOf L) := by
      have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr (ne_bot_of_mem_scriptY4 hX4)
      exact (Subgroup.subgroupOfEquivOfLe hXL).symm.injective.nontrivial
    exact Group.IsPerfect.not_isSolvable ↥(X.subgroupOf L) hsolv
  have hBN : (A ⊓ L).subgroupOf L ≤
      Subgroup.normalizer ((X.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hX4.1.2 (Subgroup.mem_subgroupOf.mp ha).1) y
  have hBX : B ≤ Subgroup.normalizer (Xb : Set _) :=
    (Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map π)
  have htop := hK _ hM B Xb hBab hB9 hBaut hXbp hXbne hBX
  refine le_antisymm (fun l hl => ?_) (sup_le hXL (Subgroup.map_subtype_le _))
  have hl' : π ⟨l, hl⟩ ∈ Xb := htop ▸ Subgroup.mem_top _
  obtain ⟨x, hx, hxl⟩ := Subgroup.mem_map.mp hl'
  have hmem : x⁻¹ * ⟨l, hl⟩ ∈ aschbacherSolvableCore 3 ↥L := QuotientGroup.eq.mp hxl
  have hl'' : l = (x : G) * ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
  rw [hl'']
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    (Subgroup.mem_sup_right ⟨_, hmem, rfl⟩)

end CFSG.RankThree.PartTwo.Sec15
