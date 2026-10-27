module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Defs
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Center
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Cent
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Conj
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y143

theorem exists_is143Point (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {B : Subgroup G} (hBA : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A)
    {Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))} (hYc : CFSG.IsComponent Yc)
    (ha : ∃ a ∈ A, a ∉ B ∧ a ∈ (Yc.comap (QuotientGroup.mk'
      (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
        (Subgroup.centralizer (B : Set G)).subtype)
    (hne : (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ⊓ Yc ≠ ⊥) :
    SectionFourHyp ↥Yc ∧ Nat.card (Subgroup.center ↥Yc) = 3 ∧ ∃ x : ↥Yc, Is143Point x := by
  classical
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  let N : Subgroup ↥C := CFSG.pPrimeCore 3 ↥C
  obtain ⟨hY4, hZ3, hZeq⟩ :=
    center_map_eq_inf_of_ne_bot h1 h2 h43 hin hR hBA hYc hne
  obtain ⟨a, haA, haB, haY⟩ := ha
  obtain ⟨a', ha'comap, ha'a⟩ := Subgroup.mem_map.mp haY
  have ha'Y : QuotientGroup.mk' N a' ∈ Yc := ha'comap
  let x : ↥Yc := ⟨QuotientGroup.mk' N a', ha'Y⟩
  have hx : (x : ↥C ⧸ N) = QuotientGroup.mk' N a' := rfl
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hA3 : IsPGroup 3 (A.subgroupOf C) :=
    (hR.mem_partTwoF.1.subgroupOf C).isPGroup
  have ha'a' : (a' : G) = a := ha'a
  have ha'_memA : (a' : G) ∈ A := by
    rw [ha'a']
    exact haA
  have ha'_notB : (a' : G) ∉ B := by
    rw [ha'a']
    exact haB
  have ha3 : a ^ 3 = 1 := hR.mem_partTwoF.1.2 a haA
  have ha'3 : a' ^ 3 = 1 := by
    apply Subtype.ext
    show (a' : G) ^ 3 = 1
    rw [ha'a']
    exact ha3
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    show (x : ↥C ⧸ N) ^ 3 = 1
    rw [hx, ← map_pow, ha'3, map_one]
  have hx_not_center : x ∉ Subgroup.center ↥Yc := by
    intro hxZ
    have hxZmap : (x : ↥C ⧸ N) ∈ (Subgroup.center ↥Yc).map Yc.subtype :=
      ⟨x, hxZ, rfl⟩
    rw [hZeq] at hxZmap
    obtain ⟨b', hb'B, hb'x⟩ := Subgroup.mem_map.mp hxZmap.1
    have hb'a : QuotientGroup.mk' N b' = QuotientGroup.mk' N a' := by
      rw [← hx]
      exact hb'x
    have hb'A : (b' : G) ∈ A := hBA.1 (Subgroup.mem_subgroupOf.mp hb'B)
    have hEq : (⟨a', ha'_memA⟩ : A.subgroupOf C) = ⟨b', hb'A⟩ := by
      apply Sylow155T51.injective_mk_comp_subtype N hN3 hA3
      show QuotientGroup.mk' N a' = QuotientGroup.mk' N b'
      exact hb'a.symm
    have hab : a' = b' := congrArg Subtype.val hEq
    have ha'B : (a' : G) ∈ B := by
      rw [hab]
      exact Subgroup.mem_subgroupOf.mp hb'B
    have haB' : a ∈ B := by
      rw [← ha'a']
      exact ha'B
    exact haB haB'
  have hc1 : c ≠ 1 := by
    intro hc1
    have h3 := (zpowers_mem_omegaA_iff.mp hR.zpowers_mem_omegaA).2.1
    rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  have hcB : c ∉ B := fun hcB => hfree c hcB hc1 hR.zpowers_mem_omegaA
  have hx_cent : ∀ u : ↥Yc, u * x = x * u → u ^ 3 = 1 →
      u ∈ Subgroup.zpowers x ⊔ Subgroup.center ↥Yc := by
    intro u hux hu3
    exact mem_zpowers_sup_center_of_commute hR.mem_partTwoF hBA ha'_memA ha'_notB hx hux hu3
  have hx_conj : ∀ z ∈ Subgroup.center ↥Yc, ∀ g : ↥Yc, g * x * g⁻¹ = x * z → z = 1 := by
    intro z hz g hg
    have hzB : (z : ↥C ⧸ N) ∈ (B.subgroupOf C).map (QuotientGroup.mk' N) := by
      have hzmap : (z : ↥C ⧸ N) ∈ (Subgroup.center ↥Yc).map Yc.subtype := ⟨z, hz, rfl⟩
      rw [hZeq] at hzmap
      exact hzmap.1
    exact eq_one_of_conj_eq_mul hR hW hBA hcB ha'_memA ha'_notB hx hzB hg
  exact ⟨hY4, hZ3, x, hx3, hx_not_center, hx_cent, hx_conj⟩

end Gagen155Y143

end CFSG.RankThree.PartTwo.Sec15
