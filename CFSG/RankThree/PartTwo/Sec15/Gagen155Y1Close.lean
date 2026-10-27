module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Comp
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Refl
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Cor74
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y1

theorem eq_inf_of_not_isPConstrained (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L)
    (hWL : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    {B : Subgroup G} (hBA : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))) :
    B = A ⊓ L ∧ ∃ Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))),
      CFSG.IsComponent Yc ∧
      c ∈ (Yc.comap (QuotientGroup.mk'
        (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
          (Subgroup.centralizer (B : Set G)).subtype ∧
      (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ⊓ Yc = ⊥ := by
  have hcB : c ∉ B := fun hcB => hfree c hcB hR.ne_one hR.zpowers_mem_omegaA
  obtain ⟨Yc, hYc, a, haA, haB, haY⟩ :=
    exists_component_mem_not_mem h1 h2 h43 hin hR.toSec14Std.toTheoremFourHyp hR.partTwoS_eq
      hR.mem_partTwoF hBA hR.mem_A hcB hW hcon
  have hBY := h143 G A c L hR hW B hBA hfree Yc hYc ⟨a, haA, haB, haY⟩
  obtain ⟨s, hsA, hsB, hsa⟩ :=
    exists_reflection hR.mem_partTwoF hBA hYc haA haB haY hBY
  have hca : c ∈ Subgroup.zpowers a :=
    mem_zpowers_of_conj_eq_inv hR.mem_partTwoF.1 hBA haA haB hR.mem_A hcB hsB hsa (hW hsA)
  have hcY : c ∈ (Yc.comap (QuotientGroup.mk'
      (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
        (Subgroup.centralizer (B : Set G)).subtype :=
    (Subgroup.zpowers_le.mpr haY) hca
  have hsc : s * c * s⁻¹ = c⁻¹ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hca
    rw [← conj_zpow, hsa, inv_zpow]
  have hAL : IsHyperplane A (A ⊓ L) :=
    ⟨inf_le_left, by rw [hR.card_eq, h9]⟩
  have hcAL : c ∉ A ⊓ L := fun h => hcL (Subgroup.mem_inf.mp h).2
  have hBeq : B = A ⊓ L :=
    eq_of_conj_eq_inv hR.mem_partTwoF.1 hBA hAL hR.mem_A hcB hcAL hsB hsc (hWL hsA)
  subst hBeq
  exact ⟨rfl, Yc, hYc, hcY, hBY⟩

end Gagen155Y1

end CFSG.RankThree.PartTwo.Sec15
