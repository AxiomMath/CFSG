module

import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Con
import CFSG.RankThree.PartTwo.Sec15.Sylow155E0
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y1

theorem layerOddPreimage_le_of_balComp {A L : Subgroup G} {c : G}
    (h142 : Concl142 A (lB A)) (h1444 : Item1444 A (lB A)) (h : Sec14Std G A c L)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hbal : ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
      g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
        Odd (orderOf g) →
        ∀ B : Subgroup G, IsHyperplane A B → (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
          ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G)) →
          ⁅CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
            pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) :
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K := by
  have hF : ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
      g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
        Odd (orderOf g) → g = 1 := by
    intro g hg hgZ hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
    have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    have hV3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 M) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
      rw [hk]
      intro h3
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
    have hbal' : ∀ B : Subgroup G, IsHyperplane A B →
        (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
          ⁅CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
            pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
      intro B hBA hfree
      by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))
      · exact Sylow155F1.commutator_le_pPrimeCoreOf_of_isPConstrained h hV3 hAV hBA hcon
          (pPrimeCoreOf_le 3 _ hg.1)
      · exact hbal g hg hgZ hodd B hBA hfree hcon
    have hgV := Sylow155F1.mem_centralizer_of_bal h.isE27 h142
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hAV (pPrimeCoreOf_le 3 _ hg.1)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg.2) hgZ hodd hbal'
    exact Sylow155F1.eq_one_of_mem_centralizer_pCoreOf h hC hg.2 hgV hodd
  exact (Sylow155E0.layerOddPreimage_eq_bot_of_isCharacteristicP
    (Sylow155F1.isCharacteristicP_delta_sup_of_f1Zero h h146 h1444 hC hE hRP hIX
      hF)).le.trans bot_le

end Gagen155Y1

end CFSG.RankThree.PartTwo.Sec15
