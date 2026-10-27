module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Close
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofPoint
public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Con

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem res1_not_mem {A : Subgroup G} {c : G} {L : Subgroup G} {Yc : Subgroup (Res1Q A L)}
    (hS : Sec14Std G A c L) (hcomp : Res1Comp A c L Yc) : c ∉ L := by
  intro hcL
  obtain ⟨-, ⟨c', hc'Y, hc'⟩, hbot⟩ := hcomp
  obtain ⟨hcA, hcard, -⟩ := zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcard
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈
      ((A ⊓ L).subgroupOf (Res1C A L)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))) := by
    refine ⟨c', ?_, rfl⟩
    show c' ∈ (A ⊓ L).subgroupOf (Res1C A L)
    rw [Subgroup.mem_subgroupOf]
    have : (c' : G) = c := hc'
    rw [this]
    exact ⟨hcA, hcL⟩
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' = 1 := by
    have h := Subgroup.mem_inf.mpr ⟨hmem, hc'Y⟩
    rw [hbot] at h
    exact h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hord : orderOf c' = 3 := by
    rw [← hc3, ← hc']
    exact (Subgroup.orderOf_coe c').symm
  have hdvd : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Res1C A L)) := by
    have h := orderOf_dvd_natCard (⟨c', h1⟩ : CFSG.pPrimeCore 3 ↥(Res1C A L))
    rwa [Subgroup.orderOf_mk, hord] at h
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card) hdvd

theorem res1_eq_one_of_mem_pPrimeCoreOf (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hhyp : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L) {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G) ⊓ M)
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G))
    (hodd : Odd (orderOf g)) (hgΘ : g ∈ pPrimeCoreOf 3 (Res1C A L)) : g = 1 := by
  have h := hR.toSec14Std
  have h9 := res1_card_inf h hhyp
  have h3L : 3 ∣ Nat.card L :=
    Sec14.three_dvd_card_of_types148
      (hR.chosen136.2 c hR.zpowers_mem_omegaA L hR.mem_lA).1
  have hNL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    Sec14.Res7Point.normalizer_zpowers_le148 hR.toSec14Std hR.zpowers_mem_omegaA hR.mem_lA h3L
  have hWL : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_rfl (hW.trans hNL)).trans Subgroup.inf_normalizer_le_normalizer_inf
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
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := hg.1
  have hbal : ∀ B : Subgroup G, IsHyperplane A B →
      (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
        ⁅CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
          pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
    intro B hBA hfree
    by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))
    · exact Sylow155F1.commutator_le_pPrimeCoreOf_of_isPConstrained h hV3 hAV hBA hcon hgA
    · obtain ⟨rfl, -⟩ := Gagen155Y1.eq_inf_of_not_isPConstrained h1 h2 h43 hin h143 hR hW h9
        hcL hWL hBA hfree hcon
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgk : g ^ k ∈ pPrimeCoreOf 3 (Res1C A L) := Subgroup.zpow_mem _ hgΘ k
      have hxN := le_normalizer_pPrimeCoreOf 3 (Res1C A L) (Subgroup.mem_inf.mp hx).2
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxN _).mp hgk)
        (Subgroup.inv_mem _ hgk)
  have hgV := Sylow155F1.mem_centralizer_of_bal h.isE27 h142
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hAV hgA
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg.2) hgZ hodd hbal
  exact Sylow155F1.eq_one_of_mem_centralizer_pCoreOf h hC hg.2 hgV hodd

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
