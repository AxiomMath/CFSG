module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.H13.GoldschmidtC137Blk
public import CFSG.Quasithin.H13.GoldschmidtC137Bridge
public import CFSG.Quasithin.H13.GoldschmidtC137Concl
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem sl3_card_ne_hat (q : ℕ) (hq : 2 ≤ q) : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ 1080 := by
  rcases le_or_gt q 2 with h | h
  · have : q = 2 := le_antisymm h hq
    subst this
    decide
  · have h1 : 9 ≤ q ^ 2 := by nlinarith
    have h2 : 27 ≤ q ^ 3 := by nlinarith
    have h3 : 8 ≤ q ^ 2 - 1 := by omega
    have h4 : 26 ≤ q ^ 3 - 1 := by omega
    have h5 : 8 * 26 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul h3 h4
    have h6 : 27 * (8 * 26) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h2 h5
    omega

theorem isHatBlock_of_c132 {L : Subgroup G} (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080)
    (h : CFSG.Quasithin.IsG2Block L ∨ CFSG.Quasithin.IsAltBlockType L 6 ∨
      CFSG.Quasithin.IsSp4Block L ∨ CFSG.Quasithin.IsHatA6Block L ∨
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ^ n ∧ CFSG.Quasithin.IsModO2Surj L α) :
    CFSG.Quasithin.IsHatA6Block L := by
  rcases h with hg | ha | hs | hh | ⟨n, F, hF, hFin, α, hcard, hmod⟩
  · exfalso
    have := SBc11.card_of_isPSU_three_three hg.2.1
    omega
  · exfalso
    have h1 := card_of_isAltBlockType ha
    omega
  · exfalso
    obtain ⟨-, F, hF, hFin, hc4, α, hα, hker, -⟩ := hs
    have h1 := card_quot_of_surj α hα hker
    have h2 : Nat.card F = 2 ^ 2 := by
      rw [Nat.card_eq_fintype_card, hc4]
      norm_num
    rw [Vol2.Ch10.SecA.card_Sp4_pow h2] at h1
    omega
  · exact hh
  · exfalso
    have h1 := card_quot_of_surj α hmod.1 hmod.2
    rw [card_statedSL_three1527d] at h1
    have hq : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    exact sl3_card_ne_hat _ hq (by omega)

theorem c124_tail_hat [Finite G] {X L S R₀ : Subgroup G} (hS : S = baum R₀)
    (ht : A6.IsHatA6 L)
    (hcl : (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R₀ ∧ (C.subgroupOf (baum R₀)).Characteristic ∧
        X ≤ normalizer (C : Set G)) ∨ CFSG.Quasithin.IsChiBlock X L ∨
      (CFSG.QuasithinUnique.IsBlock2 X L ∧ (CFSG.Quasithin.IsExcA7Block L ∨
        CFSG.Quasithin.IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L))) :
    CharNormal S X ∨ BlockPart L := by
  rcases hcl with ⟨C, hC1, hC2, hC3, hC4⟩ | hchi | ⟨-, hA7 | hA6 | hH⟩
  · left
    rw [hS]
    exact ⟨C, hC2, hC1, hC3, hC4⟩
  · exact (not_isChiBlock_of_card hchi (Or.inr (card_of_hatA6 ht))).elim
  · exact (not_isExcA7Block_of_card hA7 (Or.inr (card_of_hatA6 ht))).elim
  · have h1 := card_of_isAltBlockType hA6
    rw [card_of_hatA6 ht] at h1
    omega
  · exact Or.inr (blockPart_of_hatA6 ht (isHatA6Block_of hH))

end CFSG.Quasithin.H13.U3.GC137
