module

public import CFSG.Quasithin.H13.GoldschmidtC137Blk
public import CFSG.Quasithin.H13.GoldschmidtC137Concl
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem sl3_card_ne (q : ℕ) (hq : 2 ≤ q) : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ 360 := by
  rcases le_or_gt q 3 with h | h
  · interval_cases q <;> decide
  · have h1 : 16 ≤ q ^ 2 := by nlinarith
    have h2 : 64 ≤ q ^ 3 := by nlinarith
    have h3 : 15 ≤ q ^ 2 - 1 := by omega
    have h4 : 63 ≤ q ^ 3 - 1 := by omega
    have h5 : 15 * 63 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul h3 h4
    have h6 : 64 * (15 * 63) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h2 h5
    omega

theorem isAltBlock_of_c132 {L : Subgroup G} (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360)
    (h : CFSG.Quasithin.IsG2Block L ∨ CFSG.Quasithin.IsAltBlockType L 6 ∨
      CFSG.Quasithin.IsSp4Block L ∨ CFSG.Quasithin.IsHatA6Block L ∨
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ^ n ∧ CFSG.Quasithin.IsModO2Surj L α) :
    CFSG.Quasithin.IsAltBlockType L 6 := by
  rcases h with hg | ha | hs | hh | ⟨n, F, hF, hFin, α, hcard, hmod⟩
  · exfalso
    have := SBc11.card_of_isPSU_three_three hg.2.1
    omega
  · exact ha
  · exfalso
    obtain ⟨-, F, hF, hFin, hc4, α, hα, hker, -⟩ := hs
    have h1 := card_quot_of_surj α hα hker
    have h2 : Nat.card F = 2 ^ 2 := by
      rw [Nat.card_eq_fintype_card, hc4]
      norm_num
    rw [Vol2.Ch10.SecA.card_Sp4_pow h2] at h1
    omega
  · exfalso
    have h1 : A6.IsHatA6 L := ⟨hh.2.1.1.1, hh.2.1.2.1, hh.2.1.2.2⟩
    have := card_of_hatA6 h1
    omega
  · exfalso
    have h1 := card_quot_of_surj α hmod.1 hmod.2
    rw [card_statedSL_three1527d] at h1
    have hq : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    exact sl3_card_ne _ hq (by omega)

end CFSG.Quasithin.H13.U3.GC137
