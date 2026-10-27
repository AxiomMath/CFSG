module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L3Rank
public import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)

theorem three_le_twoRank_of_isoLThreePi {S : Type} [Group S]
    [Finite S] {n : ℕ} (hn : 1 ≤ n) (h : IsoLThreePi S 2 (3 * n)) : 3 ≤ CFSG.Open.twoRank S := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  ·
    have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 (3 * n) :=
      ⟨Fact.out, by omega, by norm_num, fun hh => absurd (Prod.mk.inj hh).1 (by norm_num),
        fun hh => absurd (Prod.mk.inj hh).1 (by norm_num)⟩
    have hL : CFSG.Blueprint.LieModel S .PSL 3 2 (3 * n) :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ⟩
    have h3 := CFSG.EvenSporadicStandard.Induction.three_le_pRank_psl_three (by omega) hL
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h3
    exact h3
  ·
    have hT := CFSG.RankThree.PartTwo.Sec4.HeringUnitary.twoRank_projSU_three_two (m := 3 * n)
      (by omega)
    have hS := CFSG.EvenSporadicStandard.Induction.pRank_two_eq_of_mulEquiv' φ
    have key : CFSG.Open.twoRank S = CFSG.Open.twoRank ↥(CFSG.PGLModel.projSU 3 2 (3 * n)) :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 S).symm.trans
        (hS.trans (CFSG.SectionRank.pRank_eq_open_pRank_top 2 _))
    rw [key, hT]
    omega

theorem twoRank_le_two_of_unitaryPSU {S : Type} [Group S] [Finite S] {p f : ℕ} {F : Type}
    [Field F] (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (e : S ≃* unitaryPSU h 3) :
    CFSG.Open.twoRank S ≤ 2 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Finite F := h.finite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField p (2 * f)) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField p (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h.card,
      GaloisField.card p (2 * f) (by have := h.one_le; omega)]
  let ι : F ≃+* GaloisField p (2 * f) := FiniteField.ringEquivOfCardEq hcard
  let φ := e.trans ((unitaryPSUEquiv h (n := 3) (by norm_num)).trans
    ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv ι 3 (p ^ f)).trans
      (CFSG.RankThree.PartTwo.KFacts.KS21LocalRank.statedProjSUEquivProjSU 3 p f)))
  exact CFSG.RankThree.PartTwo.Sec4.HeringUnitary.twoRank_le_two_of_projSU_three hp2 h.one_le φ

theorem eq_two_of_isoLThreePi_of_unitaryPSU {S : Type} [Group S]
    [Finite S] {n : ℕ} (hn : 1 ≤ n) (hS : IsoLThreePi S 2 (3 * n)) {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (e : S ≃* unitaryPSU h 3) : p = 2 := by
  by_contra hp2
  have h1 := three_le_twoRank_of_isoLThreePi hn hS
  have h2 := twoRank_le_two_of_unitaryPSU h hp2 e
  omega

end CFSG.RankThree.PartTwo.Sec4.RonanK429
