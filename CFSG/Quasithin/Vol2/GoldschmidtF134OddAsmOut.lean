module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Ch1 CFSG.RankThree.PartTwo.Sec4

variable {A : Type} [Group A] {p : ℕ} [Fact p.Prime] {L P T : Subgroup A}

theorem oddOutcome_of_psp4
    [Finite A] (hq : CFSG.IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) {n : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 n)
    (hout : Nat.card P = p ^ 2 ∧ Even n ∧ p ∣ 2 ^ n - 1 ∧
      CFSG.Quasithin.EmptyFaithfulMultiple.AutCyclic T P) : OddOutcome p L P T := by
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rcases hZ with h1 | h3
    · rw [h1]; decide
    · rw [h3]; decide
  have : Finite ↥L := inferInstance
  obtain ⟨hbot, -⟩ := CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hq hodd h
  have e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨hout.1, Or.inr ⟨n, hout.2.1, hout.2.2.1, isoInvariant_stated .PSp 2 2 n _ _ e h,
    hout.2.2.2⟩⟩

theorem oddOutcome_of_psl3 [Finite A] (hq : CFSG.IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) (hp2 : p ≠ 2)
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1) (hP : Nat.card P = p ^ 2) :
    OddOutcome p L P T := by
  refine ⟨hP, Or.inl ?_⟩
  rcases hZ with h1 | h3
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.card_eq_one.mp h1
    have e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact Or.inl (isoInvariant_stated .PSL 3 p 1 _ _ e h)
  · right
    have : Group.IsPerfect ↥L := hq.1
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have hF' : Nat.card F = p := by rw [hF, pow_one]
    obtain ⟨-, ⟨iso⟩⟩ := triple_cover_linear (p := p) (f := 1) h3 hF e
      fun E _ _ π hπ hC hodd => by
        obtain ⟨⟨s, hs, -⟩, -⟩ :=
          CFSG.SectionRank.OddCover.prime_classical_three_central_odd_extension_splitting
            (Fact.out : p.Prime) hp2 (Or.inl ⟨rfl, hF', rfl⟩) π hπ hC hodd
        exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    have := Fintype.ofFinite F
    let ψ : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq
      (by rw [← Nat.card_eq_fintype_card, hF', ← Nat.card_eq_fintype_card, Nat.card_zmod])
    exact ⟨iso.trans (((statedSLEquiv 3 F).trans
      (CFSG.ClassicalModels.specialLinearFieldEquiv ψ (Fin 3))).trans
      (statedSLEquiv 3 (ZMod p)).symm)⟩

end CFSG.Quasithin.H13.NQCore
