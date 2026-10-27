module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumIn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16k_nat_of_sum_one {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hZ : Z ≤ U) {n : ℕ}
    (hfam : (IsSLn ↥L n 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L U Z 1) ∨
      (IsSpn ↥L n 1 ∧ SumOfNat (fun H U Z => NatSpn H U Z n 1) L U Z 1) ∨
      (IsOmegaPlus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L U Z 1) ∨
      (IsOmegaMinus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L U Z 1) ∨
      (IsAlt ↥L n ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z 1)) :
    (∃ n : ℕ, (IsSLn ↥L n 1 ∧ BinaryNaturalSL L U Z n 1) ∨ (IsSpn ↥L n 1 ∧ NatSpn L U Z n 1) ∨
      (IsOmegaPlus ↥L n 1 ∧ NatOmegaPlus L U Z n 1) ∨
      (IsOmegaMinus ↥L n 1 ∧ NatOmegaMinus L U Z n 1) ∨ (IsSUn ↥L n 1 ∧ NatSUn L U Z n 1)) ∨
    (∃ n : ℕ, IsAlt ↥L n ∧ AlternatingNatural L U Z n) := by
  rcases hfam with ⟨hL, hS⟩ | ⟨hL, hS⟩ | ⟨hL, hS⟩ | ⟨hL, hS⟩ | ⟨hL, hS⟩
  · exact Or.inl ⟨n, Or.inl ⟨hL, s16k_sumOfNat_one hZ hS⟩⟩
  · exact Or.inl ⟨n, Or.inr (Or.inl ⟨hL, s16k_sumOfNat_one hZ hS⟩)⟩
  · exact Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨hL, s16k_sumOfNat_one hZ hS⟩))⟩
  · exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, s16k_sumOfNat_one hZ hS⟩)))⟩
  · exact Or.inr ⟨n, hL, s16k_sumOfNat_one hZ hS⟩

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_concl163_of_sum_two (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hOut : S16kOmega8OutInner)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ}
    (hfam :
      (IsSLn ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => NatSpn H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) ∨
      (IsAlt ↥(lBar V₀ V hV L) n ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2)) :
    Concl163 D V₀ V hV L := by
  refine Or.inl (Or.inr (Or.inr (Or.inl ?_)))
  rcases hfam with ⟨hSL, hS⟩ | ⟨hSp, hS⟩ | ⟨hΩ, hS⟩ | ⟨hΩ, hS⟩ | ⟨hA, hS⟩
  · have h3 := s16k_three_le_of_isSLn hq hSL
    by_cases h5 : n ≤ 5
    · exact s16k_case162_2_of_sl h h3 h5 hSL hS
    · exact (s16k_false_of_sum_two_sl h hGA hSchur hq (by omega) hSL hS).elim
  · have h6 := s16k_six_le_of_isSpn hq hSp
    obtain ⟨r, hr⟩ := hSp.1
    by_cases h6' : n = 6
    · subst h6'
      exact s16k_case162_2_of_sp_six h hSp hS
    · exact (s16k_false_of_sum_two_sp h hGA hSchur hq (by omega) hSp hS).elim
  · have h6 := s16k_six_le_of_isOmegaPlus hq hΩ
    obtain ⟨r, hr⟩ := hΩ.1
    by_cases h6' : n = 6
    · subst h6'
      exact s16k_case162_2_of_omegaPlus_six h hΩ hS
    · exact (s16k_false_of_sum_two_omegaPlus h hGA hSchur hOut hq (by omega) hΩ hS).elim
  · have h4 := s16k_four_le_of_isOmegaMinus hq hΩ
    obtain ⟨r, hr⟩ := hΩ.1
    rcases (by omega : n = 4 ∨ n = 6 ∨ n = 8 ∨ 10 ≤ n) with rfl | rfl | rfl | h10
    · exact s16k_case162_2_of_omegaMinus_four h hΩ hS
    · exact s16k_case162_2_of_omegaMinus_six h hΩ hS
    · exact s16k_case162_2_of_omegaMinus_eight h hΩ hS
    · exact (s16k_false_of_sum_two_omegaMinus h hGA hSchur hq h10 hΩ hS).elim
  · have h5 := s16k_five_le_of_isAlt hq hA
    by_cases h11 : n ≤ 11
    · exact s16k_case162_2_of_alt h h5 h11 hA hS
    · exact (s16k_false_of_sum_two_alt h hGA hSchur hq (by omega) hA hS).elim

theorem s16k_concl163_of_sum (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hOut : S16kOmega8OutInner)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfAtMostThreeNat (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ normalizer
          ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom) :
    Concl163 D V₀ V hV L := by
  obtain ⟨k, hk, n, hfam⟩ := hsum
  interval_cases k
  · exfalso
    have hUZ : commSub ⊤ (lBar V₀ V hV L) =
        commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
      rcases hfam with ⟨-, hS⟩ | ⟨-, hS⟩ | ⟨-, hS⟩ | ⟨-, hS⟩ | ⟨-, hS⟩ <;>
        exact s16k_sumOfNat_zero hS
    rw [h.comm_top, top_inf_eq] at hUZ
    exact h.ne (CFSG.Quasithin.B1.eq_bot_of_fixV_eq_top hUZ.symm)
  · exact (s16k_false_of_irr_nat h hGA hcomp.2.2 (s16k_nat_of_sum_one inf_le_left hfam)).elim
  · exact s16k_concl163_of_sum_two h hGA hSchur hOut hcomp.2.2 hfam
  · exact (s16k_false_of_sum_three h hGA hSchur hcomp.2.2 hfam htrans).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
