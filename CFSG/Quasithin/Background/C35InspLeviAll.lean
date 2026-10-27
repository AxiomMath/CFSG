module

public import CFSG.Quasithin.Background.C35InspLeviL3
public import CFSG.Quasithin.Background.C35InspLeviSp4
public import CFSG.Quasithin.Background.C35InspLeviG2
public import CFSG.Quasithin.Background.C35InspLeviD4
public import CFSG.Quasithin.Background.C35InspLeviF4
public import CFSG.Quasithin.Background.C35InspLeviL45
public import CFSG.Quasithin.Background.KGSchurMult2Pf

public section

namespace CFSG.Quasithin.C35Levi

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C35Pf

theorem levi_holds :
    ∀ (A : Type) [Group A] [Finite A] (K Y : Subgroup A), CFSG.Open.IsQuasisimple ↥K →
      IsPGroup 2 ↥(centerOf K) →
      (IsAlt 5 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 6 (↥K ⧸ Subgroup.center ↥K) ∨
        IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
        ((∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (1 ≤ f ∧ IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (2 ≤ f ∧ IsPSU 3 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (2 ≤ f ∧ IsPSp4 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (2 ≤ f ∧ IsG2 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (1 ≤ f ∧ Is3D4 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (Odd f ∧ 3 ≤ f ∧ Is2F4 f (↥K ⧸ Subgroup.center ↥K)) ∨
            (Odd f ∧ 3 ≤ f ∧ IsSz f (↥K ⧸ Subgroup.center ↥K))) ∨
          IsTits (↥K ⧸ Subgroup.center ↥K)) ∨
        ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 (↥K ⧸ Subgroup.center ↥K)) →
      IsParabolic2 K Y → Y ≠ K → perfectCore Y ≠ ⊥ →
      CharTwo (perfectCore Y) ∧
        ((∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m (ModO2 (perfectCore Y))) ∨
          (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m (ModO2 (perfectCore Y))) ∨
          IsPSL 3 2 1 (ModO2 (perfectCore Y)) ∨ IsPSL 4 2 1 (ModO2 (perfectCore Y))) ∧
        (IsPSL 4 2 1 (ModO2 (perfectCore Y)) →
          IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K) ∧ IsMaxParabolic2 K Y ∧
            ∀ g ∈ Subgroup.normalizer (K : Set A) ⊓ Subgroup.normalizer (Y : Set A),
              ∃ k ∈ K, ∀ x ∈ K, (g * x * g⁻¹)⁻¹ * (k * x * k⁻¹) ∈ centerOf K) := by
  intro A _ _ K Y hq hZ hfam hpar hne hX0
  show LeviConcl K Y
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hsolv : SolvOver (↥K ⧸ Subgroup.center ↥K) → False := false_of_solvOver hZ hpar hne hX0
  rcases hfam with h5 | h6 | h8 | (⟨f, ⟨hf, h2⟩ | ⟨hf, h3⟩ | ⟨hf, hu⟩ | ⟨hf, hsp⟩ | ⟨hf, hg⟩ |
      ⟨-, hd⟩ | ⟨-, -, hf4⟩ | ⟨-, -, hsz⟩⟩ | htits) | ⟨n, hn, hpsl⟩
  · obtain ⟨e⟩ := h5
    refine (hsolv (solvOver_of_card60 ?_)).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · obtain ⟨e⟩ := h6
    refine (hsolv (solvOver_of_card360 ?_)).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · exact levi_l45 hq hZ schurMult2L52_holds (Or.inl h8) hpar hne hX0
  · exact (hsolv (solvOver_of_isPSL2 (by omega) h2)).elim
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact (hsolv (solvOver_of_card168
        ((C48Pf.FMod.card_of_isPSL_two_one (Or.inl rfl) h3).1 rfl))).elim
    · exact levi_l3 hZ hf2 h3 hpar hne hX0
  · exact (hsolv (solvOver_of_isPSU3 hf hu)).elim
  · exact levi_sp4 hZ hf hsp hpar hne hX0
  · exact levi_g2 hZ hf hg hpar hne hX0
  · exact levi_d4 hZ hd hpar hne hX0
  · exact levi_f4 hZ hf4 hpar hne hX0
  · exact (hsolv (solvOver_of_isSz hsz)).elim
  · exact (hsolv (solvOver_of_isTits htits)).elim
  · exact levi_l45 hq hZ schurMult2L52_holds (Or.inr ⟨n, hn, hpsl⟩) hpar hne hX0

end CFSG.Quasithin.C35Levi
