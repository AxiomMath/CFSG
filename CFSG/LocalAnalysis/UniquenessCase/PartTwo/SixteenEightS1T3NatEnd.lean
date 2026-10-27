module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

theorem SumOfNatShape.exists_summand {k : ℕ} (h : SumOfNatShape L U Z k) (i : Fin k) :
    ∃ I : Subgroup W, Z ≤ I ∧ I ≤ U ∧ SumOfNatShape L I Z 1 := by
  obtain ⟨n, hcases⟩ := h
  rcases hcases with ⟨hSL, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOP, hsum⟩ | ⟨hOM, hsum⟩ | ⟨hAlt, hsum⟩
  · obtain ⟨I, hZI, hIU, hsum'⟩ := s16t3_sumOfNat_summand hsum i
    exact ⟨I, hZI, hIU, n, Or.inl ⟨hSL, hsum'⟩⟩
  · obtain ⟨I, hZI, hIU, hsum'⟩ := s16t3_sumOfNat_summand hsum i
    exact ⟨I, hZI, hIU, n, Or.inr (Or.inl ⟨hSp, hsum'⟩)⟩
  · obtain ⟨I, hZI, hIU, hsum'⟩ := s16t3_sumOfNat_summand hsum i
    exact ⟨I, hZI, hIU, n, Or.inr (Or.inr (Or.inl ⟨hOP, hsum'⟩))⟩
  · obtain ⟨I, hZI, hIU, hsum'⟩ := s16t3_sumOfNat_summand hsum i
    exact ⟨I, hZI, hIU, n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOM, hsum'⟩)))⟩
  · obtain ⟨I, hZI, hIU, hsum'⟩ := s16t3_sumOfNat_summand hsum i
    exact ⟨I, hZI, hIU, n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAlt, hsum'⟩)))⟩

theorem SumOfNatShape.eq_of_equivariant (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : SumOfNatShape L U Z 1) (φ : ↥U ≃* ↥U)
    (hZ : ∀ u : ↥U, ((φ u : ↥U) : W) ∈ Z ↔ (u : W) ∈ Z)
    (hφ : ∀ l ∈ L, ∀ u : ↥U, ∀ hu : l (u : W) ∈ U,
      ((φ ⟨l (u : W), hu⟩ : ↥U) : W) * (l ((φ u : ↥U) : W))⁻¹ ∈ Z) :
    ∀ u : ↥U, ((φ u : ↥U) : W) * (u : W)⁻¹ ∈ Z := by
  exact s16t3_eq_of_equivariant hq h φ hZ hφ

theorem SumOfNatShape.restrict {I : Subgroup W} (h : SumOfNatShape L U Z 1) (hIU : I ≤ U)
    (hI : StableUnder L I) (hIZ : I ⊔ Z = U) : SumOfNatShape L I (I ⊓ Z) 1 := by
  obtain ⟨n, hcases⟩ := h
  rcases hcases with ⟨hSL, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOP, hsum⟩ | ⟨hOM, hsum⟩ | ⟨hAlt, hsum⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    exact ⟨n, Or.inl ⟨hSL, s16t3_sumOfNat_singleton inf_le_left
      (s16t3_restrict_binaryNaturalSL hN hIU hI hIZ)⟩⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    exact ⟨n, Or.inr (Or.inl ⟨hSp, s16t3_sumOfNat_singleton inf_le_left
      (s16t3_restrict_natSpn hN hIU hI hIZ)⟩)⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    exact ⟨n, Or.inr (Or.inr (Or.inl ⟨hOP, s16t3_sumOfNat_singleton inf_le_left
      (s16t3_restrict_natOmegaPlus hN hIU hI hIZ)⟩))⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOM, s16t3_sumOfNat_singleton inf_le_left
      (s16t3_restrict_natOmegaMinus hN hIU hI hIZ)⟩)))⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAlt, s16t3_sumOfNat_singleton inf_le_left
      (s16t3_restrict_alternatingNatural hN hIU hI hIZ)⟩)))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
