module

public import CFSG.RankThree.PartOne.S11c.E8CharThree
public import CFSG.RankThree.Chevalley.SteinbergCFOddE6E7RootInverters

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.Assembly.RankThreeEven

theorem isInverterData_of_isEvenFourRootData {τ : Tag} {K : Type} [Field K]
    {α : Fin 4 → Fin τ.rank → ℤ} {β : Fin τ.rank → ℤ} (h : IsEvenFourRootData τ K α β) :
    IsInverterData (adjointGroup τ K) 3 (fun i => evenH τ K (α i))
      (fun i => pinnedX τ K (α i) 1) (pinnedX τ K β 1) := by
  obtain ⟨-, -, hh, hcomm, hw, hinv, hfix, hz, hz2, hzh⟩ := h
  exact ⟨hh, hcomm, fun i => (hw i).1, hinv, hfix, hz, hz2, hzh⟩

theorem isInverterData_of_isFourRootInverterData {τ : Tag} {K : Type} [Field K] {ℓ : ℕ}
    {α : Fin 4 → Fin τ.rank → ℤ} {j : Fin 4 → Fin τ.rank} {t s : Fin τ.rank}
    (h : IsFourRootInverterData τ K ℓ α j t s) :
    IsInverterData (adjointGroup τ K) ℓ (fun i => pinnedX τ K (α i) 1)
      (fun i => torusElt τ K (j i) (-1)) (torusElt τ K t (-1)) := by
  obtain ⟨-, hh, hcomm, hw, hinv, hfix, hz, hz2, hzh, -⟩ := h
  exact ⟨hh, fun i i' => hcomm i i', fun i => (hw i).1, hinv, hfix, hz, hz2,
    fun i => mul_inv_eq_iff_eq_mul.1 (hzh i)⟩

theorem E6_E7_model_actual_central_cover_odd_rank_four {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {ℓ f : ℕ} {τ : StatedLieTag} (hτ : τ = .E6 ∨ τ = .E7)
    (hcase : τ = .E7 ∨ ℓ ≠ 2) (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) τ ℓ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ (ℓ = 2 → r = 3) ∧ (ℓ ≠ 2 → r = ℓ) ∧ FourRankWitness X Y r ∧
      4 ≤ localRank r X ∧ 4 ≤ CFSG.twoLocalOddRank X := by
  have hℓ : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  have key : ∀ t : Tag, (t = .E6 ∨ t = .E7) → (t = .E7 ∨ ℓ ≠ 2) →
      UntwistedChevalleyModel (Y ⧸ Subgroup.center Y) t (ℓ ^ f) →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ (ℓ = 2 → r = 3) ∧ (ℓ ≠ 2 → r = ℓ) ∧ FourRankWitness X Y r ∧
        4 ≤ localRank r X ∧ 4 ≤ CFSG.twoLocalOddRank X := by
    intro t ht hc hm
    obtain ⟨K, _, _, hK, φ, hφ, hker⟩ := exists_surj_adjointGroup_of_model hm
    have hchar : CharP K ℓ := ringChar.of_eq (ringChar_eq_of_card hℓ hf hK)
    have : Fact ℓ.Prime := ⟨hℓ⟩
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have ht7 : t = .E7 := hc.resolve_right (by simp)
      subst ht7
      have hd := isInverterData_of_isEvenFourRootData
        (even_E7_four_three_elements_with_inverters_and_centralizing_involution K)
      exact ⟨3, Nat.prime_three, by norm_num, fun _ => rfl, fun h => absurd rfl h,
        fourRankPackage_of_inverterData Y φ hφ hker.le Nat.prime_three (by norm_num) hd⟩
    · obtain ⟨hE6, hE7⟩ := odd_E6_E7_four_commuting_root_elements_with_inverters hℓ2 K
      rcases ht with rfl | rfl
      · exact ⟨ℓ, hℓ, hℓ2, fun h => absurd h hℓ2, fun _ => rfl,
          fourRankPackage_of_inverterData Y φ hφ hker.le hℓ hℓ2
            (isInverterData_of_isFourRootInverterData hE6)⟩
      · exact ⟨ℓ, hℓ, hℓ2, fun h => absurd h hℓ2, fun _ => rfl,
          fourRankPackage_of_inverterData Y φ hφ hker.le hℓ hℓ2
            (isInverterData_of_isFourRootInverterData hE7)⟩
  rcases hτ with rfl | rfl
  · exact key .E6 (Or.inl rfl) (Or.inr (hcase.resolve_left (by decide))) hmod.2
  · exact key .E7 (Or.inr rfl) (Or.inl rfl) hmod.2

theorem E8_small_field_actual_central_cover_three_rank_four {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {ℓ f : ℕ} (hℓ : ℓ = 2 ∨ ℓ = 3)
    (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .E8 ℓ f) :
    FourRankWitness X Y 3 ∧ 4 ≤ localRank 3 X ∧ 4 ≤ CFSG.twoLocalOddRank X := by
  have hℓp : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨K, _, _, hK, φ, hφ, hker⟩ := exists_surj_adjointGroup_of_model hmod.2
  have hchar : CharP K ℓ := ringChar.of_eq (ringChar_eq_of_card hℓp hf hK)
  rcases hℓ with rfl | rfl
  · exact fourRankPackage_of_inverterData Y φ hφ hker.le Nat.prime_three (by norm_num)
      (isInverterData_of_isEvenFourRootData
        (even_E8_four_three_elements_with_inverters_and_centralizing_involution K))
  · exact fourRankPackage_of_inverterData Y φ hφ hker.le Nat.prime_three (by norm_num)
      (isInverterData_E8_charThree K)

end CFSG.RankThree.PartOne
