module

public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step202O2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    ∀ X ∈ scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G),
      CFSG.Open.pCoreOf 2 (X ⊓ M) = CFSG.Open.pCoreOf 2 X

@[expose] def Step202J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    ∀ X ∈ scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G), X ≠ M →
      CFSG.Open.pCoreOf 2 (X ⊓ M) = CFSG.Open.pCoreOf 2 X →
        ∃ K₀ ∈ oTwoComponentsIn M, 3 ∣ Nat.card K₀ ∧ ¬ K₀ ≤ X

@[expose] def Step202Unique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    ∀ K₀ ∈ oTwoComponentsIn M, 3 ∣ Nat.card K₀ → K₀ = kTwenty M c

theorem item202One_of_steps (h1 : Step202O2) (h2 : Step202J) (h3 : Step202Unique) :
    Item202One := by
  intro G _ _ A M L N c h
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 h.1
  have hAM : A ≤ M := le_of_hyp201 h.1
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨h.1.mem_scriptM.1, ?_⟩, ?_⟩
  · intro x hx
    exact sup_le hAM hKM hx
  · intro X hX
    by_contra hXM
    obtain ⟨K₀, hK₀, h3dvd, hK₀X⟩ := h2 G A M L N c h X hX hXM (h1 G A M L N c h X hX)
    rw [h3 G A M L N c h K₀ hK₀ h3dvd] at hK₀X
    exact hK₀X fun k hk => hX.2 (Subgroup.mem_sup_right hk)

@[expose] def Step204FinalCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        ∀ k : Fin 4, (k = i ∨ k = j) → CoveredByNormalizer M X T c k → False

@[expose] def Step204FinalL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) → False

theorem step204Final_of_cases (hcov : Step204FinalCover) (hL2 : Step204FinalL2) :
    Step204Final := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm h
  rcases h with hi | hj | hL
  · exact hcov G A M L N c T i j P hset X hX hXM hm i (Or.inl rfl) hi
  · exact hcov G A M L N c T i j P hset X hX hXM hm j (Or.inr rfl) hj
  · exact hL2 G A M L N c T i j P hset X hX hXM hm hL

end CFSG.RankThree.PartTwo.Sec20
