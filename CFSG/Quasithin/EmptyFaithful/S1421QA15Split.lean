module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15R

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def Core3IsLieBig (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)

@[expose] def Core3IsSmall (X : Type) [Group X] : Prop :=
  ChevalleyExceptionalModel X .trialityD4 2 1 ∨
  (∃ s : TauCeti.SporadicName, (s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .Ru) ∧
    Nonempty (X ≃* NativeSporadic.Carrier s))

@[expose] def Core3QuasiList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      Core3IsLieBig (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Core3IsSmall (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Core3QuasiBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      Core3IsLieBig (↥L ⧸ CFSG.pCore 2 ↥L) → False

@[expose] def Core3QuasiSmallLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      Core3IsSmall (↥L ⧸ CFSG.pCore 2 ↥L) → oTwoUpper H ≤ L

@[expose] def Core3QuasiSmallU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      Core3IsSmall (↥L ⧸ CFSG.pCore 2 ↥L) → oTwoUpper H ≤ L → False

theorem core3Quasi_of_list (hl : Core3QuasiList) (hb : Core3QuasiBig) (h1 : Core3QuasiSmallLe)
    (h2 : Core3QuasiSmallU) : Core3Quasi :=
  fun G _ _ T M H K1 L M₁ c hq => by
    rcases hl G T M H K1 L M₁ c hq with hbig | hsmall
    · exact hb G T M H K1 L M₁ c hq hbig
    · exact h2 G T M H K1 L M₁ c hq hsmall (h1 G T M H K1 L M₁ c hq hsmall)

@[expose] def Core3HeOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → False

@[expose] def Core3HeYnot : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ¬ yOfL22 T M ≤ L → False

@[expose] def Core3HeYin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → yOfL22 T M ≤ L → False

@[expose] def Core3HeSyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → yOfL22 T M ≤ L →
        IsSylowTwoOf (S1421.rOf T M K1 ⊓ L) L

theorem core3He_of_cases (ho : Core3HeOdd) (hn : Core3HeYnot) (hy : Core3HeYin) : Core3He := by
  intro G _ _ T M H K1 L M₁ c _ hc
  by_cases hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  · by_cases hY : yOfL22 T M ≤ L
    · exact hy G T M H K1 L M₁ c hc hq hY
    · exact hn G T M H K1 L M₁ c hc hq hY
  · exact ho G T M H K1 L M₁ c hc hq

end CFSG.Quasithin
