module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15A318
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def Core3BigExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Core3IsLieBig X → A318Exclusion X

@[expose] def Core3BigParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      Core3IsLieBig (↥L ⧸ CFSG.pCore 2 ↥L) → L = oPrimeResidualOf 3 (S1421.g0Of T M H K1) →
        ∀ y : G, y ∈ yOfL22 T M ⊓ L →
          ∃ P : Subgroup G, P < L ∧ K1 ≤ P ∧ y ∈ P ∧ S1421.sOf T K1 ⊓ L ≤ P ∧
            S1421.sOf T K1 ≤ Subgroup.normalizer (P : Set G)

theorem core3QuasiBig_of_parts (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hex : Core3BigExclusion) (hp : Core3BigParabolic) : Core3QuasiBig := by
  intro G _ _ T M H K1 L M₁ c hq hbig
  have hL : L = oPrimeResidualOf 3 (S1421.g0Of T M H K1) :=
    c.eq_oPrimeResidualOf hF h36 h38 hq (MulEquiv.refl _) (hex _ hbig)
  obtain ⟨y, hyY, hyL, -, -, hYle⟩ := c.exists_threeElement_mem hL
  obtain ⟨P, hPL, hK1P, hyP, hSP, hSN⟩ := hp G T M H K1 L M₁ c hq hbig hL y ⟨hyY, hyL⟩
  exact c.false_of_proper_overgroup hYle hPL hK1P hyP hSP hSN

end CFSG.Quasithin
