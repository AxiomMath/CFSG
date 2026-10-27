
module

public import CFSG.Quasithin.Background.C4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def InspC33 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], A38Types Y →
    ∀ M V : Subgroup Y, ⁅M, M⁆ = M → V ≤ M → IsElemAbelian 2 V → ⁅V, M⁆ = V → V = ⊥

@[expose] def InspC31SporadicAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (S M₀ R M V : Subgroup A),
    S.Normal → IsSporadic s ↥S → Subgroup.centralizer (S : Set A) = ⊥ →
    M₀ ≤ S → ⁅M₀, M₀⁆ = M₀ → M₀ ≠ ⊥ → (∃ L ∈ cComp M, M₀ = conjClosure L M) →
    IsPGroup 2 ↥R → R ≤ M → M ≤ Subgroup.normalizer (M₀ : Set A) →
    M₀ ≤ Subgroup.normalizer (R : Set A) →
    IsSylowTwoOf R (centralizerSection M M₀ (pCoreOf 2 M₀)) →
    V ≤ M₀ → V ≠ ⊥ → IsElemAbelian 2 V → ⁅V, M₀⁆ = V →
    V ≤ centerOf (pCoreOf 2 (M₀ ⊔ R)) →
    Subgroup.normalizer (V : Set A) ⊓ Subgroup.normalizer (M₀ : Set A) ≤ M →
    Subgroup.normalizer (R : Set A) ≤ M → ¬ S ≤ M →
    (C31Case3 ⊤ R M M₀ V S ∨ C31Case4 ⊤ R M M₀ V S ∨ C31Case5 ⊤ R M M₀ V S ∨
        C31Case6 ⊤ R M M₀ V S ∨ C31Case7 ⊤ R M M₀ V S ∨ C31Case8 ⊤ R M M₀ V S ∨
        C31Case9 ⊤ R M M₀ V S) ∧
      (C48Case1 ⊤ R M M₀ V S ∨ C48Case2 ⊤ R M M₀ V S ∨ C48Case3 ⊤ R M M₀ V S ∨
        C48Case4 ⊤ R M M₀ V S ∨ C48Case5 ⊤ R M M₀ V S ∨ C48Case6 ⊤ R M M₀ V S ∨
        C48Case7 ⊤ R M M₀ V S) ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
        IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 2

@[expose] def InspC31SporadicAtJ (s : TauCeti.SporadicName) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (S M₀ R M V : Subgroup A),
    S.Normal → IsSporadic s ↥S → Subgroup.centralizer (S : Set A) = ⊥ →
    M₀ ≤ S → ⁅M₀, M₀⁆ = M₀ → M₀ ≠ ⊥ → (∃ L ∈ cComp M, M₀ = conjClosure L M) →
    IsPGroup 2 ↥R → R ≤ M → M ≤ Subgroup.normalizer (M₀ : Set A) →
    M₀ ≤ Subgroup.normalizer (R : Set A) →
    IsSylowTwoOf R (centralizerSection M M₀ (pCoreOf 2 M₀)) →
    V ≤ M₀ → V ≠ ⊥ → IsElemAbelian 2 V → ⁅V, M₀⁆ = V →
    V ≤ centerOf (pCoreOf 2 (M₀ ⊔ R)) →
    Subgroup.normalizer (V : Set A) ⊓ Subgroup.normalizer (M₀ : Set A) ≤ M →
    Subgroup.normalizer (R : Set A) ≤ M → ¬ S ≤ M →
    (s = .J4 → Subgroup.normalizer (thompsonJ R : Set A) ≤ M ∧
      Subgroup.normalizer (centerOf R : Set A) ≤ M ∧
      Subgroup.normalizer (omegaOneCenterOf (thompsonJ R) : Set A) ≤ M) →
    (C31Case3 ⊤ R M M₀ V S ∨ C31Case4 ⊤ R M M₀ V S ∨ C31Case5 ⊤ R M M₀ V S ∨
        C31Case6 ⊤ R M M₀ V S ∨ C31Case7 ⊤ R M M₀ V S ∨ C31Case8 ⊤ R M M₀ V S ∨
        C31Case9 ⊤ R M M₀ V S) ∧
      (C48Case1 ⊤ R M M₀ V S ∨ C48Case2 ⊤ R M M₀ V S ∨ C48Case3 ⊤ R M M₀ V S ∨
        C48Case4 ⊤ R M M₀ V S ∨ C48Case5 ⊤ R M M₀ V S ∨ C48Case6 ⊤ R M M₀ V S ∨
        C48Case7 ⊤ R M M₀ V S) ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
        IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 2

theorem InspC31SporadicAt.toJ {s : TauCeti.SporadicName} (h : InspC31SporadicAt s) :
    InspC31SporadicAtJ s :=
  fun A _ _ S M₀ R M V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 _ =>
    h A S M₀ R M V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20

@[expose] def InspC31Sporadic : Prop :=
  ∀ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) →
    InspC31SporadicAtJ s

end CFSG.Quasithin
