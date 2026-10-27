module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G]

@[expose] def R613Def (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
    (3 < p ∧ Group.IsSolvable D.M ∧ IsWeaklyClosedIn P₀ P ∧
      rankThreeGamma 1 p (P ⊓ inftyOf (centralizer (P₀ : Set G))) ≤ D.M ∧
      (∃ n : ℕ, 1 < n ∧ LieModel (inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n) ∧
      CFSG.Open.uniqueFourIsFrobenius
        (CFSG.Open.uniqueFourPrimeCore p D.M ⊔
          centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))
        (CFSG.Open.pCoreOf 2 D.M) (centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))) ∧
    P ≤ centralizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G)

@[expose] def R613Aut (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
    ((∀ m ∈ D.M, (∀ x ∈ P ⊓ inftyOf (centralizer (P₀ : Set G)),
        m * x * m⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) →
      m ∈ centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G) ⊔
        (P ⊓ inftyOf (centralizer (P₀ : Set G))) ⊔ CFSG.Open.pCoreOf 2 D.M) ∧
      D.M ≤ normalizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) ⊔
        CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) ∧
      ∀ t ∈ D.T, (∀ x ∈ P ⊓ inftyOf (centralizer (P₀ : Set G)),
        t * x * t⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → t ∈ CFSG.Open.pCoreOf 2 D.M)

@[expose] def R613Irr (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
    IrrOn (D.M ⊓ normalizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G))
      (P ⊓ inftyOf (centralizer (P₀ : Set G)))

theorem r6_13_of_parts (D : Data G)
    (h12 : ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
      (3 < p ∧ Group.IsSolvable D.M ∧ IsWeaklyClosedIn P₀ P ∧
        rankThreeGamma 1 p (P ⊓ inftyOf (centralizer (P₀ : Set G))) ≤ D.M ∧
        (∃ n : ℕ, 1 < n ∧ LieModel (inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n) ∧
        CFSG.Open.uniqueFourIsFrobenius
          (CFSG.Open.uniqueFourPrimeCore p D.M ⊔
            centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))
          (CFSG.Open.pCoreOf 2 D.M) (centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))) ∧
      CFSG.IsStronglyClosedIn P ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) ∧
      (∀ X : Subgroup G, X ≤ P ⊓ inftyOf (centralizer (P₀ : Set G)) → X ≠ ⊥ → InU D.M X))
    (h4 : R613Aut D) (h5 : R613Irr D) : R6_13 D := fun p P P₀ h =>
  ⟨(h12 p P P₀ h).1, (h12 p P P₀ h).2.1, (h12 p P P₀ h).2.2, h4 p P P₀ h, h5 p P P₀ h⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

structure Sigma2Std (D : Data G) : Prop where
  exists_hyp612 : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀

theorem uc22p22q_inftyOf_conj {K : Subgroup G} {n x : G} (hn : n ∈ normalizer (K : Set G))
    (hx : x ∈ UC6.inftyOf K) : n * x * n⁻¹ ∈ UC6.inftyOf K := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨UC6.conjOn K hn y, ?_, rfl⟩
  have h := map_derivedSeries_le_derivedSeries (UC6.conjOn K hn).toMonoidHom (Nat.card K)
  exact h ⟨y, hy, rfl⟩

theorem uc22p22q_layer_le (H : Subgroup G) : rankThreeLayer H ≤ H :=
  sSup_le fun _ hL => hL.1

end CFSG.LocalAnalysis.UniquenessCase.UC22
