module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type*} [Group G]

structure IsSignalizerFunctor (p k : ℕ) (A : Subgroup G) (Θ : Subgroup G → Subgroup G) :
    Prop where
  central : ∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ Subgroup.centralizer (S : Set G)
  coprime : ∀ S ∈ signalizerFunctorEk p k A, Nat.Coprime p (Nat.card (Θ S))
  normalized : ∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G)
  balanced : ∀ S ∈ signalizerFunctorEk p k A, ∀ S' ∈ signalizerFunctorEk p k A,
    Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S'

@[expose] def completion (p k : ℕ) (A : Subgroup G) (Θ : Subgroup G → Subgroup G) : Subgroup G :=
  ⨆ S ∈ signalizerFunctorEk p k A, Θ S

@[expose] def IsComplete (p k : ℕ) (A : Subgroup G) (Θ : Subgroup G → Subgroup G) : Prop :=
  Nat.Coprime p (Nat.card (completion p k A Θ)) ∧
    ∀ S ∈ signalizerFunctorEk p k A,
      completion p k A Θ ⊓ Subgroup.centralizer (S : Set G) = Θ S

theorem le_completion {p k : ℕ} {A : Subgroup G} {Θ : Subgroup G → Subgroup G} {S : Subgroup G}
    (hS : S ∈ signalizerFunctorEk p k A) : Θ S ≤ completion p k A Θ :=
  le_iSup_of_le S (le_iSup_of_le hS le_rfl)

theorem completion_le {p k : ℕ} {A : Subgroup G} {Θ : Subgroup G → Subgroup G} {H : Subgroup G}
    (h : ∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ H) : completion p k A Θ ≤ H :=
  iSup₂_le h

theorem le_normalizer_completion {p k : ℕ} {A : Subgroup G} {Θ : Subgroup G → Subgroup G}
    (h : ∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G)) :
    A ≤ Subgroup.normalizer (completion p k A Θ : Set G) :=
  CFSG.SignalizerFunctor.Helpers.signalizer_completion_normalized p k A Θ h

theorem mem_Ek_of_le {p k : ℕ} {A B S : Subgroup G} (hAB : A ≤ B)
    (hS : S ∈ signalizerFunctorEk p k A) : S ∈ signalizerFunctorEk p k B :=
  ⟨hS.1.trans hAB, hS.2⟩

end CFSG.SignalizerFunctorTheorem
