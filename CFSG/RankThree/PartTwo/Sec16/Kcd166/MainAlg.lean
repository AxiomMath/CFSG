module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

@[expose] def MainAlg166 : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] [IsAlgClosed 𝕜] (p : ℕ) [CharP 𝕜 p], p.Prime → 5 ≤ p →
  ∀ (Γ : Type) [Group Γ] [Finite Γ], Group.IsPerfect Γ →
  ∀ (V : Type) [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (σ : Representation 𝕜 Γ V), σ.IsIrreducible → Function.Injective σ →
    (∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (σ t - 1)) ≤ 3) →
  ∀ (T : Type) [Group T] (π : Γ →* T), Function.Surjective π →
    Sec4.IsTripleCover T (alternatingGroup (Fin 6)) →
    Nat.Coprime (Nat.card π.ker) 3 → Group.IsSolvable π.ker →
  ∀ d : Γ, d ^ 3 = 1 → π d ∈ Subgroup.center T →
  ∀ I : Subgroup Γ, Group.IsPerfect I → Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)) →
    IsPGroup 2 ↥(I ⊓ π.ker) → I ≤ Subgroup.centralizer ({d} : Set Γ) →
  ∀ v : V, (∀ g ∈ I, σ g v = v) → σ d v = v

end CFSG.RankThree.PartTwo.Sec16.Kcd166
