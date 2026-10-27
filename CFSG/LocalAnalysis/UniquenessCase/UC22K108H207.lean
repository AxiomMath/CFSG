module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def K108FamL2 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ IsL2 S n
@[expose] def K108FamSz (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ IsSz S n
@[expose] def K108FamU3 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ IsU3 S n
@[expose] def K108FamL3 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ IsL3 S n
@[expose] def K108FamSp4 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ IsSp4 S n
@[expose] def K108FamG2 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ IsG2 S n
@[expose] def K108Fam3D4 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 ≤ n ∧ Is3D4 S n
@[expose] def K108Fam2F4 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ LieModel S .twistedF4 0 2 n
@[expose] def K108FamU4 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 ≤ n ∧ IsU4 S n
@[expose] def K108FamU5 (S : Type) [Group S] : Prop := IsU5 S 2
@[expose] def K108FamL4 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ LieModel S .PSL 4 2 n
@[expose] def K108FamSp6 (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 < n ∧ LieModel S .PSp 3 2 n
@[expose] def K108FamO8m (S : Type) [Group S] : Prop := ∃ n : ℕ, 2 ≤ n ∧ IsOmega8m S n
@[expose] def K108Fam3D4two (S : Type) [Group S] : Prop := Is3D4 S 1

@[expose] def IsList207 (S : Type) [Group S] : Prop :=
  K108FamL2 S ∨ K108FamSz S ∨ K108FamU3 S ∨ K108FamL3 S ∨ K108FamSp4 S ∨ K108FamG2 S ∨ K108Fam3D4 S ∨
    K108Fam2F4 S ∨ K108FamU4 S ∨ K108FamU5 S ∨ K108FamL4 S ∨ K108FamSp6 S ∨ K108FamO8m S ∨ K108Fam3D4two S

theorem IsList207.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : IsList207 S) :
    IsList207 S' := by
  have t : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}, LieModel S t m 2 f → LieModel S' t m 2 f :=
    fun h => LieModel.of_mulEquiv e h
  unfold IsList207 K108FamL2 K108FamSz K108FamU3 K108FamL3 K108FamSp4 K108FamG2 K108Fam3D4 K108Fam2F4 K108FamU4
    K108FamU5 K108FamL4 K108FamSp6 K108FamO8m K108Fam3D4two at h ⊢
  rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ |
    ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
  all_goals
    repeat
      first
        | exact Or.inl ⟨n, hn, t h⟩
        | exact Or.inl (t h)
        | exact ⟨n, hn, t h⟩
        | exact t h
        | refine Or.inr ?_

@[expose] def K108H207 : Prop :=
  ∀ (Gh : Type) [Group Gh] [Finite Gh] (S : Subgroup Gh), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → centralizer (S : Set Gh) = ⊥ → IsList207 ↥S →
    ∀ (T B : Subgroup Gh), Hyp10 T B → S ⊔ B = ⊤ →
    ∀ (X M : Subgroup Gh), X ≤ B → (Nat.card X).Prime → Odd (Nat.card X) →
      T ≤ M → X ≤ M → (∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) → S ≤ M

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
