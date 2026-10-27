module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Stmt12_2_11' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H U : Subgroup G), Hyp1223 G T L V →
    IsHStar T (Subgroup.normalizer (L : Set G)) H → U ≠ ⊥ → U ≤ V →
    H ≤ Subgroup.normalizer (U : Set G) →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
      (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
          alternatingGroup (Fin 6)) ∧
        Nat.card V = 2 ^ 6 ∧
        ∀ v ∈ V ⊓ Subgroup.centralizer (T : Set G), v ≠ 1 →
          V ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G))) ∨
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∧ Nat.card V = 2 ^ 6 ∧
        ∀ V₃ : Subgroup G, V₃ ≤ V → Nat.card V₃ = 2 ^ 3 → T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) →
          Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (L : Set G))) →
      E1.nParam H ≤ 2 ∧
      (E1.nParam H = 2 → ∀ C : Subgroup G, C ≤ H ⊓ Subgroup.normalizer (L : Set G) →
        Odd (Nat.card C) → (∃ k : ℕ, C.relIndex (H ⊓ Subgroup.normalizer (L : Set G)) = 2 ^ k) →
        C ≠ ⊥ ∧ IsPGroup 3 C)

theorem stmt12_2_11'_of (h : Stmt12_2_11) : Stmt12_2_11' := by
  intro G _ _ T L V H U hH hHs hU hUV hHU hcase
  refine h G T L V H U hH hHs hU hUV hHU ?_
  rcases hcase with h5 | ⟨hp, hZ, he, -, hv⟩ | h3
  · exact Or.inl h5
  · exact Or.inr (Or.inl ⟨hp, hZ, he, hv⟩)
  · exact Or.inr (Or.inr h3)

end CFSG.Quasithin.H13
