module

public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def burnsideC137_Concl (G : Type) [Group G] (X T L P V Q : Subgroup G) : Prop :=
    ((∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum (pCoreOf 2 P) ∧
        (D.subgroupOf (baum (pCoreOf 2 P))).Characteristic ∧
        X ≤ Subgroup.normalizer (D : Set G)) ∨
    ((IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsHatA6Block L ∨ IsG2TwoBlockNatural L) ∧
      (IsHatA6Block L → ∃ E : Subgroup G, E ≤ ⁅V, L⁆ ∧ IsE2 4 ↥E ∧
        autOn Q V = autOn (X ⊓ Subgroup.normalizer (E : Set G)) V)) ∨
    (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ⁅V, L⁆ = ⁅pCoreOf 2 L, L⁆ ∧
      ∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (U₁ U₂ : Subgroup G)
        (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
        (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)),
        SumOfTwoNat L ⁅V, L⁆ α U₁ U₂ β₁ β₂ ∧
        ∃ (ℓ : Submodule (ZMod 2) (Fin 3 → ZMod 2))
          (coordinates : ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L ⁅V, L⁆},
            ↥I.val →* Multiplicative (Fin 3 → ZMod 2)),
          Module.finrank (ZMod 2) ℓ = 2 ∧
          (∀ I, IsNatVia L I.val ⊥ α (coordinates I)) ∧
          P = X ⊓ ⨅ I : {I : Subgroup G // I ∈ internalIrrPlus L ⁅V, L⁆},
            Subgroup.normalizer (preimageIn I.val (coordinates I) ℓ : Set G)) ∨
    (IsG2Two ↥(autOn X V) ∧
      InternalG2TwoNatural X V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ∧
      (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, L⁆ = 2 ^ 6 ∧
      IsIrrSection X (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ⁅V, L⁆ ∧
      ∃ l : Subgroup G, ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ l ∧ l ≤ ⁅V, L⁆ ∧
        (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex l = 4 ∧
        P = X ⊓ Subgroup.normalizer (l : Set G)) ∨
    (Nonempty (↥(autOn X V) ≃* Equiv.Perm (Fin 6)) ∧
      InternalS6Natural X V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ∧
      (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, L⁆ = 2 ^ 4 ∧
      IsIrrSection X (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ⁅V, L⁆ ∧
      (∃ l : Subgroup G, ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ l ∧ l ≤ ⁅V, L⁆ ∧
        (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex l = 4 ∧
        autOn P V = autOn (X ⊓ Subgroup.normalizer (l : Set G)) V) ∧
      (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) →
        ¬ oTwoUpper (oTwoZIn L) ≤ P) ∧
      ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V)))

@[expose] def burnsideC137_Hyp (G : Type) [Group G] (X T L P M V : Subgroup G) : Prop :=
  (X : Set G) = (L : Set G) * (T : Set G) ∧ IsSylowTwoOf T X ∧ L ∈ cComp X ∧ CharTwo X ∧
    (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsAlt 6 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) ∨
      IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
    TrivialOnDynkin L T ∧
    T ≤ P ∧ P ≤ M ∧ IsMaxSubgroupIn X M ∧
    (P = M ∨ (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) ∧ P.relIndex M = 3 ∧
      ¬ oTwoUpper P ≤ oTwoZIn L)) ∧
    IsTwoReducedIn X V ∧ ⁅V, L⁆ ≠ ⊥ ∧
    (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
      (∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (U₁ U₂ : Subgroup G)
          (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
          (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)), SumOfTwoNat L ⁅V, L⁆ α U₁ U₂ β₁ β₂) ∨
      ((∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
          (β : ↥⁅V, L⁆ →* Multiplicative (Fin 3 → ZMod 2)),
          Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ IsNatVia L ⁅V, L⁆ ⊥ α β) ∧
        ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ Subgroup.centralizer ({u} : Set G)))

@[expose] def burnsideC137_C_1_37_corr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    burnsideC137_Hyp G X T L P M V → burnsideC137_Concl G X T L P V M

theorem burnsideC137_C_1_37_of_corr (h : burnsideC137_C_1_37_corr) : C_1_37 := by
  intro G _ _ X T L P M V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  exact h G X T L P M V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end CFSG.ASVolI
