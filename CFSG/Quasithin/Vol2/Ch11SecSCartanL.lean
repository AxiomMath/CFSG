module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanT4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

structure CartanL (L V₁ V₂ X : Subgroup G) : Prop where
  a : X ≤ xOne X (LOf L V₁) ⊔ (X ⊓ LOf L V₁)
  b : X ≤ (X ⊓ LOf L V₁) ⊔ (X ⊓ LOf L V₂)
  c : X ⊓ LOf L V₁ ⊓ sectionCentralizer (LOf L V₂) (pCoreOf 2 (LOf L V₂)) = ⊥
  card₁ : Nat.card ↥(X ⊓ LOf L V₁) = 3
  cardX₁ : Nat.card ↥(xOne X (LOf L V₁)) = 3
  card₂ : Nat.card ↥(X ⊓ LOf L V₂) = 3
  cardX₂ : Nat.card ↥(xOne X (LOf L V₂)) = 3

@[expose] def CartanSp4 (L V₁ V₂ X : Subgroup G) : Prop :=
  X ⊓ LOf L V₁ ≠ xOne X (LOf L V₁) ∧ X ⊓ LOf L V₁ ≠ X ⊓ LOf L V₂ ∧
  X ⊓ LOf L V₁ ≠ xOne X (LOf L V₂) ∧ xOne X (LOf L V₁) ≠ X ⊓ LOf L V₂ ∧
  xOne X (LOf L V₁) ≠ xOne X (LOf L V₂) ∧ X ⊓ LOf L V₂ ≠ xOne X (LOf L V₂) ∧
  ∀ E : Subgroup G, E ≤ X → Nat.card ↥E = 3 →
    E = X ⊓ LOf L V₁ ∨ E = xOne X (LOf L V₁) ∨ E = X ⊓ LOf L V₂ ∨ E = xOne X (LOf L V₂)

@[expose] def CartanG2 (L V₁ V₂ X : Subgroup G) : Prop :=
  xOne X (LOf L V₁) ≤ LOf L V₂

variable {T L I V₁ V₂ X : Subgroup G} {n : ℕ}

theorem autOn_cartan_data (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {i : ℕ}
    (hi : i = 1 ∨ i = 2) {U : Subgroup G} (hU : IsVi T L I n i U) (hX : IsCartanX T L X) :
    autOn (X ⊓ LOf L U) (fsuV T I) =
        autOn X (fsuV T I) ⊓ gammaW (autOn L (fsuV T I)) (U.subgroupOf (fsuV T I)) ∧
      autOn (xOne X (LOf L U)) (fsuV T I) =
        centW (autOn X (fsuV T I)) (gammaW (autOn L (fsuV T I)) (U.subgroupOf (fsuV T I))) := by
  have hL := L_le_normalizer_fsuV h
  have hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [centralizer_eq_pCoreOf h1102 h]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  exact ⟨autOn_inf_lOf hL (IsVi.le_fsuV hU) (fun x hx => (hX.1 hx).1) hX.2.1 hC,
    autOn_xOne hL (IsVi.le_fsuV hU) (cartan_le_normalizer_lOf hN h1102 h hi hU hX) hC⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
