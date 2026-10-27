module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin

structure CentASetting {G : Type} [Group G] [Finite G] (m : ℕ) (Y L R : Subgroup G) (b t : G)
    (φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)) : Prop where
  m_cases : m = 6 ∨ m = 7
  t_mem : t ∈ Y
  b_mem : b ∈ Y
  L_le : L ≤ Y
  φ_t : φ ⟨t, t_mem⟩ = jGL 1 m
  φ_b : φ ⟨b, b_mem⟩ = betaStd m
  φ_L : ∀ y : ↥Y, (y : G) ∈ L ↔ φ y ∈ leviB m
  nor : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)
  rad_le : R ≤ Subgroup.centralizer (Y : Set G)
  rad_odd : Odd (Nat.card R)
  rad : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
    R ⊔ Subgroup.zpowers b

@[expose] def CentAFus {G : Type} [Group G] {m : ℕ} (Y : Subgroup G) (b t : G)
    (φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)) : Prop :=
  ∀ g : G, g * b * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G) →
    ∃ h ∈ Subgroup.centralizer ({t} : Set G),
      h * (g * b * g⁻¹) * h⁻¹ = ((φ.symm (bStar m) : ↥Y) : G) ∨
        h * (g * b * g⁻¹) * h⁻¹ = ((φ.symm (bStar m) : ↥Y) : G)⁻¹

end CFSG.StandardType.FF81.CentA

end
