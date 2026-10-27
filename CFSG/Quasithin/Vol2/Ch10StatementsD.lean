module

public import CFSG.Quasithin.Vol2.Ch10StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Stmt10_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    (∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) → ∀ g : G, g ∉ fsuM T L →
      ⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊓ conjSubgroup ⁅fsuVM T L I, CFSG.conjugate L t⁆ g = ⊥) ∧
    (fsuCVM T L I = ⊥ → ∀ K : Subgroup G, IsLi T L K → IsTISetIn ⁅fsuVM T L I, K⁆ ⊤)

section Notation

variable {G : Type} [Group G]

@[expose] def IsData10_2_11 (T L I : Subgroup G) (t v₁ v₂ : G) : Prop :=
  t ∈ T ∧ t ∉ Subgroup.normalizer (L : Set G) ∧
    v₁ ∈ ⁅fsuVM T L I, L⁆ ⊓ Subgroup.centralizer (T1 T L : Set G) ∧ v₁ ≠ 1 ∧
    v₂ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊓ Subgroup.centralizer (T1 T L : Set G) ∧ v₂ ≠ 1

abbrev Xz (T L : Subgroup G) (z : G) : Subgroup G :=
  oTwoUpper (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G))

abbrev Kz (T L : Subgroup G) (z : G) : Subgroup G :=
  conjClosure (Xz T L z) (Subgroup.centralizer ({z} : Set G))

abbrev Vz (v₁ v₂ : G) : Subgroup G :=
  conjClosure (Subgroup.closure {v₁, v₂}) (Subgroup.centralizer ({v₁ * v₂} : Set G))

end Notation

@[expose] def Stmt10_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      (Vz v₁ v₂ ≤ centerOf (pCoreOf 2 (Subgroup.centralizer ({v₁ * v₂} : Set G))) ∧
        Subgroup.centralizer ({v₁ * v₂} : Set G) ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) ≤
          fsuM T L ⊓ Subgroup.normalizer (Vi T L I L : Set G)) ∧
      (Xz T L (v₁ * v₂) < Kz T L (v₁ * v₂) →
        Vz v₁ v₂ ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) ∧
          IsPrimeReduced 2 ((Vz v₁ v₂).subgroupOf (Subgroup.centralizer ({v₁ * v₂} : Set G)))) ∧
      fsuVM T L I ≤ pCoreOf 2 (Subgroup.centralizer ({v₁ * v₂} : Set G))

@[expose] def Stmt10_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    2 < E3.wParam T (fsuVM T L I) ∨
      (E3.wParam T (fsuVM T L I) = 2 ∧ Case10_1_1Three T L I) ∨
      (E3.wParam T (fsuVM T L I) = 2 ∧ Case10_1_1One T L I 2)

@[expose] def Stmt10_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I ∧ E3.wParam T (fsuVM T L I) = 2 ∧
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → E1.nParam H = 2

end CFSG.Quasithin.Vol2.Ch10
