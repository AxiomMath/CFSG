module

public import CFSG.Quasithin.Vol2.Ch10StatementsB
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section Notation

variable {G : Type} [Group G]

abbrev Vi (T L I K : Subgroup G) : Subgroup G :=
  ⁅fsuVM T L I, K⁆

@[expose] def IsU10_2_8 (T L I K U : Subgroup G) : Prop :=
  U ≤ ⁅fsuVM T L I, K⁆ ∧ ∀ v ∈ ⁅fsuVM T L I, K⁆,
    (v ∈ U ↔ ∀ s ∈ T1 T L, s * v * s⁻¹ * v⁻¹ ∈ fsuCVM T L I)

@[expose] def IsR10_2_8 (T L I K U R : Subgroup G) : Prop :=
  R ≤ T ∧ ∀ x ∈ T, (x ∈ R ↔ ∃ hx : x ∈ Subgroup.normalizer (fsuVM T L I : Set G),
    conjAct (fsuVM T L I) ⟨x, hx⟩ ∈
      pCoreOf 2 (autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I)))

end Notation

@[expose] def Stmt10_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Subgroup.normalizer (T1 T L : Set G) ≤ fsuM T L

@[expose] def Stmt10_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    IsUniqueM (fsuL0 T L ⊔ T1 T L) (fsuM T L) ∧
    (∀ K : Subgroup G, IsLi T L K →
      Subgroup.normalizer (Vi T L I K : Set G) ≤ fsuM T L) ∧
    Subgroup.normalizer (L : Set G) ≤ fsuM T L

@[expose] def Stmt10_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ¬ Case10_1_1Six T L I ∧
      T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) = pCoreOf 2 (fsuL0 T L ⊔ T)

@[expose] def Stmt10_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I → LBarL32 L →
    fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
      ⁅quasithinOmegaOneCenter T, L⁆ = ⊥ ∧
      omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) =
        omegaOneCenterOf (T1 T L) ⊔ fsuVM T L I ∧
      omegaOneCenterOf (T1 T L) =
        omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
          Subgroup.centralizer (fsuL0 T L : Set G) ∧
      (L = ⁅L, thompsonJ T⁆ ∧
        ∀ H : Subgroup G, IsHStar T (fsuM T L) H → ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) ∧
      ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) → ∀ U₁ U₂ R₁ R₂ : Subgroup G,
        IsU10_2_8 T L I L U₁ → IsU10_2_8 T L I (CFSG.conjugate L t) U₂ →
        IsR10_2_8 T L I L U₁ R₁ → IsR10_2_8 T L I (CFSG.conjugate L t) U₂ R₂ →
        ∀ v₂ : ↥(fsuVM T L I), (v₂ : G) ∈ U₂ →
          (v₂ : G) ∉ Subgroup.centralizer (fsuL0 T L : Set G) →
          Nonempty (↥(autOn (fsuL0 T L ⊔ T) (fsuVM T L I) ⊓
              MulAction.stabilizer (MulAut ↥(fsuVM T L I)) v₂) ≃*
            (↥(alternatingGroup (Fin 4)) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ∧
          R₁ ⊔ R₂ ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) =
            thompsonJ T ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ∧
          T ⊓ Subgroup.centralizer ({(v₂ : G)} : Set G) =
            (T ⊓ L) ⊔ R₂ ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ∧
          omegaOneCenterOf (T ⊓ Subgroup.centralizer ({(v₂ : G)} : Set G)) =
            omegaOneCenterOf (T1 T L) ⊔ Subgroup.zpowers (v₂ : G)

@[expose] def Stmt10_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ K : Subgroup G, IsLi T L K →
      (∀ v ∈ ⁅fsuVM T L I, K⁆, v ≠ 1 →
        Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) ∧
      ((E3.mQuot ⁅fsuVM T L I, K⁆ ⊥ : ℕ) : ℕ∞) ≤ E3.rParam (fsuVM T L I) ∧
      ∀ v ∈ ⁅fsuVM T L I, K⁆, v ∉ Subgroup.centralizer (fsuL0 T L : Set G) →
        Subgroup.centralizer ({v} : Set G) ≤
          fsuM T L ⊓ Subgroup.normalizer (Vi T L I K : Set G)

end CFSG.Quasithin.Vol2.Ch10
