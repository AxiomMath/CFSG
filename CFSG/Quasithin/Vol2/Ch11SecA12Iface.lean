module

public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

abbrev xOne (X L₁ : Subgroup G) : Subgroup G :=
  X ⊓ sectionCentralizer L₁ (pCoreOf 2 L₁)

@[expose] def Stmt11_1_2Star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (V₁ V₂ X K : Subgroup G),
    Hyp11 G T L I 2 → IsVi T L I 2 1 V₁ → IsVi T L I 2 2 V₂ → IsCartanX T L X →
    quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G)) →
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) →
    LOf L V₁ < K → ¬ K ≤ Subgroup.normalizer (L : Set G) → QuasithinUnique.CharTwo K →
    K ≤ Subgroup.centralizer (V₁ : Set G) →
    IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(K ⊔ xOne X (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(K ⊔ xOne X (LOf L V₁)) ≃*
        (Matrix.GeneralLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)))) →
      Case11_1_2Three T L K X (LOf L V₁) (LOf L V₂)

end CFSG.Quasithin.Vol2.Ch11.SecA
