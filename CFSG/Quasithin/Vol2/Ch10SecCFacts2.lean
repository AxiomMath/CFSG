module

public import CFSG.Quasithin.Vol2.Ch10SecC9Irr
public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def S5Core {Γ : Type} [Group Γ] [Finite Γ] (H R J L V : Subgroup Γ)
    (hV : IsElemAbelian 2 V) : Prop :=
  SQTKGroup ↥H ∧ CharTwo H ∧ IsSylowTwoOf R H ∧ J ∈ cComp H ∧
    H ≤ Subgroup.normalizer (J : Set Γ) ∧ J ⊔ R = H ∧ ¬ CFSG.Open.IsQuasisimple ↥J ∧
    IsTwoReducedIn H V ∧ V ≤ J ∧ CFSG.Open.IsQuasisimple ↥(autI hV J) ∧
    ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set Γ) ∧ L ∈ lFamily R ∧ L ≤ J ∧
    R ≤ Subgroup.normalizer (L : Set Γ) ∧ IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    ¬ L ≤ Subgroup.centralizer (V : Set Γ) ∧ autI hV L ≠ autI hV J

@[expose] def FactK2 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H R J L V₁ V : Subgroup Γ) (hV : IsElemAbelian 2 V),
    S5Core H R J L V hV → V₁ ≤ L → IsElemAbelian 2 V₁ →
    L ⊔ R ≤ Subgroup.normalizer (V₁ : Set Γ) → ⁅V₁, L⁆ = V₁ →
    pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ) →
    J ⊓ Subgroup.normalizer (V₁ : Set Γ) ≤ Subgroup.normalizer (L : Set Γ) → ModCase L V₁ →
    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) ∧
    ((∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
        (V₁ ≤ V → ∃ x ∈ J ⊓ Subgroup.normalizer (L : Set Γ), Odd (orderOf x) ∧
          (∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∣ 2 ^ n - 1) ∧
          (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) ∧
          x ∉ Subgroup.centralizer (V₁ : Set Γ))) ∨
      (Nonempty (↥(autI hV J) ≃* ↥(alternatingGroup (Fin 7))) ∧
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 5))) ∨
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        (Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
          Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ∧
        J ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 J))

@[expose] def FactK4 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H R J L V : Subgroup Γ) (hV : IsElemAbelian 2 V),
    S5Core H R J L V hV → IsAltQuotient J (oTwoZIn J) 7 →
    (IsChiBlock H J ∨ (IsBlock2 H J ∧ (CFSG.Quasithin.IsExcA7Block J ∨ IsAltBlockType J 6 ∨
      CFSG.Quasithin.IsHatA6Block J))) →
    J ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 J ∧
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      CFSG.Quasithin.IsExcA7Block J) ∧
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 5))) → ⁅V, J⁆ = V →
      IrrG L V ∨
      ((∀ v ∈ ⁅V, L⁆, ∃ l ∈ L, orderOf l = 3 ∧ l * v = v * l) ∧
        ∀ y ∈ J ⊓ Subgroup.normalizer (L : Set Γ), orderOf y = 3 →
          y ∈ L ⊔ (J ⊓ Subgroup.centralizer (V : Set Γ))))

@[expose] def FactK7 : Prop :=
  ∀ (X : Type) [Group X] (s : Bool) (r e : ℕ), IsPSLEps3 s r e X →
    ∀ f : X →* ↥(alternatingGroup (Fin 7)), ¬ Function.Surjective f

end CFSG.Quasithin.Vol2.Ch10.SecC
