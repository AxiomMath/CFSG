module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def Obl10_2_1E4HStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Ch10.Case10_1_1Two T L I →
    ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) →
    ¬ Subgroup.normalizer (baum T : Set G) ≤ fsuM T L →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥ →
    IsShort2 L → IsAltType L 5 →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → H ≤ Subgroup.normalizer (baum T : Set G) →
    ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
    ∀ t₁ ∈ T ⊓ L, ∀ v₁ ∈ fsuUL T L I, v₁ ≠ 1 → v₁ ∈ VZ T H →
      (∀ x ∈ VZ T H, t₁ * x * t₁⁻¹ = x ∨ t₁ * x * t₁⁻¹ = x * v₁) →
      ¬ t₁ ∈ Subgroup.centralizer (VZ T H : Set G) →
      (Subgroup.centralizer (conjClosure (Subgroup.zpowers v₁)
          (oTwoUpper (H ⊓ Subgroup.centralizer ({t⁻¹ * v₁ * t} : Set G))) : Set G)).relIndex
          (oTwoUpper (H ⊓ Subgroup.centralizer ({t⁻¹ * v₁ * t} : Set G))) = 3 ∨
        ∃ x ∈ H ⊓ fsuM T L, orderOf x = 3

@[expose] def Obl10_2_1E4A314 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Ch10.Case10_1_1Two T L I →
    ∀ K : Subgroup G, Ch10.IsLi T L K → IsShort2 K → IsAltType K 5 →
    ∀ X J : Subgroup G, CFSG.SectionRank.IsSQTKCat ↥X → IsSylowTwoOf (Ch10.T1 T L) X →
      J ∈ cComp X → K < J → Ch10.T1 T L ≤ Subgroup.normalizer (J : Set G) →
      ⁅fsuVM T L I, K⁆ ≤ pCoreOf 2 J ∧
        ((Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 7)) ∧
            J = oPrimeResidualOf 3 X) ∨
          (IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)) ∧
            (∃ z ∈ J, z ∈ Subgroup.centralizer (J : Set G) ∧ orderOf z = 3) ∧
            ∀ x ∈ X, orderOf x = 3 → x ∈ J))

@[expose] def Obl10_2_2FourS5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ →
    ¬ IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T) →
    pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) = ⊥ →
      Ch10.Case10_1_1Two T L I ∧
      ∃ K : Subgroup G, Ch10.IsLi T L K ∧ IsShort2 K ∧ IsAltType K 5 ∧
        ∃ X J : Subgroup G, CFSG.SectionRank.IsSQTKCat ↥X ∧ IsSylowTwoOf (Ch10.T1 T L) X ∧
          J ∈ cComp X ∧ K < J ∧ Ch10.T1 T L ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ E : Subgroup G, E ≤ J → IsElemAbelian 3 E → Nat.card E ≤ 3

end CFSG.Quasithin.Vol2.Ch10.SecF
