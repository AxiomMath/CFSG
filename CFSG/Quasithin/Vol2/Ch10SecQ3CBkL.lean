module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def Obl10_2_3BlocksLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ n, Case10_1_1One T L I n →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
      ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ →
    ∀ K : Subgroup G, K ∈ cComp H → H = K ⊔ T →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (H : Set G) = ⊥ →
      fsuCVM T L I = ⊥ →
      IsSylowTwoOf (baum T) (fsuL0 T L ⊔ baum T) →
      IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T) →
      B0 T L ≤ Subgroup.normalizer (K : Set G) →
      (IsChi0Block (fsuL0 T L ⊔ T) L ∨ IsChi0Block H K) →
    ∀ (L₁ : Subgroup G) (b : G), IsLi T L L₁ →
      baum T ≤ Subgroup.normalizer (L₁ : Set G) → baum T ≤ Subgroup.normalizer (K : Set G) →
      b ∈ L₁ → b ∈ K → b ∈ B0 T L → b ∈ Subgroup.normalizer (baum T : Set G) →
      orderOf b = 2 ^ n - 1 →
      (∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (B0 T L) ∧ b ∈ D) →
    n = 2 → ∀ Y : Subgroup G, (Y = L₁ ∨ Y = K) → IsShort2 Y → IsLin2Type Y n →
      blockZ Y = ⊥ → blockQ Y ⊓ Subgroup.centralizer (Y : Set G) = ⊥ →
        Nat.card (blockQ Y) ≠ 2 * Nat.card (blockU Y)

end CFSG.Quasithin.Vol2.Ch10.SecB
