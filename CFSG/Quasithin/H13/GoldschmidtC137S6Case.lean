module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Main

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem c137CaseS6A6M_of (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32) :
    ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
      ¬ autOn T V ≤ autOn L V →
      T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) → P = M →
      ∀ hred : IsTwoReducedIn X V, ⁅V, L⁆ ≠ ⊥ →
        (∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI hred.2.2.1 L))) →
        Concl X T V L P :=
  fun G _ _ _ _ _ _ _ _ hX hSQ hT hprod hL hL2 hA6 hnin hTP hPM hMX hmax hPeq hred hVL hmod =>
    s6_concl (hC124 G) hC132
      ⟨hX, hSQ, hT, hprod, hL, hL2, hA6, hnin, hTP, hPM, hMX, hmax, hPeq, hred, hVL, hmod⟩

theorem c137CaseS6A6_of (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32) :
    ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
      ¬ autOn T V ≤ autOn L V → (∃ _ : IsMulCommutative ↥V,
        AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) →
      T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) → P = M →
      IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ → Concl X T V L P :=
  fun G _ _ X T V L P M hX hSQ hT hprod hL hL2 hA6 hnin hnat hTP hPM hMX hmax hPeq hred hVL =>
    c137CaseS6A6M_of hC124 hC132 G X T V L P M hX hSQ hT hprod hL hL2 hA6 hnin hTP hPM hMX hmax
      hPeq hred hVL (model_of_natural hred.2.2.1 hnat)

end CFSG.Quasithin.H13.U3.GC137
