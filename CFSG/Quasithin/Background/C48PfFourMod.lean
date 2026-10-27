module

public import CFSG.Quasithin.EmptyFaithful.T1515Concl
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.C48Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def FourModFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K U P P₀ V : Subgroup G) (hU : IsElemAbelian 2 U),
    K ≤ Subgroup.normalizer (U : Set G) → K ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 K →
    (IsPSL 4 2 1 ↥(autOn K U) ∨ IsPSL 5 2 1 ↥(autOn K U)) →
    @Alt15127 ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) →
    IsParabolic2 K P → P ≠ K → P₀ ≤ P → P ≤ Subgroup.normalizer (P₀ : Set G) → ⁅P₀, P₀⁆ = P₀ →
    ∀ m : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 P₀) →
    V ≠ ⊥ → V ≤ ⁅U, K⁆ → V ≤ Subgroup.centralizer (pCoreOf 2 P₀ : Set G) → ⁅V, P₀⁆ = V →
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧
          IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k) ∨
        (m = 4 ∧ IsAltNaturalSection P₀ V ⊥ (CFSG.pCore 2 ↥P₀) 8)

end CFSG.Quasithin.C48Pf
