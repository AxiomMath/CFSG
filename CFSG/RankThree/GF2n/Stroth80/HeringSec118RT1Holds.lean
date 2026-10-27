module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module
open scoped commutatorElement Matrix

variable {G : Type} [Group G]


theorem cmSpTransv_holds [Finite G]
    (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ) (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (hx : 2 ^ x = Nat.card Z)
    (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G))
    (hT : CMSpTransvAt M Q Z B m x a h) :
    Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ (4 * m + 1) ∧
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E),
        (∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
          M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y)) ∧
        ∃ W₁ W₂ : Submodule K M₀.E,
          W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ ∧
          (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁) ∧
          (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂) ∧
          (∀ w ∈ W₁, M₀.Qf w = 0) ∧ (∀ w ∈ W₂, M₀.Qf w = 0) ∧
          ∃ (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁)
            (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K),
            ρ.range = StatedSp m K ∧
            (∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
            ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
              φ s ((b i : ↥W₁) : M₀.E) =
                ∑ j, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i •
                  ((b j : ↥W₁) : M₀.E) :=
  cmSpTransv_of_rt1
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hq hBN hBNnd hN Qf hnd ρ hρQ hS₀ hC hV =>
      CFSG.ClassicalGroups.Orthogonal.SiegelRT1.exists_decomposition_of_siegel hq hBN hBNnd hN Qf
        hnd ρ hρQ hS₀ hC hV)
    M Q Z B hc n m x hw hn ha2 hLm hx a h hT

end CFSG.RankThree.GF2n.Stroth80
