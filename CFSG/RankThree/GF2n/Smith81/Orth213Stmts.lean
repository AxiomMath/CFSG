module

public import CFSG.RankThree.GF2n.Smith81.Orth28Route

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)

namespace CFSG.RankThree.GF2n.Smith81

@[expose] def OrthClassStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (C : OrthCtx M Q Z B) (X : Subgroup G) (x : G), Sit M Q Z X x →
      (∃ g : Matrix (Fin 2) (Fin 2) C.K, g.det = 1 ∧ g ≠ 1 ∧ (g - 1) * (g - 1) = 0 ∧
          ActsAsTensor Q Z C.M₀ C.φ x g id) ∨
      (∃ u w : C.ι → C.K, C.qU u = 0 ∧ C.qU w = 0 ∧ QuadraticMap.polar C.qU u w = 0 ∧
          LinearIndependent C.K ![u, w] ∧
          ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑(eichler C.qU u w))

@[expose] def Orth213FrameStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ (A : Subgroup G), IsZConjugate Z A → ∀ x y : G, IsConj z x → IsConj z y →
      x ∈ QB A → y ∈ Subgroup.centralizer (A : Set G) → Orth213Concl z x y

@[expose] def Orth213OddStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ x y : G, x ∈ M → y ∈ M → IsConj z x → IsConj z y →
      x ∉ Q → y ∉ Q → ∀ X : Subgroup G, IsZConjugate Z X → x ∈ X →
      (∀ A : Subgroup G, IsZConjugate Z A → A ≤ Q ⊓ QB X →
        ¬ A ≤ Subgroup.centralizer ({y} : Set G)) →
      Odd (orderOf (x * y))

end CFSG.RankThree.GF2n.Smith81
