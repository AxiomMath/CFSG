module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.ClassicalGroups.Symplectic
  CFSG.ClassicalGroups.Orthogonal CFSG.CGT.Timmesfeld75 CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

@[expose] def Sec5NatPointsSpStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧ ∃ m : ℕ, 2 ≤ m ∧
        ∃ (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
          φ.range = StatedSp m K ∧ φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
          SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
            (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) ∧
          spForm m K u u' ≠ 0 ∧
          ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u ∧
          ((conjSubgroup r (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u'

@[expose] def Sec5NatPointsOmegaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec5Hyp hc n t → OmegaNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
        ((∃ (m : ℕ) (hm : 3 ≤ m)
            (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
            quadPlus m K u = 0 ∧ quadPlus m K u' = 0 ∧ u ≠ 0 ∧ u' ≠ 0 ∧
            polar (quadPlus m K) u u' ≠ 0 ∧
            φ.range = StatedOmega (StatedQuadPlus m K) ∧
            φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
            SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
              (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) ∧
            ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LomGLPlus hm u ∧
            ((conjSubgroup r (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
              LomGLPlus hm u') ∨
          (∃ (m : ℕ) (b c : K) (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
            (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
            (u u' : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K),
            quadMinus m K b c u = 0 ∧ quadMinus m K b c u' = 0 ∧ u ≠ 0 ∧ u' ≠ 0 ∧
            polar (quadMinus m K b c) u u' ≠ 0 ∧
            φ.range = StatedOmega (StatedQuadMinus m K b c) ∧
            φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
            SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
              (fun g => (g : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
                (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) ∧
            ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LomGLMinus hm hirr u ∧
            ((conjSubgroup r (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
              LomGLMinus hm hirr u'))

end CFSG.RankThree.GF2n.Stroth80
