module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

structure Cfg133 {W : Type} [CommGroup W] [Finite W] (A : Subgroup (MulAut W)) (t : MulAut W)
    (p : ℕ) : Prop where
  hW : ∀ w : W, w * w = 1
  htA : t ∈ A
  ht2 : t ^ 2 = 1
  ht1 : t ≠ 1
  hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  hO2 : pCoreOf 2 A = ⊥
  hp : p.Prime
  hP : ⁅pCoreOf p A, Subgroup.zpowers t⁆ ≠ ⊥

@[expose] def IsEntireIsotypic {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (U : Subgroup W) :
    Prop :=
  ∀ V₁ V₀ : Subgroup W, V₀ ≤ U → IsIrrOn L V₀ ⊥ → IsIrrOn L V₁ ⊥ → SecIsoOn L V₁ ⊥ V₀ ⊥ →
    V₁ ≤ U

@[expose] def conjClosure {W : Type} [CommGroup W] (A Q : Subgroup (MulAut W)) :
    Subgroup (MulAut W) :=
  Subgroup.closure {x | ∃ g ∈ A, ∃ y ∈ Q, x = g * y * g⁻¹}

@[expose] def omegaOne {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P ∧ x ^ p = 1}

structure Data8 {W : Type} [CommGroup W] [Finite W] (A : Subgroup (MulAut W)) (t z : MulAut W)
    (N : Subgroup (MulAut W)) : Prop where
  hP : IsPOnePlusTwo 3 ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆)
  hzN : z ∈ N
  hNP : N ≤ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆
  hz3 : orderOf z = 3
  hzc : ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, y * z = z * y
  hZP : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, (∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
    y * x = x * y) → x ∈ Subgroup.zpowers z
  htz : t * z * t⁻¹ = z
  hN : IsElemAbelianOfRank 3 2 ↥N
  hNO : ∀ g ∈ pCoreOf 3 A, ∀ x ∈ N, g * x * g⁻¹ ∈ N
  hNt : ∀ x ∈ N, t * x * t⁻¹ ∈ N
  hrkt : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3
  hNV : commSub ⊤ N = commSub ⊤ (Subgroup.zpowers z)
  hrkz : rk ↥(commSub ⊤ (Subgroup.zpowers z)) = 6

end CFSG.LocalAnalysis.WeakClosure81
