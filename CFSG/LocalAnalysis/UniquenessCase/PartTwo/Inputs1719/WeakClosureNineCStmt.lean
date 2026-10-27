module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {X : Type} [Group X]

structure FiveUseC (Tb A H R : Subgroup X) : Prop where
  le : A ≤ H
  R_le : R ≤ H
  R_norm : H ≤ normalizer (R : Set X)
  R_le_T : R ≤ Tb
  idx : R.relIndex A = 2
  core : coreIn (Tb ⊓ centralizer (A : Set X)) Tb ≤ H
  cY : ∀ Y : Subgroup X, Y ≤ H → H ≤ normalizer (Y : Set X) →
    (∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ R) → ∀ y ∈ Y, ∃ k : ℕ, y ^ 3 ^ k ∈ R
  cP : ∀ P : Subgroup X, P ≤ H → H ≤ normalizer (P : Set X) → IsPGroup 2 P → P ≤ R
  cD : ∀ D : Subgroup X, D ≤ H → H ≤ normalizer (D : Set X) → A ≤ D → ∃ y ∈ D, orderOf y = 3
  pair : ∃ n ∈ H, IsPGroup 2 ↥(A ⊔ A.map (MulAut.conj n).toMonoidHom) ∧
    ∃ a ∈ A, ∃ b ∈ A, a * (n * b * n⁻¹) ≠ n * b * n⁻¹ * a

@[expose] def KillStmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb Tb : Subgroup X) (B : Type) [Group B] [Finite B]
    (π : ↥(tcN1 Lb Tb) →* B) (Es : Subgroup B), TCBar Lb Tb π Es →
    ∀ A : Subgroup X, A ≤ tcT1 Lb Tb → IsElemAbelian 2 A → Nat.card (barSub π A) = 2 →
    (∀ x ∈ barSub π A, x ≠ 1 → PairProp914 (barSub π Lb) x) →
    ∃ H R : Subgroup X, FiveUseC Tb A H R

@[expose] def OrbitStmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb Tb : Subgroup X) (B : Type) [Group B] [Finite B]
    (π : ↥(tcN1 Lb Tb) →* B) (Es : Subgroup B), TCBar Lb Tb π Es →
    ∀ A : Subgroup X, A ≤ Tb → IsElemAbelian 2 A → ¬ A ≤ normalizer (Lb : Set X) →
    ∀ (H Xh : Subgroup B) (p : ℕ),
      MovWit914 (barSub π Lb) (barSub π Tb) (barSub π (A ⊓ normalizer (Lb : Set X))) H Xh p →
    ∀ F : Subgroup X, F ≤ tcT1 Lb Tb → Tb ≤ normalizer (F : Set X) →
      barSub π F ≤ normalizer (H : Set B) →
      (∀ f ∈ barSub π F, ∀ x ∈ Xh, f * x * f⁻¹ * x⁻¹ ∈ pCoreOf 2 H) →
    ∃ K Y : Subgroup X, TwoPTwoIrred K (K ⊓ Tb) Y p ∧ A ≤ K ∧ ¬ A ≤ pCoreOf 2 K ∧
      F ≤ pCoreOf 2 K ∧
      (p = 3 ∨ ∀ J : Subgroup X, Tb ≤ normalizer (J : Set X) → Y ≤ J → ∃ y ∈ J, orderOf y = 3)

end CFSG.LocalAnalysis.WeakClosure81

