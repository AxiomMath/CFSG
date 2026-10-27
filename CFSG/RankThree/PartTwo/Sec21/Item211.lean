module

public import CFSG.RankThree.PartTwo.Sec13.Steps
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def IsTypeCOnBarSL (E L : Subgroup G) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : Sec4.PiField π p f K)
    (_ : Sec4.ModThree π (p ^ f))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Sec4.slPi π 3 (p ^ f) K)
    (D : Subgroup (GL (Fin 3) K)), Sec4.IsTypeC π (p ^ f) K D ∧
      (∀ τ ∈ Sec4.autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
        ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹) ∧
      ∀ y ∈ D, ∃ τ ∈ Sec4.autThetaQuot E L, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
        ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹

@[expose] def Case211 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  (Sec4.IsHeisCentral ↥(Sec13.lBarA c L A) (lBar L) ∧
    Sec4.IsTripleCover (lBar L) NativeSporadic.M22 ∧ Nat.card A = 3 ^ 3 ∧
    CFSG.Assembly.IsElemAbelian 3 (starOf A L) ∧ Nat.card (starOf A L) = 9) ∨
  (Nonempty (lBar L ≃* NativeSporadic.M22) ∧ Nat.card A = 3 ^ 3 ∧
    Nonempty (starOf A L ≃* QuaternionGroup 2)) ∨
  ((Nonempty (lBar L ≃* NativeSporadic.M23) ∨ Nonempty (lBar L ≃* NativeSporadic.HS)) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* CFSG.Open.SemidihedralGroup 4)) ∨
  ((Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.He)) ∧
    Nat.card A = 3 ^ 3 ∧
    (Nonempty (starOf A L ≃* DihedralGroup 6) ∨ Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3)))) ∨
  (Nonempty (lBar L ≃* NativeSporadic.J2) ∧ Nat.card A = 3 ^ 3 ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
  ((Nonempty (lBar L ≃* NativeSporadic.Ru) ∨ Nonempty (lBar L ≃* NativeSporadic.J4)) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3))) ∨
  ((∃ n : ℕ, 0 < n ∧ Even n ∧
      ((Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) ∧ Sec4.IsTypeCOn A L) ∨
        (Nonempty (lBar L ≃* SL3 n) ∧ IsTypeCOnBarSL A L))) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
  ((∃ n : ℕ, 0 < n ∧ Even n ∧
      (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
        ChevalleyExceptionalModel (lBar L) .trialityD4 2 n)) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* DihedralGroup 6)) ∨
  (((∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (lBar L ≃* projSU 4 2 n))) ∨
      Nonempty (lBar L ≃* projSU 5 2 2)) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
  ((∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n)) ∧ Nat.card A = 3 ^ 4 ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))) ∨
  ((Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) ∧
    Nat.card A = 3 ^ 4 ∧
    Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))) ∨
  ((StatedClassicalModel (lBar L) .PSL 4 2 1 ∨ StatedClassicalModel (lBar L) .PSL 5 2 1) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
  (StatedClassicalModel (lBar L) .PSp 3 2 1 ∧ Nat.card A = 3 ^ 4 ∧
    Nonempty (starOf A L ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def Item211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Case211 A c L

end CFSG.RankThree.PartTwo.Sec21
