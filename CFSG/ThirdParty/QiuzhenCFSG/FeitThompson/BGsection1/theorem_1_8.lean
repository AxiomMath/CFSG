module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.lemma_1_7

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Theorem 1.8
**Stmt**:
Let $R$ be a $p$-group.
Let $A$ be an operator group on $R$ with $gcd(|A|, |R|) = 1$.
If $A$ centralizes $R/\Phi(R)$, then $A$ centralizes $R$.
-/

public theorem CFSG.theorem_1_8 {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [MulDistribMulAction A R]
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card R))
    (hquot :
      let : MulDistribMulAction A (R ⧸ frattini R) :=
        quotientMulDistribMulAction (A := A) (G := R) (frattini R)
          (isInvariant_of_characteristic (A := A) (G := R) (frattini R))
      ActsTrivially (A := A) (G := R ⧸ frattini R)) :
    ActsTrivially (A := A) (G := R) := by
  have hnilR : Group.IsNilpotent R :=
    IsPGroup.isNilpotent (p := p) (G := R) (h := (Fact.out : IsPGroup p R))
  let : Group.IsNilpotent R := hnilR
  have hsolvR : Group.IsSolvable R := by infer_instance
  have hsup :
      fixedPointSubgroup A R ⊔ commutatorAction (A := A) (G := R) = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := R) (A := A) hsolvR hcoprime
  simpa using
    actsTrivially_of_trivial_quotient_frattini_of_sup_eq_top
      (R := R) (A := A) (p := p) hsup hquot


end
