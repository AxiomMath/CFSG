module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.lemma_1_9

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

universe uG uA

/-
**Kind**: Theorem
**Note**: Proposition 1.10
**Stmt**:
Let `G` be a finite nilpotent group.
Let `A` be an operator group on `G` with `gcd(|A|, |G|) = 1`.
Let `C = C_G(A)`.
If `C_G(C) ⊂ C`, then `A` acts trivially on `G`.
-/

public theorem CFSG.proposition_1_10 {G : Type uG} {A : Type uA} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (hnil : Group.IsNilpotent G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hC : Subgroup.centralizer (fixedPointSubgroup A G : Set G) ≤ fixedPointSubgroup A G) :
    ActsTrivially (A := A) (G := G) := by
  exact actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup
    (G := G) (A := A) hnil hcoprime hC


end
