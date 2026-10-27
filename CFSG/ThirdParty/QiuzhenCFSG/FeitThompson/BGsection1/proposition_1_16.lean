module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_15

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Proposition 1.16
**Stmt**:
Let `A` be a noncyclic abelian `p`-group acting on the finite group `G`, with `gcd(p, |G|) = 1`.
(a) `G = ⟨ C_G(a) | a ∈ A, a ≠ 1 ⟩`.
(b) `G = ⟨ C_G(Y) | A/Y cyclic ⟩`.
-/

public theorem CFSG.proposition_1_16_a {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] (p : ℕ) [Fact p.Prime]
    (hG : Nat.Coprime p (Nat.card G)) [Fact (IsPGroup p A)] [MulDistribMulAction A G] (hncyc : ¬ IsCyclic A) :
    (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) = ⊤ := by
  exact iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := G) (A := A) (p := p) hG (hncyc := hncyc)

public theorem CFSG.proposition_1_16_b {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] (p : ℕ) [Fact p.Prime]
    (hG : Nat.Coprime p (Nat.card G)) [Fact (IsPGroup p A)] [MulDistribMulAction A G] (hncyc : ¬ IsCyclic A) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤ := by
  exact iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
    (G := G) (A := A) (p := p) hG (hncyc := hncyc)


end
