module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupFaithfulIrreducibleAction

namespace CFSG
end CFSG
open CFSG

/-!
# Minimal normal p-subgroups and their faithful conjugation quotient

This is equation (6.3) in the minimal-counterexample proof of Glauberman
Lemma 6.3.  If `K` is a nontrivial minimal normal p-subgroup of `Q`, then the
p-core of `Q/C_Q(K)` is trivial.
-/

namespace CFSG.Glauberman

universe u

public theorem pCore_quotient_centralizer_eq_bot_of_minimalNormal_pSubgroup
    {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q] [Finite Q]
    (K : Subgroup Q) [K.Normal] [IsMinimalNormal K]
    (hKne : K ≠ ⊥) (hKp : IsPGroup p K) :
    pCore p (Q ⧸ Subgroup.centralizer (K : Set Q)) = ⊥ := by
  classical
  let : IsElementaryAbelian p K :=
    minimalNormal_pSubgroup_isElementaryAbelian K hKne hKp
  let : IsMulCommutative K :=
    (inferInstance : IsElementaryAbelian p K).toIsMulCommutative
  let : CommGroup K := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive K) := Additive.addCommGroup
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hKne
  let : Nontrivial (Additive K) := inferInstance
  let P : Subgroup (Q ⧸ Subgroup.centralizer (K : Set Q)) :=
    pCore p (Q ⧸ Subgroup.centralizer (K : Set Q))
  by_contra hPne
  have hPne' : P ≠ ⊥ := by simpa [P] using hPne
  have hPp : IsPGroup p P := by
    simpa [P] using
      (pCore_isPGroup (G := Q ⧸ Subgroup.centralizer (K : Set Q)) (p := p))
  obtain ⟨φ, hφinj, hirr, _hφapply⟩ :=
    exists_minimalNormal_pSubgroup_faithful_irreducible_action
      (p := p) K hKne hKp
  have hKtagp : IsPGroup p (Multiplicative (Additive K)) :=
    hKp.of_equiv (MulEquiv.multiplicativeAdditive K).symm
  have hfixedBot : fixedPoints (V := Additive K) φ P = ⊥ :=
    fixedPoints_eq_bot_of_irreducible_of_normal_pSubgroup
      (V := Additive K)
      (G := Q ⧸ Subgroup.centralizer (K : Set Q))
      φ hφinj hKtagp P hPp hPne' hirr
  have hfixedNe : fixedPoints (V := Additive K) φ P ≠ ⊥ :=
    (bot_lt_fixedPoints (V := Additive K)
      (G := Q ⧸ Subgroup.centralizer (K : Set Q)) φ hKtagp P hPp).ne'
  exact hfixedNe hfixedBot

end CFSG.Glauberman
