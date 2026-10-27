module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Stmts

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

structure Sec5Results (G : Type) [Group G] [Finite G] : Prop where
  s53 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt53 M V
  s54 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt54 M V
  s55 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt55 M V
  s55e : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt55e M V
  s56 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt56 M V
  s57 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt57 M V
  s58 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt58 M V
  s512 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt512 M V
  s513 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt513 M V
  i5a : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.StmtI5a M V
  i5b : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.StmtI5b M V

structure Sec6Hyp (M V : Subgroup G) : Prop where
  sec5 : Sec5Hyp M V
  ne : (sigmaSet M V).Nonempty
  res : Sec5Results G

theorem Sec6Hyp.conj (hS : Sec6Hyp M V) (a : G) :
    Sec6Hyp (conjSubgroup a M) (conjSubgroup a V) where
  sec5 := hS.sec5.conj a
  ne := by
    obtain ⟨U, hU⟩ := hS.ne
    refine ⟨conjSubgroup a U, ?_⟩
    rw [mem_sigmaSet_conjSubgroup_iff a,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    exact hU
  res := hS.res

abbrev lOf (M V : Subgroup G) (g : G) : Subgroup G := conjSubgroup g (Pc M V) ⊓ M

@[expose] def NoCommPair (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V, ⁅U, U'⁆ = ⊥ → ∃ p ∈ Pc M V, U' = conjSubgroup p U

end CFSG.RankThree.GF2n.Tim81
