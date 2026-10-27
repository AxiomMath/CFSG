
module

public import CFSG.Sporadic.Schreier.J4SThreeBase

public import CFSG.Sporadic.Schreier.J4SThreeData
public import CFSG.Sporadic.Schreier.J4SOuterBase1
public import CFSG.Sporadic.Schreier.J4SInvolutionBase1
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFiveBase1
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import Certificates.Certificate2177
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.ComponentInitial CFSG.GroupActions MulAction

theorem q3gen_acts
    {i : ℕ} (hi : i < 2) : ActsBy (q3gen i) q3Cols[i + 1]! := by
  rw [← q3_gens i hi]
  exact actsBy_pow _ (word_conj_η_cols _)

theorem exists_q3Elt :
    ∀ k < 27, ∃ g ∈ Q3, ActsBy g q3Cols[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, Q3.one_mem, q3_zero ▸ actsBy_one⟩
    · obtain ⟨-, -, hpar, -⟩ := q3_all k hk
      obtain ⟨hp, hg, heq⟩ := hpar hpos
      obtain ⟨g, hgQ, hgA⟩ := ih _ hp (by omega)
      refine ⟨g * q3gen (q3Par[k]!)[1]!, Q3.mul_mem hgQ (q3gen_mem ⟨_, hg⟩), ?_⟩
      rw [heq]
      exact actsBy_mul hgA (q3gen_acts hg)

@[expose] def q3Elt
    (k : ℕ) : J := if h : k < 27 then Classical.choose (exists_q3Elt k h) else 1

theorem q3Elt_spec
    {k : ℕ} (hk : k < 27) : q3Elt k ∈ Q3 ∧ ActsBy (q3Elt k) q3Cols[k]! := by
  rw [q3Elt, dite_eq_left hk]
  exact Classical.choose_spec (exists_q3Elt k hk)

theorem q3Elt_injOn
    {k k' : ℕ} (hk : k < 27) (hk' : k' < 27) (h : q3Elt k = q3Elt k') :
    k = k' := by
  have h2 := (q3Elt_spec hk').2
  rw [← h] at h2
  have hc := cols_eq_of_actsBy (q3Elt_spec hk).2 h2 (q3_all k hk).1 (q3_all k' hk').1
    (q3_all k hk).2.1 (q3_all k' hk').2.1
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact q3_distinct k' hk' k hlt hc
  · exact q3_distinct k hk k' hlt hc.symm

section Generic

variable {G : Type*} [Group G]

end Generic

section Kernel

variable {G : Type*} [Group G] [Finite G] {X : Type*} [MulAction G X] [Finite X]
  [IsPretransitive G X] {H N : Subgroup G} {r : X}

end Kernel

section Core

variable {G : Type*} [Group G] [Finite G]

end Core

end CFSG.Sporadic.J4Schreier
