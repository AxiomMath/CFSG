module

public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped commutatorElement

inductive CommTerm where
  | leaf (i : ℕ)
  | comm (a b : CommTerm)

namespace CommTerm

@[expose] def eval {G : Type*} [Group G] (f : ℕ → G) : CommTerm → G
  | leaf i => f i
  | comm a b => ⁅eval f a, eval f b⁆

@[expose] def depth : CommTerm → ℕ
  | leaf _ => 0
  | comm a b => min (depth a) (depth b) + 1

@[expose] def leaves : CommTerm → List ℕ
  | leaf i => [i]
  | comm a b => leaves a ++ leaves b

theorem derivedSeries_antitone {G : Type*} [Group G] {m n : ℕ} (h : m ≤ n) :
    derivedSeries G n ≤ derivedSeries G m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine le_trans ?_ ih
    rw [derivedSeries_succ]
    exact Subgroup.commutator_le_left _ _

theorem eval_mem {G : Type*} [Group G] (f : ℕ → G) :
    ∀ t : CommTerm, t.eval f ∈ derivedSeries G t.depth
  | leaf i => by
    rw [depth, derivedSeries_zero]
    exact Subgroup.mem_top _
  | comm a b => by
    rw [eval, depth, derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (derivedSeries_antitone (min_le_left _ _) (eval_mem f a))
      (derivedSeries_antitone (min_le_right _ _) (eval_mem f b))

@[expose] def evalT (n : ℕ) (F : ℕ → Table) : CommTerm → Table
  | leaf i => F i
  | comm a b =>
    compT n (evalT n F a) (compT n (evalT n F b)
      (compT n (invT n (evalT n F a)) (invT n (evalT n F b))))

@[expose] def invsOK (n : ℕ) (F : ℕ → Table) : CommTerm → Bool
  | leaf i => invOK n (F i) (invT n (F i))
  | comm a b => invsOK n F a && invsOK n F b &&
    invOK n (evalT n F (comm a b)) (invT n (evalT n F (comm a b)))

theorem invOK_of_invsOK {n : ℕ} {F : ℕ → Table} :
    ∀ {t : CommTerm}, invsOK n F t = true → invOK n (evalT n F t) (invT n (evalT n F t)) = true
  | leaf i, h => h
  | comm a b, h => by
    unfold invsOK at h
    simp only [Bool.and_eq_true] at h
    exact h.2

theorem rep_evalT {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {F : ℕ → Table}
    {f : ℕ → G} (hF : ∀ i, Rep n (F i) (f i)) :
    ∀ {t : CommTerm}, invsOK n F t = true → Rep n (evalT n F t) (eval f t)
  | leaf i, _ => hF i
  | comm a b, h => by
    unfold invsOK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, -⟩ := h
    have ra := rep_evalT hF ha
    have rb := rep_evalT hF hb
    have h' := Rep.compT ra (Rep.compT rb (Rep.compT (Rep.inv_of_invOK ra (invOK_of_invsOK ha))
      (Rep.inv_of_invOK rb (invOK_of_invsOK hb))))
    rw [eval, commutatorElement_def, mul_assoc, mul_assoc]
    exact h'

end CommTerm

end CFSG.Sporadic.FischerOddCore
