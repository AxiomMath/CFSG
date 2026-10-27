module

public import Certificates.Data.SuzMixedCellInputs
public import CFSG.Certificates.CosetTableClosure

public section

namespace CFSG.Sporadic.SuzRecog.MixedCell

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration CFSG.Sporadic.SuzRecog.MixedCellData

@[expose] def winv (w : List ℕ) : List ℕ := w.reverse.map invCode

@[expose] def baseRels : List (List ℕ) :=
  relsH1 ++ relsH2 ++ relsA.map (fun p => p.1 ++ winv p.2) ++
    edge.map (fun p => [10] ++ p.1 ++ [11] ++ winv p.2) ++ [[10, 10] ++ winv sq]

@[expose] def cW (k : ℕ) : List ℕ := if k = 0 then cW0 else cW2

@[expose] def cpW (k : ℕ) : List ℕ := if k = 0 then cpW0 else cpW2

@[expose] def eW (k : ℕ) : List ℕ := if k = 0 then eW0 else eW2

@[expose] def deltaW (k : ℕ) : List (List ℕ) := if k = 0 then deltaW0 else deltaW2

@[expose] def cellRel (k i : ℕ) : List ℕ :=
  cW k ++ eW k ++ winv (cpW k) ++ winv ((deltaW k).getD i []) ++ [11]

@[expose] def collapseMem (cells : List (List ℕ)) : Prop :=
  ∀ (G : Type) [Group G] (gen : ℕ → G), (∀ x < 12, gen (invCode x) = (gen x)⁻¹) →
    (∀ r ∈ baseRels ++ cells, evalWord gen r = 1) →
    ∀ z ∈ [0, 2], gen z ∈ Subgroup.closure (gen '' {c | c ∈ [4, 6, 8]})

@[expose] def singleMem (n : ℕ) : Prop :=
  let t := singleChecks.getD n (0, 0, 0)
  collapseMem [cellRel t.1 t.2.1]

@[expose] def pairMem (n : ℕ) : Prop :=
  let t := pairChecks.getD n (0, 0, 0)
  collapseMem [cellRel 0 t.1, cellRel 2 t.2.1]

theorem singleChecks_length : singleChecks.length = 24 := rfl

theorem pairChecks_length : pairChecks.length = 12 := rfl

theorem collapseMem_of_singleMem (h : ∀ n < 24, singleMem n) :
    ∀ t ∈ singleChecks, collapseMem [cellRel t.1 t.2.1] := by
  intro t ht
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem ht
  have := h n (singleChecks_length ▸ hn)
  rwa [singleMem, List.getD_eq_getElem _ _ hn] at this

theorem collapseMem_of_pairMem (h : ∀ n < 12, pairMem n) :
    ∀ t ∈ pairChecks, collapseMem [cellRel 0 t.1, cellRel 2 t.2.1] := by
  intro t ht
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem ht
  have := h n (pairChecks_length ▸ hn)
  rwa [pairMem, List.getD_eq_getElem _ _ hn] at this

section Sound

variable {G : Type*} [Group G] {gen : ℕ → G}

theorem gen_invCode (hinv : ∀ i < 6, gen (2 * i + 1) = (gen (2 * i))⁻¹) {x : ℕ} (hx : x < 12) :
    gen (invCode x) = (gen x)⁻¹ := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' x
  · rw [invCode_two_mul, hinv i (by omega)]
  · rw [invCode_two_mul_add_one, hinv i (by omega), inv_inv]

theorem evalWord_winv (hinv : ∀ i < 6, gen (2 * i + 1) = (gen (2 * i))⁻¹) {w : List ℕ}
    (hw : ∀ c ∈ w, c < 12) : evalWord gen (winv w) = (evalWord gen w)⁻¹ := by
  induction w with
  | nil => simp [winv]
  | cons c w ih =>
    have ih' := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    rw [winv, List.reverse_cons, List.map_append, evalWord_append, ← winv, ih', List.map_singleton,
      evalWord_cons, evalWord_nil, mul_one, gen_invCode hinv (hw c List.mem_cons_self),
      evalWord_cons, mul_inv_rev]

end Sound

theorem mem_closure_of_collapseMem {G : Type} [Group G] {gen : ℕ → G}
    (hinv : ∀ i < 6, gen (2 * i + 1) = (gen (2 * i))⁻¹)
    {cells : List (List ℕ)} (hbase : ∀ r ∈ baseRels, evalWord gen r = 1)
    (hcells : ∀ r ∈ cells, evalWord gen r = 1) (h : collapseMem cells) :
    ∀ x < 4, gen x ∈ Subgroup.closure {gen 4, gen 6, gen 8} := by
  have hrels : ∀ r ∈ baseRels ++ cells, evalWord gen r = 1 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hbase r hr
    · exact hcells r hr
  have e : gen '' {c | c ∈ [4, 6, 8]} = {gen 4, gen 6, gen 8} := by
    ext g
    simp [eq_comm]
  have key := h G gen (fun x hx => gen_invCode hinv hx) hrels
  rw [e] at key
  have h0 := key 0 (by simp)
  have h2 := key 2 (by simp)
  intro x hx
  interval_cases x
  · exact h0
  · have e1 : gen 1 = (gen 0)⁻¹ := hinv 0 (by omega)
    rw [e1]
    exact Subgroup.inv_mem _ h0
  · exact h2
  · have e3 : gen 3 = (gen 2)⁻¹ := hinv 1 (by omega)
    rw [e3]
    exact Subgroup.inv_mem _ h2

end CFSG.Sporadic.SuzRecog.MixedCell
