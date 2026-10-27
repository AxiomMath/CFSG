module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.QuasithinUnique.A6Facts Subgroup

@[expose] def invCodes (n : ℕ) (c d : List ℕ) : Bool :=
  (List.range n).all fun i => decide (c.getD i 0 < n) && decide (d.getD i 0 < n) &&
    d.getD (c.getD i 0) 0 == i && c.getD (d.getD i 0) 0 == i

theorem invCodes_spec {n : ℕ} {c d : List ℕ} (h : invCodes n c d = true) {i : ℕ} (hi : i < n) :
    c.getD i 0 < n ∧ d.getD i 0 < n ∧ d.getD (c.getD i 0) 0 = i ∧ c.getD (d.getD i 0) 0 = i := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

@[expose] def permOfCodes (n : ℕ) (c d : List ℕ) (h : invCodes n c d = true) :
    Equiv.Perm (Fin n) where
  toFun i := ⟨c.getD i 0, (invCodes_spec h i.2).1⟩
  invFun i := ⟨d.getD i 0, (invCodes_spec h i.2).2.1⟩
  left_inv i := Fin.ext (invCodes_spec h i.2).2.2.1
  right_inv i := Fin.ext (invCodes_spec h i.2).2.2.2

variable {n : ℕ}

theorem codeN_mem_of_tbl {gens : List (Equiv.Perm (Fin n))} {gc E T : List (List ℕ)}
    (hgc : gens.map (codeN n) = gc) (h1 : List.range n ∈ E)
    (h : CFSG.QuasithinUnique.A6Facts.Core.tblCheckC (List.range n) gc E T = true) :
    ∀ x ∈ closure {g | g ∈ gens}, codeN n x ∈ E := by
  intro x hx
  have hsub : (closure {g | g ∈ gens}).toSubmonoid = Submonoid.closure {g | g ∈ gens} :=
    Subgroup.closure_toSubmonoid_of_finite
  have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by rw [← hsub]; exact hx
  refine Submonoid.closure_induction_right (motive := fun m _ => codeN n m ∈ E) ?_ ?_ hx'
  · rw [codeN_one]
    exact h1
  · intro m _ y hy ih
    rw [codeN_mul]
    refine mem_of_tblCheckCN h _ ih _ ?_
    rw [← hgc]
    exact List.mem_map.mpr ⟨y, hy, rfl⟩

theorem card_closure_le_of_tbl {gens : List (Equiv.Perm (Fin n))} {gc E T : List (List ℕ)}
    (hgc : gens.map (codeN n) = gc) (h1 : List.range n ∈ E)
    (h : CFSG.QuasithinUnique.A6Facts.Core.tblCheckC (List.range n) gc E T = true) :
    Nat.card (closure {g | g ∈ gens}) ≤ E.length := by
  classical
  let f : closure {g | g ∈ gens} → ↥E.toFinset := fun x =>
    ⟨codeN n x, List.mem_toFinset.mpr (codeN_mem_of_tbl hgc h1 h x x.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (codeN_injective (congrArg Subtype.val hxy))
  have h2 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥E.toFinset), Fintype.card_coe] at h2
  exact h2.trans (List.toFinset_card_le E)

theorem card_closure_le_of_cosets {Y : Type*} [Group Y] [Finite Y] (M : Subgroup Y) (gens : Set Y)
    (reps : List Y) (h1 : (1 : Y) ∈ reps)
    (hcl : ∀ r ∈ reps, ∀ g ∈ gens, ∃ r' ∈ reps, r * g * r'⁻¹ ∈ M) :
    Nat.card (closure gens) ≤ Nat.card M * reps.length := by
  classical
  have hsub : (closure gens).toSubmonoid = Submonoid.closure gens :=
    Subgroup.closure_toSubmonoid_of_finite
  have hcov : ∀ x ∈ closure gens, ∃ r ∈ reps, x * r⁻¹ ∈ M := by
    intro x hx
    have hx' : x ∈ Submonoid.closure gens := by rw [← hsub]; exact hx
    refine Submonoid.closure_induction_right (motive := fun m _ => ∃ r ∈ reps, m * r⁻¹ ∈ M)
      ⟨1, h1, by simp⟩ ?_ hx'
    rintro m _ g hg ⟨r, hr, hmr⟩
    obtain ⟨r', hr', hrg⟩ := hcl r hr g hg
    refine ⟨r', hr', ?_⟩
    have e : m * g * r'⁻¹ = (m * r⁻¹) * (r * g * r'⁻¹) := by group
    rw [e]
    exact M.mul_mem hmr hrg
  let F : M × Fin reps.length → Y := fun p => (p.1 : Y) * reps.get p.2
  have hsubset : ((closure gens : Subgroup Y) : Set Y) ⊆ Set.range F := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := hcov x hx
    obtain ⟨i, rfl⟩ := List.get_of_mem hr
    exact ⟨(⟨x * (reps.get i)⁻¹, hxr⟩, i), by simp [F]⟩
  have h2 : Nat.card ((closure gens : Subgroup Y) : Set Y) ≤ Nat.card (Set.range F) :=
    Nat.card_mono (Set.toFinite _) hsubset
  have h3 := Finite.card_range_le F
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin reps.length), Fintype.card_fin] at h3
  exact h2.trans h3

end CFSG.LocalAnalysis.WeakClosure81.NF3C
