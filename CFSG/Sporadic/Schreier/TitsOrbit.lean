module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def orbitLabelOK (n : ℕ) (gens : Array (Array ℕ)) (m : ℕ)
    (lab rep dep par glab : Array ℕ) : Bool :=
  allLt n (fun x => decide (lab[x]! < m)) &&
    allLt gens.size (fun i => allLt n fun x => lab[(gens[i]!)[x]!]! == lab[x]!) &&
    allLt m (fun c => decide (rep[c]! < n) && lab[rep[c]!]! == c && dep[rep[c]!]! == 0) &&
    allLt n (fun x => (dep[x]! == 0 && rep[lab[x]!]! == x) ||
      (decide (0 < dep[x]!) && decide (par[x]! < n) && dep[par[x]!]! + 1 == dep[x]! &&
        decide (glab[x]! < gens.size) && (gens[glab[x]!]!)[par[x]!]! == x))

@[expose] def orbitForest (n : ℕ) (gens : Array (Array ℕ)) (reps : Array ℕ) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut lab : Array ℕ := Array.replicate n reps.size
  let mut dep : Array ℕ := Array.replicate n 0
  let mut par : Array ℕ := Array.replicate n 0
  let mut glab : Array ℕ := Array.replicate n 0
  let mut queue : Array ℕ := #[]
  for c in [0:reps.size] do
    lab := lab.set! reps[c]! c
    queue := queue.push reps[c]!
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for i in [0:gens.size] do
        let y := (gens[i]!)[x]!
        if lab[y]! == reps.size then
          lab := lab.set! y lab[x]!
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          glab := glab.set! y i
          queue := queue.push y
  return (lab, dep, par, glab)

@[expose] def forestOK (n : ℕ) (gens : Array (Array ℕ)) (reps : Array ℕ) : Bool :=
  let F := orbitForest n gens reps
  orbitLabelOK n gens reps.size F.1 reps F.2.1 F.2.2.1 F.2.2.2

@[expose] def labelCount (n : ℕ) (lab : Array ℕ) (c : ℕ) : ℕ :=
  (List.range n).countP fun x => lab[x]! == c

variable {n : ℕ} {gens : Array (Array ℕ)} {m : ℕ} {lab rep dep par glab : Array ℕ}
  {gs : ℕ → Equiv.Perm (Fin n)}

@[expose] def genGroup (gens : Array (Array ℕ)) (gs : ℕ → Equiv.Perm (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure (gs '' {i | i < gens.size})

section Sound

variable (h : orbitLabelOK n gens m lab rep dep par glab = true)
  (hrep : ∀ i < gens.size, Rep n gens[i]! (gs i))
include h hrep

omit hrep in
theorem orbitLabelOK_parts :
    (∀ x < n, lab[x]! < m) ∧ (∀ i < gens.size, ∀ x < n, lab[(gens[i]!)[x]!]! = lab[x]!) ∧
    (∀ c < m, rep[c]! < n ∧ lab[rep[c]!]! = c ∧ dep[rep[c]!]! = 0) ∧
    ∀ x < n, (dep[x]! = 0 ∧ rep[lab[x]!]! = x) ∨
      (0 < dep[x]! ∧ par[x]! < n ∧ dep[par[x]!]! + 1 = dep[x]! ∧ glab[x]! < gens.size ∧
        (gens[glab[x]!]!)[par[x]!]! = x) := by
  simp only [orbitLabelOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun x hx => of_decide_eq_true (allLt_spec h1 hx), fun i hi x hx => ?_,
    fun c hc => ?_, fun x hx => ?_⟩
  · have := allLt_spec (allLt_spec h2 hi) hx
    simpa using this
  · have := allLt_spec h3 hc
    simpa [and_assoc] using this
  · have := allLt_spec h4 hx
    simpa [and_assoc] using this

theorem lab_smul (g : Equiv.Perm (Fin n)) (hg : g ∈ genGroup gens gs) (x : Fin n) :
    lab[((g x : Fin n) : ℕ)]! = lab[(x : ℕ)]! := by
  have hgen : ∀ i < gens.size, ∀ y : Fin n, lab[((gs i y : Fin n) : ℕ)]! = lab[(y : ℕ)]! := by
    intro i hi y
    rw [← (hrep i hi) y]
    exact (orbitLabelOK_parts h).2.1 i hi y y.2
  induction hg using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact hgen i hi x
  | one => rfl
  | mul g g' _ _ ih ih' => rw [Equiv.Perm.mul_apply, ih, ih']
  | inv g _ ih =>
    have := ih (g⁻¹ x)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact this.symm

theorem mem_orbit_rep (x : Fin n) :
    ∃ g ∈ genGroup gens gs,
      g (⟨rep[lab[(x : ℕ)]!]! % n, Nat.mod_lt _ (Fin.pos x)⟩ : Fin n) = x := by
  obtain ⟨-, hinv, hroot, htree⟩ := orbitLabelOK_parts h
  have key : ∀ d, ∀ x : Fin n, dep[(x : ℕ)]! = d → ∃ g ∈ genGroup gens gs,
      g (⟨rep[lab[(x : ℕ)]!]! % n, Nat.mod_lt _ (Fin.pos x)⟩ : Fin n) = x := by
    intro d
    induction d with
    | zero =>
      intro x hx
      rcases htree x x.2 with ⟨-, hr⟩ | ⟨hpos, -⟩
      · refine ⟨1, one_mem _, Fin.ext ?_⟩
        rw [Equiv.Perm.one_apply]
        show rep[lab[(x : ℕ)]!]! % n = x
        rw [hr, Nat.mod_eq_of_lt x.2]
      · omega
    | succ d ih =>
      intro x hx
      rcases htree x x.2 with ⟨h0, -⟩ | ⟨-, hp, hdep, hgl, hedge⟩
      · omega
      · set y : Fin n := ⟨par[(x : ℕ)]!, hp⟩
        have hy : dep[(y : ℕ)]! = d := by
          show dep[par[(x : ℕ)]!]! = d
          omega
        obtain ⟨g, hg, hgy⟩ := ih y hy
        have hgen : gs glab[(x : ℕ)]! y = x := by
          apply Fin.ext
          rw [← (hrep _ hgl) y]
          exact hedge
        have hlab : lab[(y : ℕ)]! = lab[(x : ℕ)]! := by
          rw [← hgen]
          exact (lab_smul h hrep _ (Subgroup.subset_closure ⟨_, hgl, rfl⟩) y).symm
        refine ⟨gs glab[(x : ℕ)]! * g, mul_mem (Subgroup.subset_closure ⟨_, hgl, rfl⟩) hg, ?_⟩
        rw [Equiv.Perm.mul_apply]
        have e : (⟨rep[lab[(x : ℕ)]!]! % n, Nat.mod_lt _ (Fin.pos x)⟩ : Fin n) =
            ⟨rep[lab[(y : ℕ)]!]! % n, Nat.mod_lt _ (Fin.pos y)⟩ := by
          rw [hlab]
        rw [e, hgy, hgen]
  exact key _ x rfl

theorem orbit_eq_label {c : ℕ} (hc : c < m) :
    MulAction.orbit (genGroup gens gs)
        (⟨rep[c]! % n, Nat.mod_lt _ (by have := ((orbitLabelOK_parts h).2.2.1 c hc).1; omega)⟩ :
          Fin n) =
      {x : Fin n | lab[(x : ℕ)]! = c} := by
  obtain ⟨-, -, hroot, -⟩ := orbitLabelOK_parts h
  obtain ⟨hrn, hrl, -⟩ := hroot c hc
  ext x
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    show lab[((g _ : Fin n) : ℕ)]! = c
    rw [lab_smul h hrep g hg]
    simp only [Nat.mod_eq_of_lt hrn]
    exact hrl
  · intro hx
    obtain ⟨g, hg, hgx⟩ := mem_orbit_rep h hrep x
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [← hgx]
    simp only [hx]
    rfl

end Sound

theorem pretransitive_of_orbitLabelOK (h : orbitLabelOK n gens 1 lab rep dep par glab = true)
    (hrep : ∀ i < gens.size, Rep n gens[i]! (gs i)) :
    MulAction.IsPretransitive (genGroup gens gs) (Fin n) := by
  obtain ⟨hlab, -⟩ := orbitLabelOK_parts h
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg, hgx⟩ := mem_orbit_rep h hrep x
  obtain ⟨g', hg', hgy⟩ := mem_orbit_rep h hrep y
  have hx : lab[(x : ℕ)]! = 0 := by have := hlab x x.2; omega
  have hy : lab[(y : ℕ)]! = 0 := by have := hlab y y.2; omega
  rw [hx] at hgx
  rw [hy] at hgy
  refine ⟨⟨g' * g⁻¹, mul_mem hg' (inv_mem hg)⟩, ?_⟩
  show (g' * g⁻¹) x = y
  rw [← hgx, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply g⁻¹, inv_mul_cancel,
    Equiv.Perm.one_apply]
  exact hgy

theorem ncard_label (c : ℕ) :
    Set.ncard {x : Fin n | lab[(x : ℕ)]! = c} = labelCount n lab c := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, labelCount,
    ← List.map_coe_finRange_eq_range,
    List.countP_map, Finset.card_def, Finset.filter_val, Finset.val_univ_fin, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]
  congr 1

end CFSG.Sporadic.Schreier.Tits
