module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def orbitPartOK (n : ℕ) (gens : Array (Array ℕ)) (lab roots depth par gl : Array ℕ) :
    Bool :=
  (allLt n fun x =>
    (allLt gens.size fun k => decide ((gens[k]!)[x]! < n) && lab[(gens[k]!)[x]!]! == lab[x]!) &&
    (if depth[x]! == 0 then roots[lab[x]!]! == x
      else decide (par[x]! < n) && decide (depth[par[x]!]! < depth[x]!) &&
        decide (gl[x]! < gens.size) && (gens[gl[x]!]!)[par[x]!]! == x)) &&
  allLt roots.size fun k => decide (roots[k]! < n) && lab[roots[k]!]! == k

@[expose] def orbitForest (n : ℕ) (gens : Array (Array ℕ)) (roots : Array ℕ) :
    Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut depth : Array ℕ := Array.replicate n 0
  let mut par : Array ℕ := Array.replicate n 0
  let mut gl : Array ℕ := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array ℕ := #[]
  for r in roots do
    if r < n && !seen[r]! then
      seen := seen.set! r true
      queue := queue.push r
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:gens.size] do
        let y := (gens[k]!)[x]!
        if y < n && !seen[y]! then
          seen := seen.set! y true
          depth := depth.set! y (depth[x]! + 1)
          par := par.set! y x
          gl := gl.set! y k
          queue := queue.push y
  return (depth, par, gl)

variable {n : ℕ} {gens : Array (Array ℕ)} {Gs : ℕ → Equiv.Perm (Fin n)}
  {lab roots depth par gl : Array ℕ}

@[expose] noncomputable def genSubgroup (n : ℕ) (k : ℕ) (Gs : ℕ → Equiv.Perm (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ i < k, Gs i = g}

theorem orbitPartOK_spec (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (h : orbitPartOK n gens lab roots depth par gl = true) :
    (∀ k < gens.size, ∀ x : Fin n, lab[((Gs k) x : ℕ)]! = lab[(x : ℕ)]!) ∧
    (∀ x : Fin n, depth[(x : ℕ)]! = 0 → roots[lab[(x : ℕ)]!]! = x) ∧
    (∀ x : Fin n, depth[(x : ℕ)]! ≠ 0 → ∃ (p : Fin n), (p : ℕ) = par[(x : ℕ)]! ∧
      depth[(p : ℕ)]! < depth[(x : ℕ)]! ∧ gl[(x : ℕ)]! < gens.size ∧ (Gs gl[(x : ℕ)]!) p = x) ∧
    (∀ k < roots.size, roots[k]! < n ∧ lab[roots[k]!]! = k) := by
  simp only [orbitPartOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun k hk x => ?_, fun x hx => ?_, fun x hx => ?_, fun k hk => ?_⟩
  · have hx := allLt_spec h1 x.2
    rw [Bool.and_eq_true] at hx
    have := allLt_spec hx.1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rw [← (hrep k hk).apply x.2]
    exact this.2
  · have hx' := allLt_spec h1 x.2
    rw [Bool.and_eq_true] at hx'
    have := hx'.2
    rw [hx] at this
    simpa using this
  · have hx' := allLt_spec h1 x.2
    rw [Bool.and_eq_true] at hx'
    have := hx'.2
    simp only [beq_iff_eq, hx, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨hp, hd⟩, hg⟩, he⟩ := this
    refine ⟨⟨par[(x : ℕ)]!, hp⟩, rfl, hd, hg, Fin.ext ?_⟩
    rw [← (hrep _ hg).apply hp]
    exact he
  · have := allLt_spec h2 hk
    simpa using this

theorem orbit_eq_label (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (h : orbitPartOK n gens lab roots depth par gl = true) (x : Fin n) :
    MulAction.orbit (genSubgroup n gens.size Gs) x =
      {y : Fin n | lab[(y : ℕ)]! = lab[(x : ℕ)]!} := by
  obtain ⟨hinv, h0, hpar, hr⟩ := orbitPartOK_spec hrep h
  set G := genSubgroup n gens.size Gs
  have hG : ∀ g ∈ G, ∀ y : Fin n, lab[((g : Equiv.Perm (Fin n)) y : ℕ)]! = lab[(y : ℕ)]! := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      exact hinv k hk
    | one => intro y; rfl
    | mul g g' _ _ ihg ihg' => intro y; rw [Equiv.Perm.mul_apply, ihg, ihg']
    | inv g _ ihg =>
      intro y
      have e : g (g⁻¹ y) = y := (Equiv.eq_symm_apply g).mp rfl
      rw [← ihg (g⁻¹ y), e]
  have hroot : ∀ y : Fin n, ∃ r : Fin n, (r : ℕ) = roots[lab[(y : ℕ)]!]! ∧
      y ∈ MulAction.orbit G r := by
    intro y
    induction hd : depth[(y : ℕ)]! using Nat.strong_induction_on generalizing y with
    | _ d ih =>
      by_cases hd0 : depth[(y : ℕ)]! = 0
      · exact ⟨y, (h0 y hd0).symm, MulAction.mem_orbit_self y⟩
      · obtain ⟨p, -, hpd, hgl, hpy⟩ := hpar y hd0
        obtain ⟨r, hr', hp⟩ := ih _ (hd ▸ hpd) p rfl
        have hlab : lab[(p : ℕ)]! = lab[(y : ℕ)]! := by
          rw [← hpy, hinv _ hgl p]
        refine ⟨r, by rw [hr', hlab], ?_⟩
        obtain ⟨⟨g, hg⟩, rfl⟩ := hp
        refine ⟨⟨Gs gl[(y : ℕ)]! * g, G.mul_mem (Subgroup.subset_closure ?_) hg⟩, ?_⟩
        · exact ⟨_, hgl, rfl⟩
        · show (Gs gl[(y : ℕ)]! * g) r = y
          exact hpy
  ext y
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact hG g hg x
  · intro hy
    obtain ⟨r, hr1, hx⟩ := hroot x
    obtain ⟨r', hr2, hy'⟩ := hroot y
    have hyx : lab[(y : ℕ)]! = lab[(x : ℕ)]! := hy
    have hrr : r = r' := Fin.ext (by rw [hr1, hr2, hyx])
    subst hrr
    rw [MulAction.orbit_eq_iff.2 hx]
    exact hy'

end CFSG.Sporadic.RuSchreier
