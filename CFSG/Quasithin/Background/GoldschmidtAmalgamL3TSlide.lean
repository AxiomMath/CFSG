module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} {Γ : SimpleGraph V} {s : ℕ}

section Stab

variable (G : Type*) [Group G] [MulAction G V]

def Arc.stab (p : Arc Γ s) : Subgroup G :=
  ⨅ i : Fin (s + 1), MulAction.stabilizer G (p.vert i)

theorem Arc.mem_stab {p : Arc Γ s} {g : G} :
    g ∈ p.stab G ↔ ∀ i, i ≤ s → g • p.vert i = p.vert i := by
  simp only [Arc.stab, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h i hi => h ⟨i, by omega⟩, fun h i => h i (by omega)⟩

@[expose] def FixesExtensions (s : ℕ) (Γ : SimpleGraph V) : Prop :=
  ∀ (q : Arc Γ s) (w : V), Γ.Adj (q.vert s) w → ∀ g ∈ q.stab G, g • w = w

def Arc.FixedBy (X : Subgroup G) (q : Arc Γ s) : Prop :=
  ∀ i, i ≤ s → ∀ g ∈ X, g • q.vert i = q.vert i

variable {G}

theorem Arc.FixedBy.mem_stab {X : Subgroup G} {q : Arc Γ s} (h : q.FixedBy G X) {g : G}
    (hg : g ∈ X) : g ∈ q.stab G :=
  (Arc.mem_stab G).mpr fun i hi => h i hi g hg

theorem Arc.FixedBy.rev {X : Subgroup G} {q : Arc Γ s} (h : q.FixedBy G X) :
    q.rev.FixedBy G X := fun i hi g hg => by
  rw [Arc.rev_vert]
  exact h (s - i) (Nat.sub_le _ _) g hg

theorem Arc.FixedBy.fwd {X : Subgroup G} {q : Arc Γ s} (h : q.FixedBy G X) {w : V}
    (hw : Γ.Adj (q.vert s) w) (hw' : 1 ≤ s → w ≠ q.vert (s - 1))
    (hfix : ∀ g ∈ X, g • w = w) : (q.fwd w hw hw').FixedBy G X := by
  intro i hi g hg
  by_cases hlt : i < s
  · rw [Arc.fwd_vert_lt q w hw hw' hlt]
    exact h (i + 1) (by omega) g hg
  · have : i = s := by omega
    subst this
    rw [Arc.fwd_vert_last]
    exact hfix g hg

end Stab

section Slide

variable {G : Type*} [Group G] [MulAction G V]

theorem fixes_all_of_fixesExtensions (hconn : Γ.Connected)
    (hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v) (hs : 1 ≤ s)
    (hext : FixesExtensions G s Γ) (p : Arc Γ s) {g : G} (hg : g ∈ p.stab G) (v : V) :
    g • v = v := by
  set X : Subgroup G := p.stab G with hX
  have hp : p.FixedBy G X := fun i hi g hg => (Arc.mem_stab G).mp hg i hi
  let E : V → Prop := fun u => ∃ q : Arc Γ s, q.FixedBy G X ∧ q.vert s = u
  have hE0 : E (p.vert s) := ⟨p, hp, rfl⟩
  have hstep : ∀ u w, E u → Γ.Adj u w → E w := by
    rintro u w ⟨q, hq, rfl⟩ hadj
    have hwfix : ∀ g ∈ X, g • w = w := fun g hg => hext q w hadj g (hq.mem_stab hg)
    by_cases hw : w = q.vert (s - 1)
    · have hr : q.rev.FixedBy G X := hq.rev
      have h1 : q.rev.vert (s - 1) = q.vert 1 := by
        rw [Arc.rev_vert]
        congr 1
        omega
      obtain ⟨z, hz, hzne⟩ := hdeg (q.vert 0) (q.vert 1) (q.adj 0 (by omega))
      have hadj' : Γ.Adj (q.rev.vert s) z := by
        rw [Arc.rev_vert_last]
        exact hz
      have hzne' : 1 ≤ s → z ≠ q.rev.vert (s - 1) := fun _ => by
        rw [h1]
        exact hzne
      have hzfix : ∀ g ∈ X, g • z = z := fun g hg => hext q.rev z hadj' g (hr.mem_stab hg)
      refine ⟨(q.rev.fwd z hadj' hzne').rev, (hr.fwd hadj' hzne' hzfix).rev, ?_⟩
      rw [Arc.rev_vert_last, Arc.fwd_vert_zero q.rev hs z hadj' hzne', Arc.rev_vert, hw]
    · exact ⟨q.fwd w hadj (fun _ => hw), hq.fwd hadj (fun _ => hw) hwfix,
        Arc.fwd_vert_last _ _ _ _⟩
  have hall : ∀ u, E u := by
    intro u
    have hreach : Γ.Reachable (p.vert s) u := hconn.preconnected _ _
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact hE0
    | tail _ hadj ih => exact hstep _ _ ih hadj
  obtain ⟨q, hq, rfl⟩ := hall v
  exact hq s le_rfl g hg

end Slide

end CFSG.Quasithin.F6.GoldAmL3T
