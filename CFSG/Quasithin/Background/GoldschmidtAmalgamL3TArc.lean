module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

public section

namespace CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*}

structure Arc (Γ : SimpleGraph V) (s : ℕ) where
  vert : ℕ → V
  adj : ∀ i, i < s → Γ.Adj (vert i) (vert (i + 1))
  nb : ∀ i, i + 2 ≤ s → vert i ≠ vert (i + 2)

namespace Arc

variable {Γ : SimpleGraph V} {s : ℕ}

def rev (p : Arc Γ s) : Arc Γ s where
  vert i := p.vert (s - i)
  adj i hi := by
    have h : s - i = (s - (i + 1)) + 1 := by omega
    rw [h]
    exact (p.adj (s - (i + 1)) (by omega)).symm
  nb i hi := by
    have h : s - i = (s - (i + 2)) + 2 := by omega
    rw [h]
    exact (p.nb (s - (i + 2)) (by omega)).symm

theorem rev_vert (p : Arc Γ s) (i : ℕ) : p.rev.vert i = p.vert (s - i) := by
  simp [rev]

@[simp] theorem rev_vert_zero (p : Arc Γ s) : p.rev.vert 0 = p.vert s := by
  simp [rev_vert]

@[simp] theorem rev_vert_last (p : Arc Γ s) : p.rev.vert s = p.vert 0 := by
  simp [rev_vert]

def fwd (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w) (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) :
    Arc Γ s where
  vert i := if i < s then p.vert (i + 1) else w
  adj i hi := by
    by_cases h : i + 1 < s
    · simp only [hi, h, ↓reduceIte]
      exact p.adj (i + 1) h
    · have h' : i + 1 = s := by omega
      simp only [hi, h, ↓reduceIte]
      rw [h']
      exact hw
  nb i hi := by
    have hi' : i < s := by omega
    by_cases h : i + 2 < s
    · simp only [hi', h, ↓reduceIte]
      exact p.nb (i + 1) (by omega)
    · have hs : 1 ≤ s := by omega
      simp only [hi', h, ↓reduceIte]
      have e : i + 1 = s - 1 := by omega
      rw [e]
      exact (hw' hs).symm

@[simp] theorem fwd_vert_last (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : (p.fwd w hw hw').vert s = w := by
  simp [fwd]

theorem fwd_vert_zero (p : Arc Γ s) (hs : 1 ≤ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : (p.fwd w hw hw').vert 0 = p.vert 1 := by
  simp [fwd, show 0 < s by omega]

theorem fwd_vert_lt (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) {i : ℕ} (hi : i < s) :
    (p.fwd w hw hw').vert i = p.vert (i + 1) := by
  simp [fwd, hi]

def snoc (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w) (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) :
    Arc Γ (s + 1) where
  vert i := if i ≤ s then p.vert i else w
  adj i hi := by
    by_cases h : i + 1 ≤ s
    · simp only [show i ≤ s by omega, h, ↓reduceIte]
      exact p.adj i (by omega)
    · have h' : i = s := by omega
      subst h'
      simp only [le_refl, h, ↓reduceIte]
      exact hw
  nb i hi := by
    by_cases h : i + 2 ≤ s
    · simp only [show i ≤ s by omega, h, ↓reduceIte]
      exact p.nb i h
    · have h' : i = s - 1 := by omega
      have hs : 1 ≤ s := by omega
      have h'' : i + 2 = s + 1 := by omega
      simp only [show i ≤ s by omega, h, ↓reduceIte]
      rw [h']
      exact (hw' hs).symm

theorem snoc_vert_zero (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : (p.snoc w hw hw').vert 0 = p.vert 0 := by
  simp [snoc]

end Arc

theorem exists_arc {Γ : SimpleGraph V} (hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v)
    {u v : V} (huv : Γ.Adj u v) : ∀ s : ℕ, ∃ p : Arc Γ s, p.vert 0 = u
  | 0 => ⟨⟨fun _ => u, fun i hi => by omega, fun i hi => by omega⟩, rfl⟩
  | s + 1 => by
    obtain ⟨p, hp⟩ := exists_arc hdeg huv s
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact ⟨p.snoc v (by rw [hp]; exact huv) (fun h => by omega), by rw [Arc.snoc_vert_zero, hp]⟩
    · obtain ⟨w, hw, hwne⟩ := hdeg (p.vert s) (p.vert (s - 1)) (by
        have := (p.adj (s - 1) (by omega)).symm
        rwa [show s - 1 + 1 = s by omega] at this)
      exact ⟨p.snoc w hw (fun _ => hwne), by rw [Arc.snoc_vert_zero, hp]⟩

end CFSG.Quasithin.F6.GoldAmL3T
