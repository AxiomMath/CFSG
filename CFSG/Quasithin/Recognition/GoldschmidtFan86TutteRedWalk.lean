module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc

public section

namespace CFSG.Quasithin.Fan86.Tutte.Red

open CFSG.Quasithin.F6.GoldAmL3T

variable {W : Type} {Γ : SimpleGraph W}

@[expose] def truncArc {s : ℕ} (p : Arc Γ (s + 1)) : Arc Γ s where
  vert := p.vert
  adj i hi := p.adj i (by omega)
  nb i hi := p.nb i (by omega)

@[simp] theorem truncArc_vert {s : ℕ} (p : Arc Γ (s + 1)) : (truncArc p).vert = p.vert := rfl

@[expose] def snocArc {s : ℕ} (p : Arc Γ s) (w : W) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : Arc Γ (s + 1) where
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

theorem snocArc_vert_le {s : ℕ} (p : Arc Γ s) (w : W) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) {i : ℕ} (hi : i ≤ s) :
    (snocArc p w hw hw').vert i = p.vert i := by
  simp [snocArc, hi]

theorem snocArc_vert_last {s : ℕ} (p : Arc Γ s) (w : W) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : (snocArc p w hw hw').vert (s + 1) = w := by
  simp [snocArc]

theorem exists_walk (hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v) {u v : W}
    (huv : Γ.Adj u v) :
    ∃ ω : ℕ → W, ω 0 = u ∧ ω 1 = v ∧ (∀ i, Γ.Adj (ω i) (ω (i + 1))) ∧ ∀ i, ω i ≠ ω (i + 2) := by
  classical
  let step : {p : W × W // Γ.Adj p.1 p.2} → {p : W × W // Γ.Adj p.1 p.2} := fun p =>
    ⟨(p.1.2, Classical.choose (hdeg p.1.2 p.1.1 p.2.symm)),
      (Classical.choose_spec (hdeg p.1.2 p.1.1 p.2.symm)).1⟩
  let seq : ℕ → {p : W × W // Γ.Adj p.1 p.2} := fun n => step^[n] ⟨(u, v), huv⟩
  have hseq : ∀ n, seq (n + 1) = step (seq n) := fun n =>
    Function.iterate_succ_apply' step n _
  have h1 : ∀ n, (seq (n + 1)).1.1 = (seq n).1.2 := fun n => by rw [hseq]
  refine ⟨fun n => (seq n).1.1, rfl, ?_, fun n => ?_, fun n => ?_⟩
  · show (seq 1).1.1 = v
    rw [h1 0]
    rfl
  · show Γ.Adj (seq n).1.1 (seq (n + 1)).1.1
    rw [h1 n]
    exact (seq n).2
  · have h2 : (seq (n + 2)).1.1 = (seq (n + 1)).1.2 := h1 (n + 1)
    have h3 : (seq (n + 1)).1.2 =
        Classical.choose (hdeg (seq n).1.2 (seq n).1.1 (seq n).2.symm) := by
      rw [hseq]
    show (seq n).1.1 ≠ (seq (n + 2)).1.1
    rw [h2, h3]
    exact (Classical.choose_spec (hdeg (seq n).1.2 (seq n).1.1 (seq n).2.symm)).2.symm

@[expose] def walkArc (ω : ℕ → W) (hω : ∀ i, Γ.Adj (ω i) (ω (i + 1)))
    (hω' : ∀ i, ω i ≠ ω (i + 2)) (k : ℕ) : Arc Γ k where
  vert := ω
  adj i _ := hω i
  nb i _ := hω' i

@[simp] theorem walkArc_vert (ω : ℕ → W) (hω : ∀ i, Γ.Adj (ω i) (ω (i + 1)))
    (hω' : ∀ i, ω i ≠ ω (i + 2)) (k : ℕ) : (walkArc ω hω hω' k).vert = ω := rfl

end CFSG.Quasithin.Fan86.Tutte.Red
