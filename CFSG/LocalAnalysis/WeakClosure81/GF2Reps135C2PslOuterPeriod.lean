module

public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Finset.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private def c2sloutper_P {n f : ℕ} (ε : Fin f → Finset (Fin n)) (p : ℕ) : Prop :=
  ∀ r : Fin f, ε ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩ = ε r

private lemma c2sloutper_P_zero {n f : ℕ} (ε : Fin f → Finset (Fin n)) :
    c2sloutper_P ε 0 := by
  intro r
  have hfin : (⟨((r : ℕ) + 0) % f, Nat.mod_lt _ r.pos⟩ : Fin f) = r := by
    apply Fin.ext
    show ((r : ℕ) + 0) % f = (r : ℕ)
    rw [Nat.add_zero, Nat.mod_eq_of_lt r.isLt]
  rw [hfin]

private lemma c2sloutper_P_f {n f : ℕ} (ε : Fin f → Finset (Fin n)) :
    c2sloutper_P ε f := by
  intro r
  have hfin : (⟨((r : ℕ) + f) % f, Nat.mod_lt _ r.pos⟩ : Fin f) = r := by
    apply Fin.ext
    show ((r : ℕ) + f) % f = (r : ℕ)
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
  rw [hfin]

private lemma c2sloutper_P_add {n f : ℕ} {ε : Fin f → Finset (Fin n)} {p q : ℕ}
    (hp : c2sloutper_P ε p) (hq : c2sloutper_P ε q) : c2sloutper_P ε (p + q) := by
  intro r
  have hfin : (⟨((r : ℕ) + (p + q)) % f, Nat.mod_lt _ r.pos⟩ : Fin f)
      = ⟨(((r : ℕ) + p) % f + q) % f, Nat.mod_lt _ r.pos⟩ := by
    apply Fin.ext
    show ((r : ℕ) + (p + q)) % f = (((r : ℕ) + p) % f + q) % f
    rw [← Nat.add_assoc, ← Nat.mod_add_mod]
  rw [hfin]
  exact (hq ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩).trans (hp r)

private lemma c2sloutper_P_mul {n f : ℕ} {ε : Fin f → Finset (Fin n)} {q : ℕ}
    (hq : c2sloutper_P ε q) (j : ℕ) : c2sloutper_P ε (q * j) := by
  induction j with
  | zero => simpa using c2sloutper_P_zero ε
  | succ j ih =>
      rw [Nat.mul_succ]
      exact c2sloutper_P_add ih hq

private lemma c2sloutper_P_sub {n f : ℕ} {ε : Fin f → Finset (Fin n)} {p q : ℕ}
    (hp : c2sloutper_P ε p) (hq : c2sloutper_P ε q) (hle : q ≤ p) :
    c2sloutper_P ε (p - q) := by
  intro r
  let r' : Fin f := ⟨((r : ℕ) + (p - q)) % f, Nat.mod_lt _ r.pos⟩
  have hq' : ε ⟨((r' : ℕ) + q) % f, Nat.mod_lt _ r'.pos⟩ = ε r' := hq r'
  have hfin : (⟨((r' : ℕ) + q) % f, Nat.mod_lt _ r'.pos⟩ : Fin f)
      = ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩ := by
    apply Fin.ext
    show ((r' : ℕ) + q) % f = ((r : ℕ) + p) % f
    dsimp only [r']
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel hle]
  rw [hfin] at hq'
  exact hq'.symm.trans (hp r)

theorem w135c2_psl_period_dvd {n f s : ℕ} (hs : 1 ≤ s) (ε : Fin f → Finset (Fin n))
    (hrot : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (hmin : ∀ p : ℕ, 0 < p → p < s →
      ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r) :
    s ∣ f := by
  have hPs : c2sloutper_P ε s := hrot
  have hPf : c2sloutper_P ε f := c2sloutper_P_f ε
  have hPmul : c2sloutper_P ε (s * (f / s)) := c2sloutper_P_mul hPs (f / s)
  have hle : s * (f / s) ≤ f := Nat.mul_div_le f s
  have hPmod : c2sloutper_P ε (f % s) := by
    rw [Nat.mod_eq_sub_mul_div]
    exact c2sloutper_P_sub hPf hPmul hle
  rcases Nat.eq_zero_or_pos (f % s) with h0 | hpos
  · exact Nat.dvd_of_mod_eq_zero h0
  · exfalso
    have hlt : f % s < s := Nat.mod_lt f (by omega)
    obtain ⟨r, hr⟩ := hmin (f % s) hpos hlt
    exact hr (hPmod r)

end CFSG.LocalAnalysis.WeakClosure81
