module

public import CFSG.Sporadic.He.FpSpec
public import Certificates.Data.CFSGNative.He.Orbit
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.He.Native

open Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

structure VecFacts (p d : ℕ) (A B : Array (Array ℕ)) (O : VOrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 32
  canon : ∀ k < O.keys.size, canonV p d O.keys[k]! = true
  alpha : ∀ k < O.keys.size, ap O.alpha k < O.keys.size ∧
    toVec p d O.keys[ap O.alpha k]! = toMat p d A *ᵥ toVec p d O.keys[k]!
  beta : ∀ k < O.keys.size, ap O.beta k < O.keys.size ∧
    toVec p d O.keys[ap O.beta k]! = toMat p d B *ᵥ toVec p d O.keys[k]!
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, toVec p d O.keys[i]! = toVec p d O.keys[j]! →
    i = j
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))

theorem vecOrbitOK_facts {p d : ℕ} {A B : Array (Array ℕ)} {v₀ : Array ℕ} {O : VOrbit} {c : ℕ}
    (h : vecOrbitOK p d A B v₀ O c = true) : VecFacts p d A B O := by
  unfold vecOrbitOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hpos, hlt⟩, -⟩, hall⟩ := h
  set pos : Array ℕ → ℕ := fun X => (indexOf O.keys).getD X O.keys.size
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, canonV p d O.keys[k]! = true ∧ pos O.keys[k]! = k ∧
      ap O.alpha k < O.keys.size ∧ (mulVec p d A O.keys[k]! == O.keys[ap O.alpha k]!) = true ∧
      ap O.beta k < O.keys.size ∧ (mulVec p d B O.keys[k]! == O.keys[ap O.beta k]!) = true ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [vecCheckAt, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    simp only [beq_iff_eq] at h2 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨hpos, hlt, fun k hk' => (hk k hk').1, ?_, ?_, ?_, ?_⟩
  · intro k hk'
    obtain ⟨-, -, ha, he, -⟩ := hk k hk'
    exact ⟨ha, by rw [← toVec_eq_of_beq he, toVec_mulVec]⟩
  · intro k hk'
    obtain ⟨-, -, -, -, hb, he, -⟩ := hk k hk'
    exact ⟨hb, by rw [← toVec_eq_of_beq he, toVec_mulVec]⟩
  · intro i hi j hj hij
    have e := eq_of_toVec_eq (hk i hi).1 (hk j hj).1 hij
    rw [← (hk i hi).2.1, ← (hk j hj).2.1, e]
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2.2 with h0 | h1
    · omega
    · exact h1

end CFSG.Sporadic.He.Native
