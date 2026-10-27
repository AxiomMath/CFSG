module

public import Certificates.Data.CFSGNative.HN.F5Orbit
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.F5

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

structure VecFacts (d : ℕ) (TA TB : Array W17) (v₀ : ByteArray) (O : VOrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 32
  root : O.keys[0]! = v₀
  canon : ∀ k < O.keys.size, canonB d O.keys[k]! = true
  alpha : ∀ k < O.keys.size, ap O.alpha k < O.keys.size ∧
    O.keys[ap O.alpha k]! = mulW d d TA O.keys[k]!
  beta : ∀ k < O.keys.size, ap O.beta k < O.keys.size ∧
    O.keys[ap O.beta k]! = mulW d d TB O.keys[k]!
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))

theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have h' : (a.data == b.data) = true := h
  exact ByteArray.ext (by simpa using h')

theorem f5OrbitOK_facts {d : ℕ} {TA TB : Array W17} {v₀ : ByteArray} {O : VOrbit} {c : ℕ}
    (h : f5OrbitOK d TA TB v₀ O c = true) : VecFacts d TA TB v₀ O := by
  unfold f5OrbitOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hpos, hlt⟩, hroot'⟩, hall⟩ := h
  have hroot := byteArray_eq_of_beq hroot'
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, canonB d O.keys[k]! = true ∧
      O.index.getD O.keys[k]! O.keys.size = k ∧
      ap O.alpha k < O.keys.size ∧ mulW d d TA O.keys[k]! = O.keys[ap O.alpha k]! ∧
      ap O.beta k < O.keys.size ∧ mulW d d TB O.keys[k]! = O.keys[ap O.beta k]! ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [f5OrbitCheckAt, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    exact ⟨h1, h2, h3, byteArray_eq_of_beq h4, h5, byteArray_eq_of_beq h6, h7⟩
  refine ⟨hpos, hlt, hroot, fun k hk' => (hk k hk').1, ?_, ?_, ?_, ?_⟩
  · intro k hk'
    obtain ⟨-, -, ha, he, -⟩ := hk k hk'
    exact ⟨ha, he.symm⟩
  · intro k hk'
    obtain ⟨-, -, -, -, hb, he, -⟩ := hk k hk'
    exact ⟨hb, he.symm⟩
  · intro i hi j hj hij
    rw [← (hk i hi).2.1, ← (hk j hj).2.1, hij]
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2.2 with h0 | h1
    · omega
    · exact h1

end CFSG.Sporadic.F5
