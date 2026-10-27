
module

public import CFSG.GroupTheory.TwoWeightData
public import CFSG.Sporadic.Ly.Certificate
public import CFSG.Sporadic.Ly.SimpleBase

@[expose] public section

namespace CFSG.Sporadic.Ly

open Native Matrix
open CFSG.Sporadic.Th CFSG.Perm
open CFSG.Sporadic.Th.Native (Table ap compT powT order3OK invOK invT wordT)
open CFSG.Sporadic.Fi23 (slpG slpG_eq rep_slpLetters)
open CFSG.Sporadic.Fi23.Native (slpOK slpLetters slpLetterT)
open CFSG.Sporadic.Ly.TwoWeights

section

@[expose] noncomputable def twGs (j : ℕ) : J := slpG genG twWords j

@[expose] noncomputable def twLetterG (z : ℤ) : J :=
  if z.natAbs ≤ 2 then genG z
  else if 0 < z then twGs (z.natAbs - 3) else (twGs (z.natAbs - 3))⁻¹

theorem twLetterG_eq : twLetterG = Omega.slpLetter twWords := by
  funext z
  unfold twLetterG twGs Omega.slpLetter genG Omega.seedLetter
  rfl

end

section

theorem tw_L1 : twLetterG 1 = a := by simp [twLetterG, genG]

theorem tw_L4 : twLetterG 4 = twGs 1 := by simp [twLetterG]

theorem tw_L9 : twLetterG 9 = twGs 6 := by simp [twLetterG]

theorem tw_L10 : twLetterG 10 = twGs 7 := by simp [twLetterG]

theorem tw_L13 : twLetterG 13 = twGs 10 := by simp [twLetterG]

theorem tw_L14 : twLetterG 14 = twGs 11 := by simp [twLetterG]

theorem tw_Ln13 : twLetterG (-13) = (twGs 10)⁻¹ := by simp [twLetterG]

theorem tw_Ln14 : twLetterG (-14) = (twGs 11)⁻¹ := by simp [twLetterG]

theorem tw_rels : ∀ r ∈ twRels, wordG twLetterG r.1 = wordG twLetterG r.2 := by
  rw [twLetterG_eq]
  exact ly_word_facts.2.1

theorem two_weight_rels :
    CFSG.GroupTheory.TwoWeights.Data a (twGs 1) (twGs 6) (twGs 7) (twGs 10) (twGs 11) := by
  have R := tw_rels
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := R ([1, 1], []) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([4, 4], []) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([9, 9], []) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([10, 10], []) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([4, 9], [9, 4]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([4, 10], [10, 4]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([4, 1], [1, 4]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([9, 10], [10, 9]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([9, 1], [1, 9]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([10, 1], [1, 10]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([1, 13], [13, 1]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([1, 14], [14, 1]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([13, 4], [4, 1, 13]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([13, 9], [10, 1, 13]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([13, 10], [9, 1, 13]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([-13, 4], [4, 1, -13]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([-13, 9], [10, 1, -13]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([-13, 10], [9, 1, -13]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([14, 4], [4, 14]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([14, 9], [9, 1, 14]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([14, 10], [4, 10, 1, 14]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([-14, 4], [4, -14]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([-14, 9], [9, 1, -14]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([-14, 10], [4, 10, 1, -14]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([13, 13], [1]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([14, 14], [1]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h
  · have h := R ([13, 14, 13, 14, 13, 14, 13, 14], [1]) (by decide +kernel)
    simpa [wordG, tw_L1, tw_L4, tw_L9, tw_L10, tw_L13, tw_L14, tw_Ln13,
      tw_Ln14, mul_assoc] using h

end

end CFSG.Sporadic.Ly
