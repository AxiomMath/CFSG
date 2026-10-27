module

public import CFSG.Quasithin.EmptyFaithful.ModDData

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin

set_option synthInstance.maxSize 2048 in
theorem fl_line_exact : ∀ p q : Fin 63, p ≠ 0 → q ≠ 0 → p ≠ q →
    (∀ i ∈ [(0 : Fin 5), 1, 2, 4], (vImg i 0 = 0 ∨ vImg i 0 = p ∨ vImg i 0 = q) ∧
      (vImg i p = 0 ∨ vImg i p = p ∨ vImg i p = q) ∧ (vImg i q = 0 ∨ vImg i q = p ∨ vImg i q = q)) →
    (p = 37 ∧ q = 43) ∨ (p = 43 ∧ q = 37) := by decide +kernel

theorem A_preserves_cSet : ∀ i ∈ [(0 : Fin 5), 1, 2, 3], ∀ x : Fin 63, (vImg i x ∈ cSet ↔ x ∈ cSet) := by
  decide +kernel

@[expose] def baseTriples : List (Fin 63 × Fin 63 × Fin 63) := [(0, 37, 43), (37, 0, 43), (37, 43, 0), (8, 37, 45)]

@[expose] def wordsA : List String := ["", "b", "Xsa", "xa", "Xs", "bxs", "aX", "sb", "Xsb", "ba", "X", "bx", "sba", "aXs", "s", "Xb", "xsb", "xb", "a", "sa", "xsa", "x", "Xa", "xs"]

theorem closure_wit : ∀ i ∈ cSet, ∀ j ∈ cSet, i ≠ j → ∃ w ∈ wordsA, ∃ b ∈ baseTriples,
    (evalW vImg (u33Word w)) b.1 = i ∧ (evalW vImg (u33Word w)) b.2.1 = j ∧
      (evalW vImg (u33Word w)) b.2.2 ∈ cSet := by decide +kernel

theorem S1_cert : (evalW vImg (u33Word "Xa")) 0 = 0 ∧ (evalW vImg (u33Word "Xa")) 1 = 1 ∧
    ∀ x : Fin 63, (evalW vImg (u33Word "Xa")) x = x → x = 0 ∨ x = 1 ∨ x = 10 := by decide +kernel

theorem S2_cert : (evalW vImg (u33Word "yxYXBa")) 1 = 1 ∧ (evalW vImg (u33Word "yxYXBa")) 16 = 16 ∧
    ∀ x : Fin 63, (evalW vImg (u33Word "yxYXBa")) x = x → x = 1 ∨ x = 16 ∨ x = 15 := by decide +kernel

theorem S3_cert : (evalW vImg (u33Word "XbA")) 0 = 0 ∧ (evalW vImg (u33Word "XbA")) 15 = 15 ∧
    ∀ x : Fin 63, (evalW vImg (u33Word "XbA")) x = x → x = 0 ∨ x = 15 ∨ x = 25 := by decide +kernel

theorem g1_wit : (evalW vImg (u33Word "A")) 0 = 0 ∧ (evalW vImg (u33Word "A")) 1 = 25 ∧
    (evalW vImg (u33Word "A")) 10 = 15 := by decide +kernel

theorem g2_wit : (evalW vImg (u33Word "XyxyXy")) 0 = 1 ∧ (evalW vImg (u33Word "XyxyXy")) 37 = 16 ∧
    (evalW vImg (u33Word "XyxyXy")) 43 = 15 := by decide +kernel

theorem g0_wit : (evalW vImg (u33Word "yXYx")) 10 = 8 ∧ (evalW vImg (u33Word "yXYx")) 16 = 37 ∧
    (evalW vImg (u33Word "yXYx")) 25 = 45 := by decide +kernel

theorem h_wit : vImg 4 0 = 43 ∧ (vImg 4)⁻¹ 0 = 37 := by decide +kernel

end CFSG.Quasithin.ModD
