module

public import CFSG.Quasithin.Background.G2UClosure
public import CFSG.Quasithin.Background.G2UColumns

public section

namespace CFSG.Quasithin.G2U

open Matrix

@[expose] def cc : List ℕ :=
  mul2 (mul2 g0c g1c) (mul2 g0c g1c)

@[expose] def dc : List ℕ :=
  mul2 (mul2 g2c g3c) (mul2 g2c g3c)

@[expose] def ac : List ℕ :=
  mul2 cc cc

@[expose] def bc : List ℕ :=
  mul2 (mul2 (mul2 cc cc) cc) dc

@[expose] def Ac : List ℕ :=
  [2, 0, 0, 0, 2, 0, 0, 0, 1]

@[expose] def Bc : List ℕ :=
  [2, 7, 2, 4, 3, 1, 1, 3, 4]

@[expose] def Bic : List ℕ :=
  [2, 7, 1, 4, 6, 6, 2, 1, 7]

@[expose] def decP (c : List ℕ) :
    Matrix (Fin 14) (Fin 14) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9 :=
  (dec2 (c.drop 9), dec3 c)

@[expose] def mulP (c c' : List ℕ) : List ℕ :=
  mul3 c c' ++ mul2 (c.drop 9) (c'.drop 9)

@[expose] def oneP : List ℕ :=
  id3 ++ id2

@[expose] def canonP (c : List ℕ) : Bool :=
  canon3 (c.take 9) && canon2 (c.drop 9)

theorem length_mul3 (m n : List ℕ) : (mul3 m n).length = 9 :=
  rfl

theorem dec3_append {m : List ℕ} (h : m.length = 9) (l : List ℕ) : dec3 (m ++ l) = dec3 m := by
  refine Matrix.ext fun i j => ?_
  simp only [dec3, Matrix.of_apply]
  rw [List.getD_append _ _ _ _ (by rw [h]; omega)]

theorem dec3_take (m : List ℕ) : dec3 (m.take 9) = dec3 m := by
  refine Matrix.ext fun i j => ?_
  simp only [dec3, Matrix.of_apply, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt (by omega)]

theorem decP_mulP (c c' : List ℕ) : decP (mulP c c') = decP c * decP c' := by
  simp only [decP, mulP, Prod.mk_mul_mk, dec3_append (length_mul3 c c'),
    List.drop_left' (length_mul3 c c'), dec2_mul2, dec3_mul3]

theorem decP_oneP : decP oneP = 1 := by
  have h : (id3 ++ id2).drop 9 = id2 := rfl
  rw [decP, oneP, dec3_append (rfl : id3.length = 9), h, dec2_id2, dec3_id3, Prod.mk_one_one]

theorem decP_injective {c c' : List ℕ} (h : canonP c = true) (h' : canonP c' = true)
    (e : decP c = decP c') : c = c' := by
  simp only [canonP, Bool.and_eq_true] at h h'
  simp only [decP, Prod.mk.injEq] at e
  rw [← List.take_append_drop 9 c, ← List.take_append_drop 9 c',
    dec2_injective h.2 h'.2 e.1,
    dec3_injective h.1 h'.1 (by rw [dec3_take, dec3_take, e.2])]

@[expose] def gensR : List (List ℕ) :=
  [g0c, g1c, g2c, g3c]

@[expose] def parR : List (ℕ × ℕ) :=
  bfsParents id2 mul2 gensR 12096

@[expose] def elemsR : Array (List ℕ) :=
  build id2 mul2 gensR parR

@[expose] def gensD : List (List ℕ) :=
  [Ac ++ ac, Bc ++ bc]

@[expose] def parD : List (ℕ × ℕ) :=
  bfsParents oneP mulP gensD 6048

@[expose] def elemsD : Array (List ℕ) :=
  build oneP mulP gensD parD

@[expose] def pairOK (c : List ℕ) : Bool :=
  canonP c && (c.drop 9 == id2) == (c.take 9 == id3)

theorem pairOK_spec {c : List ℕ} (h : pairOK c = true) :
    canonP c = true ∧ (c.drop 9 = id2 ↔ c.take 9 = id3) := by
  simp only [pairOK, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  rw [← beq_iff_eq (a := c.drop 9), ← beq_iff_eq (a := c.take 9), beq_iff_eq.mp h.2]

end CFSG.Quasithin.G2U
