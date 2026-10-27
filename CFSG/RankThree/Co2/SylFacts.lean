module

public import CFSG.RankThree.Co2.ClassesCertInputs
public import CFSG.RankThree.Co2.XData

public section

namespace CFSG.RankThree.Co2

@[expose] def rowsMat (R : Array ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun t j => if (R[t.val]!).testBit j.val then 1 else 0

@[expose] def wordMat (w : List ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMat (wordRows w)

@[expose] def repMat (i : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) := wordMat repWords[i]!

@[expose] noncomputable def matGrp (ws : Array (List ℕ)) :
    Submonoid (Matrix (Fin 22) (Fin 22) (ZMod 2)) :=
  Submonoid.closure (Set.range fun k : Fin ws.size => wordMat ws[k])

structure SylGrp (ws : Array (List ℕ)) (n : ℕ) (cls : List ℕ) : Prop where
  pow : ∀ x ∈ matGrp ws, x ^ 32 = 1
  card : n ≤ Nat.card (matGrp ws)
  mem : ∀ j ∈ cls, repMat j ∈ matGrp ws
  comm : ∀ j ∈ cls, ∀ x ∈ matGrp ws, x * repMat j = repMat j * x

@[expose] def SqCount (ws : Array (List ℕ)) (n i a : ℕ) : Prop :=
  Nat.card (matGrp ws) ≤ n →
    Nat.card {x : matGrp ws // (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) * x = repMat i} = a

@[expose] def ConjMul (ws : Array (List ℕ)) (R : Matrix (Fin 22) (Fin 22) (ZMod 2)) : Prop :=
  ∃ u ∈ matGrp ws, ∃ w ∈ matGrp ws, u * u = 1 ∧ u ≠ 1 ∧ w * u = u * R * w

@[expose] def SylFacts : Prop :=
  (SylGrp pWords1 (2 ^ 17) [1] ∧ SqCount pWords1 (2 ^ 17) 1 2304 ∧
    SqCount pWords1 (2 ^ 17) 0 768) ∧
  (SylGrp pWords3 (2 ^ 16) [2, 3] ∧ SqCount pWords3 (2 ^ 16) 3 1152 ∧
    SqCount pWords3 (2 ^ 16) 0 384) ∧
  (SylGrp pWords4 (2 ^ 15) [4] ∧ SqCount pWords4 (2 ^ 15) 4 128 ∧
    SqCount pWords4 (2 ^ 15) 0 192) ∧
  (SylGrp pWords5 (2 ^ 14) [5, 6] ∧ SqCount pWords5 (2 ^ 14) 5 256 ∧
    SqCount pWords5 (2 ^ 14) 0 0) ∧
  (SylGrp pWords6 (2 ^ 14) [5, 6] ∧ ConjMul pWords6 (repMat 0) ∧
    (Nat.card (matGrp pWords6) ≤ 2 ^ 14 → ¬ ConjMul pWords6 (repMat 6))) ∧
  (SylGrp pWords8 (2 ^ 14) [7, 8] ∧ ConjMul pWords8 (repMat 0) ∧
    (Nat.card (matGrp pWords8) ≤ 2 ^ 14 → ¬ ConjMul pWords8 (repMat 8)))

end CFSG.RankThree.Co2

end
