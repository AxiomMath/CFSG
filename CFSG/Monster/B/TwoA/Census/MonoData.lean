module

public import CFSG.Monster.B.TwoA.Census.PermCert
public import CFSG.Monster.Lifts.PermLift

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts Matrix

@[expose] def sylowGenArr : List (Array ℕ) := [
  #[0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15],
  #[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19],
  #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21],
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  #[1, 0, 3, 2, 4, 5, 6, 7, 10, 11, 8, 9, 15, 14, 13, 12, 17, 16, 19, 18, 20, 21, 22, 23],
  #[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8, 16, 17, 19, 18, 21, 20, 22, 23],
  #[0, 1, 2, 3, 5, 4, 7, 6, 11, 10, 9, 8, 14, 15, 12, 13, 17, 16, 19, 18, 20, 21, 22, 23],
  #[2, 3, 0, 1, 4, 5, 6, 7, 11, 10, 9, 8, 13, 12, 15, 14, 18, 19, 16, 17, 20, 21, 22, 23],
  #[0, 1, 2, 3, 6, 7, 4, 5, 9, 8, 11, 10, 15, 14, 13, 12, 18, 19, 16, 17, 20, 21, 22, 23],
  #[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23]]

@[expose] def seedArr : List (Array ℕ) := [
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15],
  #[4, 5, 6, 7, 0, 1, 2, 3, 14, 15, 12, 13, 10, 11, 8, 9, 18, 19, 16, 17, 22, 23, 20, 21]]

@[expose] def centGenArr0 : List (Array ℕ) := [
  #[3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10],
  #[3, 9, 6, 18, 4, 5, 13, 22, 8, 14, 10, 23, 15, 2, 1, 20, 16, 7, 0, 11, 12, 21, 17, 19]]

@[expose] def centGenArr1 : List (Array ℕ) := [
  #[2, 4, 0, 6, 1, 7, 3, 5, 21, 19, 23, 17, 22, 16, 20, 18, 13, 11, 15, 9, 14, 8, 12, 10],
  #[1, 7, 2, 3, 5, 6, 4, 0, 8, 22, 17, 15, 19, 13, 10, 20, 16, 14, 9, 23, 11, 21, 18, 12],
  #[4, 3, 6, 0, 2, 7, 1, 5, 8, 21, 9, 20, 23, 10, 22, 11, 16, 13, 17, 12, 15, 18, 14, 19],
  #[4, 0, 2, 3, 6, 7, 1, 5, 8, 13, 22, 19, 23, 18, 9, 12, 16, 21, 14, 11, 15, 10, 17, 20],
  #[7, 2, 5, 6, 4, 3, 0, 1, 10, 21, 12, 19, 23, 8, 17, 14, 18, 13, 20, 11, 15, 16, 9, 22]]

@[expose] def centGenArr2 : List (Array ℕ) := [
  #[4, 16, 6, 22, 0, 18, 2, 20, 23, 15, 19, 13, 17, 11, 21, 9, 1, 12, 5, 10, 7, 14, 3, 8],
  #[15, 3, 11, 1, 9, 7, 13, 5, 23, 4, 19, 2, 17, 6, 21, 0, 22, 12, 20, 10, 18, 14, 16, 8],
  #[19, 5, 21, 7, 17, 1, 23, 3, 16, 15, 20, 13, 22, 11, 18, 9, 8, 4, 14, 0, 10, 2, 12, 6],
  #[3, 23, 1, 17, 7, 21, 5, 19, 9, 18, 11, 22, 13, 20, 15, 16, 8, 4, 14, 0, 10, 2, 12, 6],
  #[23, 3, 19, 5, 21, 7, 17, 1, 12, 6, 8, 4, 14, 0, 10, 2, 11, 22, 13, 20, 15, 16, 9, 18]]


@[expose] def centGenArrs : ℕ → List (Array ℕ)
  | 0 => centGenArr0
  | 1 => centGenArr1
  | _ => centGenArr2

@[expose] def monoSign : List ℕ := [0, 255, 212822, 0, 197482, 0, 3346236]

@[expose] def monoSeed : List ℕ := [0, 0, 0, 1, 1, 2, 2]

@[expose] noncomputable def sylowGen (k : ℕ) : Equiv.Perm (Fin 24) :=
  decode (sylowGenArr.getD k #[])

@[expose] noncomputable def seedPerm (j : ℕ) : Equiv.Perm (Fin 24) := decode (seedArr.getD j #[])

@[expose] noncomputable def centGen (j k : ℕ) : Equiv.Perm (Fin 24) :=
  decode ((centGenArrs j).getD k #[])

theorem sylowGenArr_perm : ∀ a ∈ sylowGenArr, PermArr a = true := by decide +kernel

theorem seedArr_perm : ∀ a ∈ seedArr, PermArr a = true := by decide +kernel

theorem centGenArr_perm : ∀ j < 3, ∀ a ∈ centGenArrs j, PermArr a = true := by decide +kernel

@[expose] def monoWord (i : ℕ) : Fin 24 → ZMod 2 := bvec 24 (monoSign.getD i 0)

@[expose] noncomputable def monoA (i : ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  diagonal (fun k => sgn (monoWord i k)) * Pmat (seedPerm (monoSeed.getD i 0))

theorem sgn_mul_self (t : ZMod 2) : sgn t * sgn t = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem monoA_mul_transpose (i : ℕ) : monoA i * (monoA i)ᵀ = 1 := by
  rw [monoA, Matrix.transpose_mul, Matrix.diagonal_transpose, Pmat, Matrix.transpose_permMatrix,
    Matrix.mul_assoc, ← Matrix.mul_assoc (Equiv.Perm.permMatrix ℚ _),
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext k
  exact sgn_mul_self _

theorem seedPerm_zero : seedPerm 0 = 1 := by
  ext i
  rw [seedPerm, decode_apply (seedArr_perm _ (by decide +kernel)), Equiv.Perm.one_apply]
  revert i
  decide +kernel

structure XiEdge where
  source : ℕ
  target : ℕ
  conjSign : ℕ
  word : List ℕ
  afterSign : ℕ
  afterPerm : Array ℕ
  normalizer : Array ℕ

@[expose] def xiEdges : List XiEdge := [
  ⟨1, 3, 13899902,
    [0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0],
    983055,
    #[1, 0, 3, 2, 7, 6, 5, 4, 8, 9, 10, 11, 14, 15, 12, 13, 18, 19, 16, 17, 20, 21, 22, 23],
    #[19, 11, 17, 9, 22, 20, 12, 14, 1, 2, 7, 6, 18, 8, 10, 16, 23, 13, 15, 21, 3, 5, 0, 4]⟩,
  ⟨2, 5, 15794160,
    [0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    1044735,
    #[1, 0, 3, 2, 7, 6, 5, 4, 11, 10, 9, 8, 13, 12, 15, 14, 17, 16, 19, 18, 23, 22, 21, 20],
    #[14, 8, 10, 12, 11, 15, 9, 13, 1, 3, 7, 5, 18, 16, 20, 22, 23, 21, 17, 19, 4, 6, 2, 0]⟩,
  ⟨2, 4, 12070626,
    [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0],
    15794160,
    #[3, 2, 1, 0, 5, 4, 7, 6, 8, 9, 10, 11, 14, 15, 12, 13, 16, 17, 18, 19, 22, 23, 20, 21],
    #[20, 22, 14, 12, 11, 19, 9, 17, 1, 2, 7, 6, 18, 8, 10, 16, 5, 3, 4, 0, 13, 23, 21, 15]⟩]

@[expose] noncomputable def xiAfterMat (e : XiEdge) : Matrix (Fin 24) (Fin 24) ℚ :=
  diagonal (fun k => sgn (bvec 24 e.afterSign k)) * Pmat (decode e.afterPerm)

@[expose] noncomputable def xiNormalizer (e : XiEdge) : Equiv.Perm (Fin 24) := decode e.normalizer

theorem xiEdges_perm :
    ∀ e ∈ xiEdges, PermArr e.afterPerm = true ∧ PermArr e.normalizer = true := by
  decide +kernel

theorem xiEdges_word : ∀ e ∈ xiEdges, ∀ l ∈ e.word, l < 2 := by decide +kernel

theorem monomial_involution_certificate_data :
    sylowGenArr.length = 10 ∧ (∀ a ∈ sylowGenArr, PermArr a = true) ∧
    seedArr.length = 3 ∧ (∀ a ∈ seedArr, PermArr a = true) ∧ seedPerm 0 = 1 ∧
    (∀ j < 3, ∀ a ∈ centGenArrs j, PermArr a = true) ∧
    monoSign = [0, 255, 212822, 0, 197482, 0, 3346236] ∧ monoSeed = [0, 0, 0, 1, 1, 2, 2] ∧
    (∀ i, monoA i * (monoA i)ᵀ = 1) ∧
    xiEdges.length = 3 ∧ (∀ e ∈ xiEdges, PermArr e.afterPerm = true ∧ PermArr e.normalizer = true) ∧
    (∀ e ∈ xiEdges, ∀ l ∈ e.word, l < 2) :=
  ⟨rfl, sylowGenArr_perm, rfl, seedArr_perm, seedPerm_zero, centGenArr_perm, rfl, rfl,
    monoA_mul_transpose, rfl, xiEdges_perm, xiEdges_word⟩

end CFSG.Monster.B.TwoA.Census
