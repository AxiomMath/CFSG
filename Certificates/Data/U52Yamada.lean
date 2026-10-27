module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace Certificates.U52Yamada

open Matrix CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

@[expose] def nfMat (a₁ b₁ a₂ a₃ a₄ b₄ : F4) : Matrix (Fin 5) (Fin 5) F4 :=
  x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄

@[expose] def ValidPair (a b : F4) : Prop := a * bar a = b + bar b

instance (a b : F4) : Decidable (ValidPair a b) := by
  unfold ValidPair
  infer_instance

@[expose] def RowZero (M : Matrix (Fin 5) (Fin 5) F4) (i : Fin 5) : Prop :=
  ∀ j : Fin 5, i < j → M i j = 0

instance (M : Matrix (Fin 5) (Fin 5) F4) (i : Fin 5) : Decidable (RowZero M i) := by
  unfold RowZero
  infer_instance

@[expose] def IsFShape (M : Matrix (Fin 5) (Fin 5) F4) : Prop :=
  (∀ i : Fin 5, RowZero M i) ∧ (∀ i : Fin 5, M i i = 1) ∧ M 2 1 = 0 ∧ M 1 0 = 0 ∧ M 2 0 = 0

instance (M : Matrix (Fin 5) (Fin 5) F4) : Decidable (IsFShape M) := by
  unfold IsFShape
  infer_instance

@[expose] def invMat (M : Matrix (Fin 5) (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4 :=
  J5 * (M.map bar)ᵀ * J5

@[expose] def genMat : Fin 10 → Matrix (Fin 5) (Fin 5) F4 :=
  ![uMat, vMat, e₁Mat, e₂Mat, x₂Mat 1, x₂Mat F4.ω, x₁Mat 0 1, x₁Mat 1 F4.ω, x₃Mat 1,
    x₄Mat 1 F4.ω]

@[expose] def wordMat (w : List (Fin 10)) : Matrix (Fin 5) (Fin 5) F4 := (w.map genMat).prod

@[expose] def toArr (M : Matrix (Fin 5) (Fin 5) F4) : Array F4 :=
  #[M 0 0, M 0 1, M 0 2, M 0 3, M 0 4, M 1 0, M 1 1, M 1 2, M 1 3, M 1 4,
    M 2 0, M 2 1, M 2 2, M 2 3, M 2 4, M 3 0, M 3 1, M 3 2, M 3 3, M 3 4,
    M 4 0, M 4 1, M 4 2, M 4 3, M 4 4]

@[expose] def ofArr (a : Array F4) : Matrix (Fin 5) (Fin 5) F4 :=
  fun i j => a.getD (5 * i.val + j.val) 0

theorem ofArr_toArr (M : Matrix (Fin 5) (Fin 5) F4) : ofArr (toArr M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def amul (a b : Array F4) : Array F4 := toArr (ofArr a * ofArr b)

theorem ofArr_amul (a b : Array F4) : ofArr (amul a b) = ofArr a * ofArr b := ofArr_toArr _

@[expose] def nfA (a₁ b₁ a₂ a₃ a₄ b₄ : F4) : Array F4 :=
  amul (amul (amul (toArr (x₁Mat a₁ b₁)) (toArr (x₂Mat a₂))) (toArr (x₃Mat a₃)))
    (toArr (x₄Mat a₄ b₄))

theorem ofArr_nfA (a₁ b₁ a₂ a₃ a₄ b₄ : F4) :
    ofArr (nfA a₁ b₁ a₂ a₃ a₄ b₄) = nfMat a₁ b₁ a₂ a₃ a₄ b₄ := by
  simp only [nfA, nfMat, ofArr_amul, ofArr_toArr]

@[expose] def wordA (w : List (Fin 10)) : Array F4 :=
  w.foldr (fun i acc => amul (toArr (genMat i)) acc) (toArr 1)

theorem ofArr_wordA (w : List (Fin 10)) : ofArr (wordA w) = wordMat w := by
  induction w with
  | nil => exact ofArr_toArr 1
  | cons i w ih =>
    change ofArr (amul (toArr (genMat i)) (wordA w)) = ((i :: w).map genMat).prod
    rw [List.map_cons, List.prod_cons, ofArr_amul, ofArr_toArr, ih, wordMat]

@[expose] def invA (a : Array F4) : Array F4 :=
  toArr (Matrix.of fun i j => bar (ofArr a (Fin.rev j) (Fin.rev i)))

theorem ofArr_invA (a : Array F4) : ofArr (invA a) = invMat (ofArr a) := by
  rw [invA, ofArr_toArr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invMat, J5, Matrix.mul_apply, Fin.sum_univ_five, Fin.rev]

@[expose] def Check3101 : Prop :=
  ∀ a₁ b₁ a₂ a₃ a₄ b₄ : F4, ValidPair a₁ b₁ → ValidPair a₄ b₄ →
    nfMat a₁ b₁ a₂ a₃ a₄ b₄ * (nfMat a₁ b₁ a₂ a₃ a₄ b₄).map bar = 1 →
    ∃ c₁ d₁ c₂ c₃ c₄ d₄ : F4, ValidPair c₁ d₁ ∧ ValidPair c₄ d₄ ∧
      nfMat c₁ d₁ c₂ c₃ c₄ d₄ * nfMat a₁ b₁ a₂ a₃ a₄ b₄ = (nfMat c₁ d₁ c₂ c₃ c₄ d₄).map bar

@[expose] def Check3101M : Prop :=
  ∀ a₁ b₁ a₂ a₃ a₄ b₄ : F4, ValidPair a₁ b₁ → ValidPair a₄ b₄ →
    ofArr (nfA a₁ b₁ a₂ a₃ a₄ b₄) * (ofArr (nfA a₁ b₁ a₂ a₃ a₄ b₄)).map bar = 1 →
    ∃ c₁ d₁ c₂ c₃ c₄ d₄ : F4, ValidPair c₁ d₁ ∧ ValidPair c₄ d₄ ∧
      ofArr (amul (nfA c₁ d₁ c₂ c₃ c₄ d₄) (nfA a₁ b₁ a₂ a₃ a₄ b₄)) =
        (ofArr (nfA c₁ d₁ c₂ c₃ c₄ d₄)).map bar

theorem check3101M_iff : Check3101M ↔ Check3101 := by
  simp only [Check3101M, Check3101, ofArr_amul, ofArr_nfA]

opaque decCheck3101M (_ : Unit) : Decidable Check3101M := by
  unfold Check3101M
  infer_instance

@[expose] def check3101 (u : Unit) : Bool :=
  @decide Check3101 (@decidable_of_iff _ Check3101M check3101M_iff (decCheck3101M u))

theorem of_check3101 (h : check3101 () = true) : Check3101 :=
  @of_decide_eq_true Check3101 (@decidable_of_iff _ Check3101M check3101M_iff (decCheck3101M ())) h

@[expose] def conjWord : Fin 8 → List (Fin 10) :=
  ![[0], [0, 6], [0, 7], [0, 6, 7], [0, 7, 0], [0, 7, 3], [0, 6, 7, 3], [0, 7, 0, 6]]

@[expose] def Check39 : Prop :=
  ∀ a₁ b₁ a₂ a₃ a₄ b₄ : F4, ValidPair a₁ b₁ → ValidPair a₄ b₄ →
    nfMat a₁ b₁ a₂ a₃ a₄ b₄ * nfMat a₁ b₁ a₂ a₃ a₄ b₄ = 1 →
    IsFShape (nfMat a₁ b₁ a₂ a₃ a₄ b₄) ∨ ∃ k : Fin 8,
      IsFShape (wordMat (conjWord k) * nfMat a₁ b₁ a₂ a₃ a₄ b₄ *
        invMat (wordMat (conjWord k)))

@[expose] def Check39M : Prop :=
  ∀ a₁ b₁ a₂ a₃ a₄ b₄ : F4, ValidPair a₁ b₁ → ValidPair a₄ b₄ →
    ofArr (amul (nfA a₁ b₁ a₂ a₃ a₄ b₄) (nfA a₁ b₁ a₂ a₃ a₄ b₄)) = 1 →
    IsFShape (ofArr (nfA a₁ b₁ a₂ a₃ a₄ b₄)) ∨ ∃ k : Fin 8,
      IsFShape (ofArr (amul (amul (wordA (conjWord k)) (nfA a₁ b₁ a₂ a₃ a₄ b₄))
        (invA (wordA (conjWord k)))))

theorem check39M_iff : Check39M ↔ Check39 := by
  simp only [Check39M, Check39, ofArr_amul, ofArr_nfA, ofArr_wordA, ofArr_invA]

opaque decCheck39M (_ : Unit) : Decidable Check39M := by
  unfold Check39M
  infer_instance

@[expose] def check39 (u : Unit) : Bool :=
  @decide Check39 (@decidable_of_iff _ Check39M check39M_iff (decCheck39M u))

theorem of_check39 (h : check39 () = true) : Check39 :=
  @of_decide_eq_true Check39 (@decidable_of_iff _ Check39M check39M_iff (decCheck39M ())) h

@[expose] def genF : Fin 4 → Matrix (Fin 5) (Fin 5) F4 :=
  ![x₁Mat 0 1, x₃Mat 1, x₃Mat F4.ω, x₄Mat 0 1]

@[expose] def genN0 : Fin 5 → Fin 10 := ![1, 2, 3, 4, 5]

@[expose] def CheckNormF : Prop :=
  ∀ i : Fin 5, ∀ j : Fin 4,
    IsFShape (genMat (genN0 i) * genF j * invMat (genMat (genN0 i)))

@[expose] def orb5 : Fin 4 → F4 × F4 × F4 :=
  ![(1, 0, 0), (1, 1, 1), (1, F4.ω, 1), (1, F4.ω + 1, 1)]

@[expose] def orbWord5 : Fin 4 → List (Fin 10) := ![[1], [4, 1], [5, 1], [5, 4, 1]]

@[expose] def orb10 : Fin 9 → F4 × F4 × F4 :=
  ![(0, 1, 1), (0, F4.ω, 0), (0, F4.ω, 1), (0, F4.ω + 1, 0), (0, F4.ω + 1, 1), (1, 0, 1),
    (1, 1, 0), (1, F4.ω, 0), (1, F4.ω + 1, 0)]

@[expose] def orbWord10 : Fin 9 → List (Fin 10) :=
  ![[5], [2], [2, 5], [1, 2], [2, 2, 5], [4, 1, 5], [1, 5], [2, 1, 5], [5, 1, 5]]

@[expose] def fMat (p : F4 × F4 × F4) : Matrix (Fin 5) (Fin 5) F4 := nfMat 0 p.1 0 p.2.1 0 p.2.2

@[expose] def CheckOrb5 : Prop :=
  ∀ k : Fin 4, wordMat (orbWord5 k) * x₄Mat 0 1 = fMat (orb5 k) * wordMat (orbWord5 k)

@[expose] def CheckOrb10 : Prop :=
  ∀ k : Fin 9, wordMat (orbWord10 k) * x₃Mat 1 = fMat (orb10 k) * wordMat (orbWord10 k)

@[expose] def cA5 : Matrix (Fin 5) (Fin 5) F4 := x₃Mat 1 * x₄Mat 0 1

@[expose] def bA5 : Matrix (Fin 5) (Fin 5) F4 := x₁Mat 0 1 * x₄Mat 0 1 * uMat * vMat * uMat * vMat

@[expose] def cbMat (w : List Bool) : Matrix (Fin 5) (Fin 5) F4 :=
  (w.map fun x => if x then bA5 else cA5).prod

@[expose] def a5Word : Fin 4 → List Bool :=
  ![[true, false, true, false, true, true], [false, true, true, false, true, false, true],
    [false, true, true], [false, true, false, true, true, false, true]]

@[expose] def CheckA5 : Prop :=
  cA5 * cbMat (a5Word 1) * cbMat (a5Word 0) = cbMat (a5Word 0) * cbMat (a5Word 1) ∧
    bA5 * cbMat (a5Word 3) * cbMat (a5Word 2) = cbMat (a5Word 2) * cbMat (a5Word 3)

@[expose] def CheckIdent : Prop := CheckNormF ∧ CheckOrb5 ∧ CheckOrb10 ∧ CheckA5

@[expose] def cA5A (_ : Unit) : Array F4 := amul (toArr (x₃Mat 1)) (toArr (x₄Mat 0 1))

@[expose] def bA5A (_ : Unit) : Array F4 :=
  amul (amul (amul (amul (amul (toArr (x₁Mat 0 1)) (toArr (x₄Mat 0 1))) (toArr uMat))
    (toArr vMat)) (toArr uMat)) (toArr vMat)

@[expose] def cbA (w : List Bool) : Array F4 :=
  w.foldr (fun x acc => amul (if x then bA5A () else cA5A ()) acc) (toArr 1)

theorem ofArr_cbA (w : List Bool) : ofArr (cbA w) = cbMat w := by
  have hb : ofArr (bA5A ()) = bA5 := by simp only [bA5A, bA5, ofArr_amul, ofArr_toArr]
  have hc : ofArr (cA5A ()) = cA5 := by simp only [cA5A, cA5, ofArr_amul, ofArr_toArr]
  induction w with
  | nil => exact ofArr_toArr 1
  | cons x w ih =>
    change ofArr (amul (if x then bA5A () else cA5A ()) (cbA w)) =
      ((x :: w).map fun x => if x then bA5 else cA5).prod
    rw [List.map_cons, List.prod_cons, ofArr_amul, ih, cbMat]
    cases x
    · simp only [Bool.false_eq_true, ↓reduceIte, hc]
    · simp only [↓reduceIte, hb]

@[expose] def CheckIdentM : Prop :=
  (∀ i : Fin 5, ∀ j : Fin 4, IsFShape (ofArr (amul (amul (toArr (genMat (genN0 i)))
    (toArr (genF j))) (invA (toArr (genMat (genN0 i))))))) ∧
  (∀ k : Fin 4, ofArr (amul (wordA (orbWord5 k)) (toArr (x₄Mat 0 1))) =
    ofArr (amul (nfA 0 (orb5 k).1 0 (orb5 k).2.1 0 (orb5 k).2.2) (wordA (orbWord5 k)))) ∧
  (∀ k : Fin 9, ofArr (amul (wordA (orbWord10 k)) (toArr (x₃Mat 1))) =
    ofArr (amul (nfA 0 (orb10 k).1 0 (orb10 k).2.1 0 (orb10 k).2.2) (wordA (orbWord10 k)))) ∧
  (ofArr (amul (amul (cA5A ()) (cbA (a5Word 1))) (cbA (a5Word 0))) =
      ofArr (amul (cbA (a5Word 0)) (cbA (a5Word 1))) ∧
    ofArr (amul (amul (bA5A ()) (cbA (a5Word 3))) (cbA (a5Word 2))) =
      ofArr (amul (cbA (a5Word 2)) (cbA (a5Word 3))))

theorem checkIdentM_iff : CheckIdentM ↔ CheckIdent := by
  have hb : ofArr (bA5A ()) = bA5 := by simp only [bA5A, bA5, ofArr_amul, ofArr_toArr]
  have hc : ofArr (cA5A ()) = cA5 := by simp only [cA5A, cA5, ofArr_amul, ofArr_toArr]
  simp only [CheckIdentM, CheckIdent, CheckNormF, CheckOrb5, CheckOrb10, CheckA5, fMat,
    ofArr_amul, ofArr_toArr, ofArr_nfA, ofArr_wordA, ofArr_invA, ofArr_cbA, hb, hc]

opaque decCheckIdentM (_ : Unit) : Decidable CheckIdentM := by
  unfold CheckIdentM
  infer_instance

@[expose] def checkIdent (u : Unit) : Bool :=
  @decide CheckIdent (@decidable_of_iff _ CheckIdentM checkIdentM_iff (decCheckIdentM u))

theorem of_checkIdent (h : checkIdent () = true) : CheckIdent :=
  @of_decide_eq_true CheckIdent
    (@decidable_of_iff _ CheckIdentM checkIdentM_iff (decCheckIdentM ())) h

end Certificates.U52Yamada
