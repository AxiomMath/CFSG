
module

public import CFSG.Sporadic.Fi24.Simple

@[expose] public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure LetterOK
    (X : Array W) (M : Matrix (Fin 781) (Fin 781) (ZMod 3)) : Prop where
  wf : RowsWF X
  size : X.size = 781
  mat : matW 781 781 X = M

theorem LetterOK.of_canonRows
    {X : Array W} (h : canonRows 781 X = true) :
    LetterOK X (matW 781 781 X) :=
  ⟨RowsWF.of_canonRows h, (canonRows_spec h).1, rfl⟩

theorem letterOK_idW : LetterOK (idW 781) 1 :=
  ⟨RowsWF.idW (by norm_num), idW_size 781, matW_idW (by norm_num)⟩

theorem LetterOK.mulW
    {X Y : Array W} {M N : Matrix (Fin 781) (Fin 781) (ZMod 3)}
    (hX : LetterOK X M) (hY : LetterOK Y N) : LetterOK (mulW X Y) (M * N) :=
  ⟨RowsWF.mulW hX.wf hY.wf, by rw [mulW_size, hX.size],
    by rw [matW_mulW (m := 781) (by norm_num) hX.wf hY.wf (by rw [hY.size]), hX.mat, hY.mat]⟩

theorem wordW_aux
    {f : ℤ → Array W} {m : ℤ → Matrix (Fin 781) (Fin 781) (ZMod 3)}
    (w : List ℤ) (h : ∀ z ∈ w, LetterOK (f z) (m z)) {M0 : Array W}
    {X0 : Matrix (Fin 781) (Fin 781) (ZMod 3)} (h0 : LetterOK M0 X0) :
    LetterOK (w.foldl (fun M z => mulW M (f z)) M0) (X0 * (w.map m).prod) := by
  induction w generalizing M0 X0 with
  | nil => simpa using h0
  | cons z w ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))
      (h0.mulW (h z List.mem_cons_self))

theorem wordW_spec
    {f : ℤ → Array W} {m : ℤ → Matrix (Fin 781) (Fin 781) (ZMod 3)}
    (w : List ℤ) (h : ∀ z ∈ w, LetterOK (f z) (m z)) :
    LetterOK (wordW f w) (w.map m).prod := by
  have := wordW_aux w h letterOK_idW
  rwa [one_mul] at this

@[expose] noncomputable def matHom :
    J →* Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  (Units.coeHom _).comp J.subtype

theorem matHom_apply (g : J) : matHom g = mat g := rfl

theorem mat_wordG
    (f : ℤ → J) (w : List ℤ) : mat (wordG f w) = (w.map fun z => mat (f z)).prod := by
  rw [wordG, ← matHom_apply, map_list_prod, List.map_map]
  rfl

theorem mat_inv_eq
    {g : J} {X : Matrix (Fin 781) (Fin 781) (ZMod 3)} (h : mat g * X = 1) :
    X = mat g⁻¹ := by
  calc X = mat g⁻¹ * mat g * X := by rw [mat_inv_mul, Matrix.one_mul]
    _ = mat g⁻¹ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

private theorem getElem!_push_lt {α : Type} [Inhabited α] (L : Array α) (x : α) {i : ℕ}
    (hi : i < L.size) : (L.push x)[i]! = L[i]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt hi, getElem!_pos L i hi]

private theorem getElem!_push_of_eq {α : Type} [Inhabited α] (L : Array α) (x : α) {i : ℕ}
    (hi : i = L.size) : (L.push x)[i]! = x := by
  subst hi
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem slpMatsN_size (words : Array (List ℤ)) (n : ℕ) :
    (slpMatsN words n).1.size = n ∧ (slpMatsN words n).2.size = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => simp [slpMatsN, ih.1, ih.2]

theorem slpMatsN_succ_fst (words : Array (List ℤ)) (n : ℕ) : (slpMatsN words (n + 1)).1 =
    (slpMatsN words n).1.push
      (wordW (chainLetterW (slpMatsN words n).1 (slpMatsN words n).2) words[n]!) := rfl

theorem slpMatsN_succ_snd (words : Array (List ℤ)) (n : ℕ) : (slpMatsN words (n + 1)).2 =
    (slpMatsN words n).2.push
      (invW 781 (wordW (chainLetterW (slpMatsN words n).1 (slpMatsN words n).2) words[n]!)) :=
  rfl

theorem slpMatsN_get (words : Array (List ℤ)) {j : ℕ} : ∀ n, j < n →
    (slpMatsN words n).1[j]! = (slpMatsN words (j + 1)).1[j]! ∧
      (slpMatsN words n).2[j]! = (slpMatsN words (j + 1)).2[j]!
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · obtain ⟨h1, h2⟩ := slpMatsN_get words n h
      have hs := slpMatsN_size words n
      rw [slpMatsN_succ_fst words n, slpMatsN_succ_snd words n,
        getElem!_push_lt _ _ (by omega), getElem!_push_lt _ _ (by omega)]
      exact ⟨h1, h2⟩
    · exact ⟨rfl, rfl⟩

theorem slpMatsN_succ (words : Array (List ℤ)) (n : ℕ) :
    (slpMatsN words (n + 1)).1[n]! =
      wordW (chainLetterW (slpMatsN words n).1 (slpMatsN words n).2) words[n]! := by
  rw [slpMatsN_succ_fst, getElem!_push_of_eq _ _ (slpMatsN_size words n).1.symm]

noncomputable abbrev sgW : Array (Array W) := (slpMatsN chainWords 13).1

noncomputable abbrev sgiW : Array (Array W) := (slpMatsN chainWords 13).2

noncomputable abbrev gramInvW : Array W := gramInv ()

noncomputable abbrev matTW : Array W := matT ()

structure ExtFacts : Prop where
  base : baseChecks matTW gramInvW = true
  gens : genChecks sgW sgiW = true
  norm : normChecks sgW sgiW matTW = true
  loc : localChecks sgW sgiW gramInvW = true

theorem slpOK_letter
    {j : ℕ} (hj : j < chainWords.size) {z : ℤ} (hz : z ∈ chainWords[j]!) :
    z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
  have hok := actionFacts.slp_ok
  unfold CFSG.Sporadic.Fi23.Native.slpOK at hok
  have := (allIn_eq_true.1 hok) j (Nat.zero_le _) hj
  rw [List.all_eq_true] at this
  have := this z hz
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

theorem chainWords_size :
    chainWords.size = 13 := actionFacts.words_size

theorem getD_eq_getElem! (L : Array (Array W)) (i : ℕ) : L[i]?.getD #[] = L[i]! := by
  by_cases hi : i < L.size
  · rw [Array.getElem?_eq_getElem hi, getElem!_pos L i hi]; rfl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi), getElem!_neg L i hi]; rfl

theorem mat_b_inv : mat b⁻¹ = mB * mB := by
  have h1 : mat b⁻¹ * mB = 1 := by rw [← mat_b, ← mat_mul, inv_mul_cancel, mat_one]
  calc mat b⁻¹ = mat b⁻¹ * (mB * (mB * mB)) := by rw [matrixFacts.B_cube, Matrix.mul_one]
    _ = (mat b⁻¹ * mB) * (mB * mB) := by rw [Matrix.mul_assoc]
    _ = mB * mB := by rw [h1, Matrix.one_mul]

theorem letterOK_matA :
    LetterOK matA mA := ⟨rowsWF_matA, matA_size, matW_matA⟩

theorem chainLetterW_one (G Gi : Array (Array W)) : chainLetterW G Gi 1 = matA := by
  simp [chainLetterW]

theorem chainLetterW_neg_one (G Gi : Array (Array W)) : chainLetterW G Gi (-1) = matA := by
  simp [chainLetterW]

theorem chainLetterW_two (G Gi : Array (Array W)) : chainLetterW G Gi 2 = matB := by
  simp [chainLetterW]

theorem chainLetterW_neg_two (G Gi : Array (Array W)) :
    chainLetterW G Gi (-2) = mulW matB matB := by
  simp [chainLetterW]

theorem genG_one : genG 1 = a := by simp [genG]

theorem genG_neg_one : genG (-1) = a⁻¹ := by simp [genG]

theorem genG_two : genG 2 = b := by simp [genG]

theorem genG_neg_two : genG (-2) = b⁻¹ := by simp [genG]

theorem letterOK_matB :
    LetterOK matB mB := ⟨rowsWF_matB, matB_size, matW_matB⟩

@[expose] noncomputable def genLetterG (z : ℤ) : J :=
  if 0 < z then gs (z.natAbs - 1) else (gs (z.natAbs - 1))⁻¹

@[expose] noncomputable def extWord
    (w : List ℤ) : J := wordG genLetterG w

noncomputable abbrev mR : Matrix (Fin 253) (Fin 781) (ZMod 3) := matW 253 781 rootForm.rows

noncomputable abbrev mS : Matrix (Fin 253) (Fin 253) (ZMod 3) := matW 253 253 gramInvW

noncomputable abbrev mK : Matrix (Fin 253) (Fin 253) (ZMod 3) := mR * mF * mRᵀ

noncomputable abbrev mE : Matrix (Fin 781) (Fin 781) (ZMod 3) := mRᵀ * (mS * (mR * mF))

noncomputable abbrev mT : Matrix (Fin 781) (Fin 781) (ZMod 3) := 1 + mE

theorem form_zero : form 0 = rootForm := formAt_zero _ _ _

theorem rootForm_facts :
    rootForm.rows.size = 253 ∧ RowsWF rootForm.rows := by
  rw [← form_zero]; exact form_facts (by rw [nPts_eq]; norm_num)

structure BaseFacts : Prop where
  A_canon : canonRows 781 matA = true
  B_canon : canonRows 781 matB = true
  T_canon : canonRows 781 matTW = true
  S_canon : canonRows 253 gramInvW = true
  SK : eqRows 253 (mulW gramInvW (gramW 253 rootForm.rows matF)) (idW 253) = true
  KS : eqRows 253 (mulW (gramW 253 rootForm.rows matF) gramInvW) (idW 253) = true

theorem matW_gramW :
    matW 253 253 (gramW 253 rootForm.rows matF) = mK := by
  have hRw := rootForm_facts.2
  have hFw := matrixFacts.F_wf
  have hFs := matrixFacts.F_size
  have hRF : matW 253 781 (mulW rootForm.rows matF) = mR * mF :=
    matW_mulW (m := 781) (by norm_num) hRw hFw (by omega)
  rw [gramW, matW_mulW (m := 781) (by norm_num) (RowsWF.mulW hRw hFw)
    (RowsWF.transposeW (by norm_num) _ _) (by rw [transposeW_size]), hRF,
    matW_transposeW (by norm_num) hRw]

theorem rowsWF_gramW : RowsWF (gramW 253 rootForm.rows matF) :=
  RowsWF.mulW (RowsWF.mulW rootForm_facts.2 matrixFacts.F_wf) (RowsWF.transposeW (by norm_num) _ _)

theorem gramW_size : (gramW 253 rootForm.rows matF).size = 253 := by
  rw [gramW, mulW_size, mulW_size, rootForm_facts.1]

end CFSG.Sporadic.Fi24
