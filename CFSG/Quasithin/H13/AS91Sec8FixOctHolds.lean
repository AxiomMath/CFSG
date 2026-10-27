module

public import CFSG.Quasithin.H13.AS91Sec8FixOct
public import CFSG.Quasithin.H13.AS91Sec3Twelve
public import Certificates.Certificate664001

public section

open scoped Pointwise
open scoped commutatorElement

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.Quasithin.H13.AS91.M24G

section Tables

variable {a b : Array ℕ} {g h : Equiv.Perm (Fin 24)}

theorem repT_idTab : RepT Native.fixOctIdTab (1 : Equiv.Perm (Fin 24)) := by
  unfold RepT Native.fixOctIdTab
  decide +kernel

theorem repT_mulTab (ha : RepT a g) (hb : RepT b h) :
    RepT (Native.mulTab a b) (g * h) := by
  intro i
  rw [Equiv.Perm.mul_apply]
  have h1 : (Native.mulTab a b)[i.val]! = a[b[i.val]!]! := by
    simp [Native.mulTab]
  rw [h1, hb i, ha (h i)]

theorem hasArr_of_repT (h : RepT a g) : HasArr g a := by
  intro i
  have h' := h i
  unfold RepT at h'
  rw [h']

end Tables

section Bricks


@[expose] def brickMask : Fin 3 → ℕ := ![255, 65280, 16711680]

@[expose] def brick (j : Fin 3) : ↥(trioFin 0) :=
  ⟨maskFin (brickMask j), by
    rw [trioFin_zero_eq]
    fin_cases j <;> simp [brickMask]⟩

@[expose] def posOf (O : ↥(trioFin 0)) : Fin 3 :=
  if (⟨0, by norm_num⟩ : Fin 24) ∈ (O : Finset (Fin 24)) then 0
  else if (⟨8, by norm_num⟩ : Fin 24) ∈ (O : Finset (Fin 24)) then 1 else 2

@[expose] def posMask (n : ℕ) : Fin 3 :=
  if n.testBit 0 = true then 0 else if n.testBit 8 = true then 1 else 2

theorem posOf_brick (j : Fin 3) : posOf (brick j) = j := by
  fin_cases j <;> simp [posOf, brick, brickMask, mem_maskFin] <;> decide

theorem posOf_maskFin (n : ℕ) (h : maskFin n ∈ trioFin 0) :
    posOf ⟨maskFin n, h⟩ = posMask n := by
  simp [posOf, posMask, mem_maskFin]

theorem eq_brick (O : ↥(trioFin 0)) : ∃ j : Fin 3, brick j = O := by
  have hO := O.2
  simp only [trioFin_zero_eq, Finset.mem_insert, Finset.mem_singleton] at hO
  rcases hO with h | h | h
  · exact ⟨0, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨1, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨2, Subtype.ext (by rw [h]; rfl)⟩

theorem brick_posOf (O : ↥(trioFin 0)) : brick (posOf O) = O := by
  obtain ⟨j, rfl⟩ := eq_brick O
  rw [posOf_brick]

theorem brick_injective : Function.Injective brick := by
  intro i j h
  have h' : brickMask i = brickMask j :=
    maskFin_inj (by fin_cases i <;> simp [brickMask])
      (by fin_cases j <;> simp [brickMask]) (congrArg Subtype.val h)
  fin_cases i <;> fin_cases j <;> simp_all [brickMask]

theorem posOf_injective : Function.Injective posOf := by
  intro O O' h
  have h' := congrArg brick h
  rwa [brick_posOf, brick_posOf] at h'

end Bricks

@[expose] def actPerm (l : Finset (Finset (Fin 24))) (σ : S24) (h : σ • l = l) :
    Equiv.Perm ↥l where
  toFun O :=
    ⟨σ • O.1, by
      have h1 := Finset.smul_mem_smul_finset (a := σ) O.2
      rwa [h] at h1⟩
  invFun O :=
    ⟨σ⁻¹ • O.1, by
      have h' : σ⁻¹ • l = l := by
        conv_lhs => rw [← h]
        rw [inv_smul_smul]
      have h1 := Finset.smul_mem_smul_finset (a := σ⁻¹) O.2
      rwa [h'] at h1⟩
  left_inv O := by
    apply Subtype.ext
    simp
  right_inv O := by
    apply Subtype.ext
    simp

section Words

@[expose] def wordTab : Fin 6 → Array ℕ :=
  ![
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    #[12, 11, 8, 15, 10, 13, 14, 9, 19, 20, 23, 16, 21, 18, 17, 22, 1, 6, 5, 2, 7, 0, 3, 4],
    #[21, 16, 19, 22, 23, 18, 17, 20, 2, 7, 4, 1, 0, 5, 6, 3, 11, 14, 13, 8, 9, 12, 15, 10],
    #[15, 9, 8, 14, 13, 11, 10, 12, 3, 5, 4, 2, 1, 7, 6, 0, 22, 16, 17, 23, 20, 18, 19, 21],
    #[22, 20, 19, 17, 18, 16, 23, 21, 15, 13, 10, 8, 11, 9, 14, 12, 3, 1, 6, 4, 7, 5, 2, 0],
    #[3, 7, 2, 6, 5, 1, 4, 0, 22, 18, 23, 19, 16, 20, 17, 21, 15, 11, 14, 10, 9, 13, 8, 12]]

@[expose] def wordPerm : Fin 6 → Equiv.Perm (Fin 24) :=
  ![1, lPerm 0, lPerm 0 * lPerm 0, lPerm 2, lPerm 0 * lPerm 2, lPerm 0 * (lPerm 0 * lPerm 2)]

theorem repT_wordTab (i : Fin 6) : RepT (wordTab i) (wordPerm i) := by
  revert i
  unfold wordTab wordPerm RepT
  decide +kernel

private theorem wordPerm_basis : ∀ (i : Fin 6) (j : Fin 12),
    CFSG.Monster.Code.B j ∘ ⇑(wordPerm i) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem wordPerm_basis' : ∀ (i : Fin 6) (j : Fin 12),
    CFSG.Monster.Code.B j ∘ ⇑(wordPerm i)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem wordPerm_mem (i : Fin 6) : wordPerm i ∈ M24g :=
  mem_AutPerm_of_basis (wordPerm_basis i) (wordPerm_basis' i)

end Words

theorem wordTab_img_mem (i : Fin 6) (j : Fin 3) :
    Native.img (wordTab i) (brickMask j) = brickMask 0 ∨
      Native.img (wordTab i) (brickMask j) = brickMask 1 ∨
        Native.img (wordTab i) (brickMask j) = brickMask 2 := by
  revert i j
  unfold wordTab brickMask
  decide +kernel

section Sym


theorem wordPerm_fix (i : Fin 6) : wordPerm i • trioFin 0 = trioFin 0 := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    rw [Finset.mem_smul_finset] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    simp only [trioFin_zero_eq, Finset.mem_insert, Finset.mem_singleton] at hm' ⊢
    rcases hm' with rfl | rfl | rfl
    · rw [← maskFin_img (repT_wordTab i) 255,
        show (255 : ℕ) = brickMask 0 from rfl]
      rcases wordTab_img_mem i 0 with h | h | h <;> rw [h] <;> simp [brickMask]
    · rw [← maskFin_img (repT_wordTab i) 65280,
        show (65280 : ℕ) = brickMask 1 from rfl]
      rcases wordTab_img_mem i 1 with h | h | h <;> rw [h] <;> simp [brickMask]
    · rw [← maskFin_img (repT_wordTab i) 16711680,
        show (16711680 : ℕ) = brickMask 2 from rfl]
      rcases wordTab_img_mem i 2 with h | h | h <;> rw [h] <;> simp [brickMask]
  · rw [Finset.card_smul_finset]

@[expose] def codeOf (π : Equiv.Perm ↥(trioFin 0)) : Fin 3 × Fin 3 × Fin 3 :=
  (posOf (π (brick 0)), posOf (π (brick 1)), posOf (π (brick 2)))

@[expose] def tabCode (t : Array ℕ) : Fin 3 × Fin 3 × Fin 3 :=
  (posMask (Native.img t 255), posMask (Native.img t 65280),
    posMask (Native.img t 16711680))

theorem tabCode_wordTab : ∀ c : Fin 3 × Fin 3 × Fin 3,
    (c.1 ≠ c.2.1 ∧ c.1 ≠ c.2.2 ∧ c.2.1 ≠ c.2.2) →
      ∃ i : Fin 6, tabCode (wordTab i) = c := by
  decide +kernel

theorem posOf_congr {O O' : ↥(trioFin 0)} (h : O.1 = O'.1) : posOf O = posOf O' := by
  unfold posOf
  rw [h]

theorem posOf_actPerm (i : Fin 6) (j : Fin 3) :
    posOf (actPerm (trioFin 0) (wordPerm i) (wordPerm_fix i) (brick j)) =
      posMask (Native.img (wordTab i) (brickMask j)) := by
  have hval : (actPerm (trioFin 0) (wordPerm i) (wordPerm_fix i) (brick j)).1 =
      maskFin (Native.img (wordTab i) (brickMask j)) := by
    show wordPerm i • (brick j).1 = _
    rw [show (brick j).1 = maskFin (brickMask j) from rfl,
      ← maskFin_img (repT_wordTab i) (brickMask j)]
  have hmem : maskFin (Native.img (wordTab i) (brickMask j)) ∈ trioFin 0 := by
    rw [maskFin_img (repT_wordTab i) (brickMask j), ← wordPerm_fix i]
    exact Finset.smul_mem_smul_finset (a := wordPerm i) (brick j).2
  exact (posOf_congr hval).trans (posOf_maskFin _ hmem)

theorem codeOf_actPerm (i : Fin 6) :
    codeOf (actPerm (trioFin 0) (wordPerm i) (wordPerm_fix i)) = tabCode (wordTab i) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [codeOf, tabCode]
  · simpa [brickMask] using posOf_actPerm i 0
  · simpa [brickMask] using posOf_actPerm i 1
  · simpa [brickMask] using posOf_actPerm i 2

theorem codeOf_injective : Function.Injective codeOf := by
  intro π π' h
  simp only [codeOf, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  have key : ∀ j : Fin 3, π (brick j) = π' (brick j) := by
    intro j
    fin_cases j
    · exact posOf_injective h0
    · exact posOf_injective h1
    · exact posOf_injective h2
  refine Equiv.ext fun O => ?_
  rw [← brick_posOf O]
  exact key (posOf O)

theorem codeOf_distinct (π : Equiv.Perm ↥(trioFin 0)) :
    (codeOf π).1 ≠ (codeOf π).2.1 ∧ (codeOf π).1 ≠ (codeOf π).2.2 ∧
      (codeOf π).2.1 ≠ (codeOf π).2.2 := by
  have h : ∀ i j : Fin 3, i ≠ j → π (brick i) ≠ π (brick j) := by
    intro i j hij hh
    exact hij (brick_injective (π.injective hh))
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    exact h 0 1 (by decide) (posOf_injective hh)
  · intro hh
    exact h 0 2 (by decide) (posOf_injective hh)
  · intro hh
    exact h 1 2 (by decide) (posOf_injective hh)

theorem baseSym (π : Equiv.Perm ↥(trioFin 0)) :
    ∃ σ ∈ M24g, ∀ O : ↥(trioFin 0), σ • O.1 = (π O).1 := by
  obtain ⟨i, hi⟩ := tabCode_wordTab (codeOf π) (codeOf_distinct π)
  refine ⟨wordPerm i, wordPerm_mem i, fun O => ?_⟩
  have hπ : actPerm (trioFin 0) (wordPerm i) (wordPerm_fix i) = π :=
    codeOf_injective (by rw [codeOf_actPerm, hi])
  have h' := congrArg (fun (e : Equiv.Perm ↥(trioFin 0)) => (e O).1) hπ
  show wordPerm i • O.1 = (π O).1
  exact h'

theorem fixOctSym_holds : FixOctSym := by
  intro l hl π
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have hinv : g⁻¹ • trioFin 0 = l := by rw [← hgl, inv_smul_smul]
  let e : ↥l → ↥(trioFin 0) := fun O =>
    ⟨g • O.1, by
      have h1 := Finset.smul_mem_smul_finset (a := g) O.2
      rwa [hgl] at h1⟩
  let e' : ↥(trioFin 0) → ↥l := fun X =>
    ⟨g⁻¹ • X.1, by
      have h1 := Finset.smul_mem_smul_finset (a := g⁻¹) X.2
      rwa [hinv] at h1⟩
  have he_left : ∀ O : ↥l, e' (e O) = O := by
    intro O
    apply Subtype.ext
    simp [e, e']
  have he_right : ∀ X : ↥(trioFin 0), e (e' X) = X := by
    intro X
    apply Subtype.ext
    simp [e, e']
  let ee : ↥l ≃ ↥(trioFin 0) :=
    { toFun := e, invFun := e', left_inv := he_left, right_inv := he_right }
  let π' : Equiv.Perm ↥(trioFin 0) := (ee.symm.trans π).trans ee
  obtain ⟨σ', hσ', hbase⟩ := baseSym π'
  refine ⟨g⁻¹ * σ' * g, M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hg) hσ') hg, fun O => ?_⟩
  have hσ'O : σ' • (ee O).1 = (π' (ee O)).1 := hbase (ee O)
  have hpi : (π' (ee O)).1 = g • (π O).1 := by
    simp only [π', Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  calc (g⁻¹ * σ' * g) • O.1 = g⁻¹ • (σ' • (g • O.1)) := by simp only [mul_smul]
    _ = g⁻¹ • (π' (ee O)).1 := by
        rw [show g • O.1 = (ee O).1 from rfl, hσ'O]
    _ = (π O).1 := by rw [hpi, inv_smul_smul]

end Sym


section Perfect


theorem fixOctPerfectCheck_parts (h : Native.fixOctPerfectCheck () = true) :
    ∀ f ∈ Native.fixOctPerfectCheckParts (), f = true := by
  have h' := h
  unfold Native.fixOctPerfectCheck at h'
  rwa [List.all_eq_true] at h'

theorem closureSizeOK_spec (h : Native.fixOctPerfectCheck () = true) :
    10752 ≤ (Native.fixOctClosure ()).1.size := by
  have hmem : Native.closureSizeOK (Native.fixOctClosure ()) ∈
      Native.fixOctPerfectCheckParts () := by
    simp [Native.fixOctPerfectCheckParts]
  have h2 := fixOctPerfectCheck_parts h _ hmem
  simpa [Native.closureSizeOK, decide_eq_true_eq] using h2

theorem closureBaseOK_spec (h : Native.fixOctPerfectCheck () = true) :
    (Native.fixOctClosure ()).1[0]! = Native.fixOctIdTab := by
  have hmem : Native.closureBaseOK (Native.fixOctClosure ()) ∈
      Native.fixOctPerfectCheckParts () := by
    simp [Native.fixOctPerfectCheckParts]
  have h2 := fixOctPerfectCheck_parts h _ hmem
  simpa [Native.closureBaseOK, beq_iff_eq] using h2

theorem closureNodupOK_spec (h : Native.fixOctPerfectCheck () = true) :
    (Native.fixOctClosure ()).1.toList.Nodup := by
  have hmem : Native.closureNodupOK (Native.fixOctClosure ()) ∈
      Native.fixOctPerfectCheckParts () := by
    simp [Native.fixOctPerfectCheckParts]
  have h2 := fixOctPerfectCheck_parts h _ hmem
  simpa [Native.closureNodupOK, decide_eq_true_eq] using h2

theorem closureWidthOK_spec (h : Native.fixOctPerfectCheck () = true) :
    ∀ p, p < (Native.fixOctClosure ()).1.size → ((Native.fixOctClosure ()).1[p]!).size = 24 := by
  have hmem : Native.closureWidthOK (Native.fixOctClosure ()) ∈
      Native.fixOctPerfectCheckParts () := by
    simp [Native.fixOctPerfectCheckParts]
  have h2 := fixOctPerfectCheck_parts h _ hmem
  simp only [Native.closureWidthOK, Native.allLt_iff, beq_iff_eq] at h2
  exact h2

theorem closureTreeOK_spec (h : Native.fixOctPerfectCheck () = true) :
    ∀ p, p < (Native.fixOctClosure ()).1.size → p = 0 ∨
      ((Native.fixOctClosure ()).2.1[p]! < p ∧ (Native.fixOctClosure ()).2.2[p]! < 2 ∧
        Native.mulTab ((Native.fixOctComms ()).getD ((Native.fixOctClosure ()).2.2[p]!) #[])
          (Native.fixOctClosure ()).1[(Native.fixOctClosure ()).2.1[p]!]! =
          (Native.fixOctClosure ()).1[p]!) := by
  have hmem : Native.closureTreeOK (Native.fixOctComms ()) (Native.fixOctClosure ()) ∈
      Native.fixOctPerfectCheckParts () := by
    simp [Native.fixOctPerfectCheckParts]
  have h2 := fixOctPerfectCheck_parts h _ hmem
  simp only [Native.closureTreeOK, Native.allLt_iff, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h2
  exact h2

@[expose] def permA1 : Equiv.Perm (Fin 24) where
  toFun := ![4, 3, 1, 6, 0, 7, 5, 2, 15, 8, 10, 13, 11, 12, 14, 9, 21, 18, 16, 23, 17, 22, 20, 19]
  invFun := ![4, 2, 7, 1, 0, 6, 3, 5, 9, 15, 10, 12, 13, 11, 14, 8, 18, 20, 17, 23, 22, 16, 21, 19]
  left_inv := by decide
  right_inv := by decide

@[expose] def permB1 : Equiv.Perm (Fin 24) where
  toFun := ![3, 1, 2, 0, 5, 7, 4, 6, 14, 12, 15, 13, 8, 10, 9, 11, 16, 18, 17, 19, 22, 20, 23, 21]
  invFun := ![3, 1, 2, 0, 6, 4, 7, 5, 12, 14, 13, 15, 9, 11, 8, 10, 16, 18, 17, 19, 21, 23, 20, 22]
  left_inv := by decide
  right_inv := by decide

@[expose] def permA2 : Equiv.Perm (Fin 24) where
  toFun := ![6, 0, 7, 1, 2, 4, 3, 5, 10, 12, 11, 13, 14, 8, 15, 9, 21, 19, 20, 18, 17, 23, 16, 22]
  invFun := ![1, 3, 4, 6, 5, 7, 0, 2, 13, 15, 8, 10, 9, 11, 12, 14, 22, 20, 19, 17, 18, 16, 23, 21]
  left_inv := by decide
  right_inv := by decide

@[expose] def permB2 : Equiv.Perm (Fin 24) where
  toFun := ![7, 6, 4, 5, 2, 3, 1, 0, 13, 12, 14, 15, 8, 9, 11, 10, 21, 20, 22, 23, 16, 17, 19, 18]
  invFun := ![7, 6, 4, 5, 2, 3, 1, 0, 12, 13, 15, 14, 9, 8, 10, 11, 20, 21, 23, 22, 17, 16, 18, 19]
  left_inv := by decide
  right_inv := by decide

@[expose] def fixOctTab : Fin 4 → Array ℕ :=
  ![Native.fixOctA1, Native.fixOctB1, Native.fixOctA2, Native.fixOctB2]

@[expose] def fixOctPerm : Fin 4 → Equiv.Perm (Fin 24) := ![permA1, permB1, permA2, permB2]

theorem repT_fixOctTab (i : Fin 4) : RepT (fixOctTab i) (fixOctPerm i) := by
  revert i
  unfold fixOctTab fixOctPerm RepT
  decide +kernel

private theorem fixOctPerm_basis : ∀ (i : Fin 4) (j : Fin 12),
    CFSG.Monster.Code.B j ∘ ⇑(fixOctPerm i) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem fixOctPerm_basis' : ∀ (i : Fin 4) (j : Fin 12),
    CFSG.Monster.Code.B j ∘ ⇑(fixOctPerm i)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem fixOctPerm_mem (i : Fin 4) : fixOctPerm i ∈ M24g :=
  mem_AutPerm_of_basis (fixOctPerm_basis i) (fixOctPerm_basis' i)

theorem fixOctTab_img (i : Fin 4) :
    Native.img (fixOctTab i) 255 = 255 ∧ Native.img (fixOctTab i) 65280 = 65280 ∧
      Native.img (fixOctTab i) 16711680 = 16711680 := by
  revert i
  unfold fixOctTab
  decide +kernel

theorem fixOctPerm_mem_fixOct (i : Fin 4) : fixOctPerm i ∈ fixOct (trioFin 0) := by
  rw [mem_fixOct]
  refine ⟨fixOctPerm_mem i, fun O hO => ?_⟩
  obtain ⟨e1, e2, e3⟩ := fixOctTab_img i
  simp only [trioFin_zero_eq, Finset.mem_insert, Finset.mem_singleton] at hO
  rcases hO with rfl | rfl | rfl
  · rw [← maskFin_img (repT_fixOctTab i) 255, e1]
  · rw [← maskFin_img (repT_fixOctTab i) 65280, e2]
  · rw [← maskFin_img (repT_fixOctTab i) 16711680, e3]

theorem repT_comm1 : RepT Native.fixOctComm1 ⁅fixOctPerm 0, fixOctPerm 1⁆ := by
  unfold RepT Native.fixOctComm1 fixOctPerm
  decide +kernel

theorem repT_comm2 : RepT Native.fixOctComm2 ⁅fixOctPerm 2, fixOctPerm 3⁆ := by
  unfold RepT Native.fixOctComm2 fixOctPerm
  decide +kernel

@[expose] def commPair : Fin 2 → S24 :=
  fun j => if j = 0 then ⁅fixOctPerm 0, fixOctPerm 1⁆ else ⁅fixOctPerm 2, fixOctPerm 3⁆

theorem repT_commPair (j : Fin 2) :
    RepT ((Native.fixOctComms ()).getD j #[]) (commPair j) := by
  fin_cases j
  · simpa [Native.fixOctComms, commPair] using repT_comm1
  · simpa [Native.fixOctComms, commPair] using repT_comm2

theorem repT_of_closure_tree {gens : List (Array ℕ)} {P : Fin 2 → S24}
    (hP : ∀ j : Fin 2, RepT (gens.getD j #[]) (P j))
    {L : Array (Array ℕ)} {par gen : Array ℕ}
    (h0 : L[0]! = Native.fixOctIdTab)
    (hall : ∀ p, p < L.size → p = 0 ∨ (par[p]! < p ∧ gen[p]! < 2 ∧
      Native.mulTab (gens.getD gen[p]! #[]) L[par[p]!]! = L[p]!)) :
    ∀ p, p < L.size → ∃ σ ∈ Subgroup.closure (Set.range P), RepT L[p]! σ := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    rcases hall p hp with rfl | ⟨hpar, hgen, hstep⟩
    · exact ⟨1, Subgroup.one_mem _, by rw [h0]; exact repT_idTab⟩
    · obtain ⟨σ, hσ, hσT⟩ := ih par[p]! hpar (lt_trans hpar hp)
      refine ⟨P ⟨gen[p]!, hgen⟩ * σ, ?_, ?_⟩
      · exact (Subgroup.closure (Set.range P)).mul_mem
          (Subgroup.subset_closure ⟨⟨gen[p]!, hgen⟩, rfl⟩) hσ
      · rw [← hstep]
        exact repT_mulTab (hP ⟨gen[p]!, hgen⟩) hσT

theorem closure_card_lower :
    10752 ≤ Nat.card ↥(Subgroup.closure (Set.range commPair)) := by
  have hcert := Certificates.certificate664001
  have hsize := closureSizeOK_spec hcert
  have hbase := closureBaseOK_spec hcert
  have hnd := closureNodupOK_spec hcert
  have hall := closureTreeOK_spec hcert
  have hrep := repT_of_closure_tree (gens := Native.fixOctComms ()) (P := commPair)
    repT_commPair (L := (Native.fixOctClosure ()).1) (par := (Native.fixOctClosure ()).2.1)
    (gen := (Native.fixOctClosure ()).2.2) hbase hall
  have hinj : Function.Injective (fun p : Fin (Native.fixOctClosure ()).1.size =>
      (⟨Classical.choose (hrep p.1 p.2),
        (Classical.choose_spec (hrep p.1 p.2)).1⟩ :
        ↥(Subgroup.closure (Set.range commPair)))) := by
    intro p q hpq
    have hσ : Classical.choose (hrep p.1 p.2) = Classical.choose (hrep q.1 q.2) := by
      simpa using congrArg Subtype.val hpq
    have hL' : (Native.fixOctClosure ()).1[p.1]! = (Native.fixOctClosure ()).1[q.1]! := by
      have hw : (Native.fixOctClosure ()).1[p.1]!.size =
          (Native.fixOctClosure ()).1[q.1]!.size := by
        have h1 : (Native.fixOctClosure ()).1[p.1]!.size = 24 :=
          closureWidthOK_spec hcert p.1 p.2
        have h2 : (Native.fixOctClosure ()).1[q.1]!.size = 24 :=
          closureWidthOK_spec hcert q.1 q.2
        exact h1.trans h2.symm
      apply Array.ext hw
      intro k hk hk'
      have hk24 : k < 24 := by
        have h := hk
        rw [closureWidthOK_spec hcert p.1 p.2] at h
        exact h
      have hk24' : k < 24 := by
        have h := hk'
        rw [closureWidthOK_spec hcert q.1 q.2] at h
        exact h
      rw [← getElem!_pos _ k hk, ← getElem!_pos _ k hk']
      rw [show ((Native.fixOctClosure ()).1[p.1]!)[k]! =
          (Classical.choose (hrep p.1 p.2) ⟨k, hk24⟩).val from
          (Classical.choose_spec (hrep p.1 p.2)).2 ⟨k, hk24⟩,
        show ((Native.fixOctClosure ()).1[q.1]!)[k]! =
          (Classical.choose (hrep q.1 q.2) ⟨k, hk24'⟩).val from
          (Classical.choose_spec (hrep q.1 q.2)).2 ⟨k, hk24'⟩, hσ]
    have hget : (Native.fixOctClosure ()).1.toList[p.1]'(by simpa using p.2) =
        (Native.fixOctClosure ()).1.toList[q.1]'(by simpa using q.2) := by
      rw [Array.getElem_toList, Array.getElem_toList,
        ← getElem!_pos _ p.1 p.2, ← getElem!_pos _ q.1 q.2]
      exact hL'
    exact Fin.ext (List.Nodup.getElem_inj hnd |>.1 hget)
  calc 10752 ≤ (Native.fixOctClosure ()).1.size := hsize
    _ = Nat.card (Fin (Native.fixOctClosure ()).1.size) := by simp
    _ ≤ Nat.card ↥(Subgroup.closure (Set.range commPair)) :=
        Nat.card_le_card_of_injective _ hinj

theorem comm_closure_le :
    Subgroup.closure (Set.range commPair) ≤ ⁅fixOct (trioFin 0), fixOct (trioFin 0)⁆ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact Subgroup.commutator_mem_commutator (fixOctPerm_mem_fixOct 0) (fixOctPerm_mem_fixOct 1)
  · exact Subgroup.commutator_mem_commutator (fixOctPerm_mem_fixOct 2) (fixOctPerm_mem_fixOct 3)

@[expose] noncomputable def stabTrio0Act : ↥StabTrio0 →* Equiv.Perm ↥(trioFin 0) where
  toFun σ := actPerm (trioFin 0) (σ : S24) (mem_StabTrio0.1 σ.2).2
  map_one' := by
    refine Equiv.ext fun O => ?_
    apply Subtype.ext
    simp [actPerm]
  map_mul' := by
    intro σ τ
    refine Equiv.ext fun O => ?_
    apply Subtype.ext
    simp [actPerm, mul_smul]

theorem stabTrio0Act_ker :
    stabTrio0Act.ker = (fixOct (trioFin 0)).subgroupOf StabTrio0 := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_fixOct]
  constructor
  · intro h
    refine ⟨(mem_StabTrio0.1 σ.2).1, fun O hO => ?_⟩
    have h' := congrArg
      (fun (e : Equiv.Perm ↥(trioFin 0)) => (e ⟨O, hO⟩).1) h
    simpa [stabTrio0Act, actPerm] using h'
  · rintro ⟨hM, hfix⟩
    refine Equiv.ext fun O => ?_
    exact Subtype.ext (hfix O.1 O.2)

theorem fixOct_le_stab : fixOct (trioFin 0) ≤ StabTrio0 := by
  intro σ hσ
  rw [mem_StabTrio0]
  refine ⟨fixOct_le_M24g _ hσ, ?_⟩
  ext O
  simp only [Finset.mem_smul_finset]
  constructor
  · rintro ⟨O', hO', rfl⟩
    rw [(mem_fixOct.1 hσ).2 O' hO']
    exact hO'
  · intro hO
    exact ⟨O, hO, (mem_fixOct.1 hσ).2 O hO⟩

theorem stabTrio0Act_range : stabTrio0Act.range = ⊤ := by
  rw [eq_top_iff]
  rintro π -
  obtain ⟨i, hi⟩ := tabCode_wordTab (codeOf π) (codeOf_distinct π)
  have hπ : actPerm (trioFin 0) (wordPerm i) (wordPerm_fix i) = π :=
    codeOf_injective (by rw [codeOf_actPerm, hi])
  have hmem0 : wordPerm i ∈ StabTrio0 :=
    mem_StabTrio0.2 ⟨wordPerm_mem i, wordPerm_fix i⟩
  exact ⟨⟨wordPerm i, hmem0⟩, hπ⟩

theorem card_fixOct_trioFin : Nat.card ↥(fixOct (trioFin 0)) = 10752 := by
  have hrange := stabTrio0Act_range
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup stabTrio0Act.ker
  have hq : Nat.card (↥StabTrio0 ⧸ stabTrio0Act.ker) = 6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange stabTrio0Act).toEquiv, hrange,
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe,
      show (trioFin 0).card = 3 from by rw [trioFin_zero_eq]; decide]
    decide
  have hker : Nat.card ↥stabTrio0Act.ker = Nat.card ↥(fixOct (trioFin 0)) := by
    rw [stabTrio0Act_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixOct_le_stab).toEquiv
  rw [hker, hq, card_StabTrio0] at hcard
  omega

theorem perfect_base :
    ⁅fixOct (trioFin 0), fixOct (trioFin 0)⁆ = fixOct (trioFin 0) := by
  have hlow := closure_card_lower
  have hcard : 10752 ≤ Nat.card ↥⁅fixOct (trioFin 0), fixOct (trioFin 0)⁆ :=
    le_trans hlow (Nat.card_le_card_of_injective
      (fun x : ↥(Subgroup.closure (Set.range commPair)) =>
        (⟨x.1, comm_closure_le x.2⟩ : ↥⁅fixOct (trioFin 0), fixOct (trioFin 0)⁆))
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)))
  have hcommle : ⁅fixOct (trioFin 0), fixOct (trioFin 0)⁆ ≤ fixOct (trioFin 0) := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    exact (fixOct (trioFin 0)).mul_mem ((fixOct (trioFin 0)).mul_mem
      ((fixOct (trioFin 0)).mul_mem h₁ h₂) ((fixOct (trioFin 0)).inv_mem h₁))
      ((fixOct (trioFin 0)).inv_mem h₂)
  refine Subgroup.eq_of_le_of_card_ge hcommle ?_
  rw [card_fixOct_trioFin]
  exact hcard

theorem fixOct_smul_eq {l : Finset (Finset (Fin 24))} {g : S24} (hg : g ∈ M24g) :
    fixOct (g • l) = (fixOct l).map (MulAut.conj g).toMonoidHom := by
  have key : ∀ τ : S24, τ ∈ fixOct (g • l) ↔ g⁻¹ * τ * g ∈ fixOct l := by
    intro τ
    have h := fixOct_conj_iff (l := g • l) (σ := g⁻¹) (τ := τ) (M24g.inv_mem hg)
    simpa using h
  ext τ
  rw [Subgroup.mem_map, key]
  constructor
  · intro h
    exact ⟨g⁻¹ * τ * g, h, by show g * (g⁻¹ * τ * g) * g⁻¹ = τ; group⟩
  · rintro ⟨x, hx, hxτ⟩
    rw [← hxτ]
    show g⁻¹ * (g * x * g⁻¹) * g ∈ fixOct l
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x from by group]

theorem fixOctPerfect_holds : FixOctPerfect := by
  intro l hl
  have hbase := perfect_base
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have hl' : l = g⁻¹ • trioFin 0 := by rw [← hgl, inv_smul_smul]
  rw [hl', fixOct_smul_eq (l := trioFin 0) (g := g⁻¹) (M24g.inv_mem hg),
    ← Subgroup.map_commutator, hbase]

end Perfect

section CommW11


@[expose] def commSet (l : Finset (Finset (Fin 24))) : Set W11 :=
  {x : W11 | ∃ (w : W11) (σ : ↥AutPerm), (σ : S24) ∈ fixOct l ∧
    x = w * (rho11 AutPerm le_rfl σ w)⁻¹}

theorem W11_inv_eq_self (x : W11) : x⁻¹ = x := by
  apply inv_eq_of_mul_eq_one_right
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem toW_mul_self (n z : ℕ) : toW n z * toW n z = 1 := by
  rw [← toW_xor, Nat.xor_self, toW_zero]

theorem toW_inv (n z : ℕ) : (toW n z)⁻¹ = toW n z :=
  inv_eq_of_mul_eq_one_right (toW_mul_self n z)

theorem lTabs_one_bricks :
    Native.img (Native.lTabs.getD ((1 : Fin 4) : ℕ) #[]) 255 = 255 ∧
      Native.img (Native.lTabs.getD ((1 : Fin 4) : ℕ) #[]) 65280 = 65280 ∧
        Native.img (Native.lTabs.getD ((1 : Fin 4) : ℕ) #[]) 16711680 = 16711680 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem lPerm_one_mem_fixOct : (lPerm 1 : S24) ∈ fixOct (trioFin 0) := by
  obtain ⟨e1, e2, e3⟩ := lTabs_one_bricks
  rw [mem_fixOct]
  refine ⟨lPerm_mem 1, fun O hO => ?_⟩
  simp only [trioFin_zero_eq, Finset.mem_insert, Finset.mem_singleton] at hO
  rcases hO with rfl | rfl | rfl
  · rw [← maskFin_img (repT_lPerm 1) 255, e1]
  · rw [← maskFin_img (repT_lPerm 1) 65280, e2]
  · rw [← maskFin_img (repT_lPerm 1) 16711680, e3]

@[expose] def commMask : Fin 9 → ℕ := ![16, 32, 64, 128, 256, 512, 1024, 3, 12]

@[expose] def commPre : Fin 9 → ℕ := ![746, 215, 188, 104, 163, 743, 179, 136, 566]

@[expose] def commMaskList : List ℕ := List.ofFn commMask

theorem comm_act (j : Fin 9) :
    commPre j ^^^ act11 (Native.lTabs.getD 1 #[]) (commPre j) = commMask j := by
  revert j
  decide +kernel

theorem commMask_lt (j : Fin 9) : commMask j < 2 ^ 11 := by
  revert j
  decide +kernel

theorem commMaskList_nodup : (combos commMaskList).Nodup := by
  unfold commMaskList commMask
  decide +kernel

theorem comm_mask_mem (j : Fin 9) : toW 11 (commMask j) ∈ commSet (trioFin 0) := by
  have harr : HasArr ((⟨lPerm 1, lPerm_mem 1⟩ : ↥AutPerm) : S24) (Native.lTabs.getD 1 #[]) :=
    hasArr_of_repT (repT_lPerm 1)
  have hrho : rho11 AutPerm le_rfl (⟨lPerm 1, lPerm_mem 1⟩ : ↥AutPerm)
      (toW 11 (commPre j)) = toW 11 (act11 (Native.lTabs.getD 1 #[]) (commPre j)) :=
    rho11_toW AutPerm le_rfl _ harr _
  have hx : toW 11 (commMask j) =
      toW 11 (commPre j) * (rho11 AutPerm le_rfl (⟨lPerm 1, lPerm_mem 1⟩ : ↥AutPerm)
        (toW 11 (commPre j)))⁻¹ := by
    rw [hrho, toW_inv, ← toW_xor, comm_act]
  have hmem : toW 11 (commMask j) ∈ commSet (trioFin 0) :=
    ⟨toW 11 (commPre j), (⟨lPerm 1, lPerm_mem 1⟩ : ↥AutPerm), lPerm_one_mem_fixOct, hx⟩
  exact hmem

theorem commW11_base : 2 ^ 9 ≤ Nat.card ↥(Subgroup.closure (commSet (trioFin 0))) := by
  have hnd := commMaskList_nodup
  have hlt : ∀ a ∈ commMaskList, a < 2 ^ 11 := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    exact commMask_lt j
  have hU : ∀ a ∈ commMaskList, (MaskCoords.std 11).vm a ∈
      Subgroup.closure (commSet (trioFin 0)) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    simpa [MaskCoords.std] using Subgroup.subset_closure (comm_mask_mem j)
  have h := MaskCoords.pow_le_card (MaskCoords.std 11) (Subgroup.closure (commSet (trioFin 0)))
    commMaskList hnd hlt hU
  simpa [commMaskList] using h

private theorem rho11_inv_apply (g : ↥AutPerm) (w : W11) :
    (rho11 AutPerm le_rfl g)⁻¹ (rho11 AutPerm le_rfl g w) = w := by
  simp only [MulAut.inv_apply]
  exact MulEquiv.symm_apply_apply _ _

theorem rho11_conj (g τ : ↥AutPerm) (w : W11) :
    rho11 AutPerm le_rfl (g * τ * g⁻¹) (rho11 AutPerm le_rfl g w) =
      rho11 AutPerm le_rfl g (rho11 AutPerm le_rfl τ w) := by
  rw [map_mul, map_mul, map_inv]
  simp only [MulAut.mul_apply]
  rw [rho11_inv_apply]

theorem commSet_map {g : S24} (hg : g ∈ M24g) {w : W11} (σ : ↥AutPerm)
    (hσ : (σ : S24) ∈ fixOct (trioFin 0)) :
    rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm)
        (w * (rho11 AutPerm le_rfl σ w)⁻¹) ∈ commSet (g • trioFin 0) := by
  have hσM : (σ : S24) ∈ M24g := (mem_fixOct.1 hσ).1
  have hconjM : g * (σ : S24) * g⁻¹ ∈ M24g :=
    M24g.mul_mem (M24g.mul_mem hg hσM) (M24g.inv_mem hg)
  have hconjfix : g * (σ : S24) * g⁻¹ ∈ fixOct (g • trioFin 0) :=
    (fixOct_conj_iff (l := trioFin 0) hg).1 hσ
  refine ⟨rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm) w,
    (⟨g * (σ : S24) * g⁻¹, hconjM⟩ : ↥AutPerm), hconjfix, ?_⟩
  have hstep : rho11 AutPerm le_rfl (⟨g * (σ : S24) * g⁻¹, hconjM⟩ : ↥AutPerm)
      (rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm) w) =
      rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm) (rho11 AutPerm le_rfl σ w) :=
    rho11_conj ⟨g, hg⟩ σ w
  have hdiv : rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm)
      (w * (rho11 AutPerm le_rfl σ w)⁻¹) =
      rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm) w *
        (rho11 AutPerm le_rfl (⟨g, hg⟩ : ↥AutPerm) (rho11 AutPerm le_rfl σ w))⁻¹ := by
    rw [map_mul, W11_inv_eq_self, W11_inv_eq_self]
  rw [hdiv, hstep]

theorem fixOctCommW11_holds : FixOctCommW11 := by
  intro l hl
  change 2 ^ 9 ≤ Nat.card ↥(Subgroup.closure (commSet l))
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have hl' : l = g⁻¹ • trioFin 0 := by rw [← hgl, inv_smul_smul]
  have hsub : (fun x => rho11 AutPerm le_rfl (⟨g⁻¹, M24g.inv_mem hg⟩ : ↥AutPerm) x) ''
      commSet (trioFin 0) ⊆ commSet (g⁻¹ • trioFin 0) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨w, σ, hσ, rfl⟩ := hy
    exact commSet_map (M24g.inv_mem hg) σ hσ
  have hcl : (Subgroup.closure (commSet (trioFin 0))).map
      (rho11 AutPerm le_rfl (⟨g⁻¹, M24g.inv_mem hg⟩ : ↥AutPerm)).toMonoidHom ≤
      Subgroup.closure (commSet (g⁻¹ • trioFin 0)) := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hsub
  have hcard : Nat.card ↥((Subgroup.closure (commSet (trioFin 0))).map
      (rho11 AutPerm le_rfl (⟨g⁻¹, M24g.inv_mem hg⟩ : ↥AutPerm)).toMonoidHom) =
      Nat.card ↥(Subgroup.closure (commSet (trioFin 0))) :=
    Subgroup.card_map_of_injective (rho11 AutPerm le_rfl _).injective
  rw [hl']
  calc 2 ^ 9 ≤ Nat.card ↥(Subgroup.closure (commSet (trioFin 0))) := commW11_base
    _ = Nat.card ↥((Subgroup.closure (commSet (trioFin 0))).map
        (rho11 AutPerm le_rfl (⟨g⁻¹, M24g.inv_mem hg⟩ : ↥AutPerm)).toMonoidHom) := hcard.symm
    _ ≤ Nat.card ↥(Subgroup.closure (commSet (g⁻¹ • trioFin 0))) :=
        Nat.card_le_card_of_injective
          (fun x => (⟨x.1, hcl x.2⟩ : ↥(Subgroup.closure (commSet (g⁻¹ • trioFin 0)))))
          (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

end CommW11
