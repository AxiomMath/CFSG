module

public import CFSG.Sporadic.SuzRecog.MixedCellCert
public import CFSG.Sporadic.SuzRecog.RootTwistCentre
public import CFSG.Sporadic.SuzRecog.C1ModelT0
public import CFSG.Sporadic.SuzRecog.LevelTwoCover

public section

namespace CFSG.Sporadic.SuzRecog.MixedCell

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ModelGroupsCheck
  CFSG.Sporadic.SuzRecog.B0TwistData CFSG.Sporadic.SuzRecog.MixedCellData
  CFSG.Sporadic.SuzRecog.MixedCellCheck CFSG.Certificates.CosetEnumeration
  CFSG.ComponentClassification.PSL3Four

@[expose] noncomputable def h1 : Equiv.Perm (Fin 1782) := permC 1782 h1Arr

@[expose] noncomputable def h2 : Equiv.Perm (Fin 1782) := permC 1782 h2Arr

@[expose] noncomputable def ja : Equiv.Perm (Fin 1782) := permC 1782 aArr

@[expose] noncomputable def jb : Equiv.Perm (Fin 1782) := permC 1782 bArr

@[expose] noncomputable def sP : Equiv.Perm (Fin 1782) := permC 1782 LevelTwo.swapE.1

@[expose] noncomputable def p1P : Equiv.Perm (Fin 1782) := LevelTwo.aP LevelTwo.p1

@[expose] noncomputable def wP : Equiv.Perm (Fin 1782) := suzInv 1 * LevelTwo.aP LevelTwo.p1

@[expose] noncomputable def cP (j : Fin 2) : Equiv.Perm (Fin 1782) :=
  permC 1782 (LevelTwo.cellC (2 * j.val)).1

@[expose] noncomputable def cP' (j : Fin 2) : Equiv.Perm (Fin 1782) :=
  permC 1782 (LevelTwo.cellC' (2 * j.val)).1

@[expose] noncomputable def letter : ℕ → Equiv.Perm (Fin 1782)
  | 0 => h1
  | 1 => h2
  | 2 => Model.rho1
  | 3 => ja
  | 4 => jb
  | 5 => sP
  | 6 => C1Model.tau0
  | 7 => Model.w0
  | _ => 1

@[expose] noncomputable def genM (c : ℕ) : Equiv.Perm (Fin 1782) :=
  if c % 2 = 0 then letter (c / 2) else (letter (c / 2))⁻¹

@[expose] noncomputable def xM : Equiv.Perm (Fin 1782) := evalWord genM xW

theorem coe_sX : (LevelTwo.sX : Equiv.Perm (Fin 1782)) = sP :=
  rfl

theorem coe_cX (j : Fin 2) :
    (LevelTwo.cX (LevelTwoCover.mixK j) : Equiv.Perm (Fin 1782)) = cP j := rfl

theorem coe_c'X (j : Fin 2) :
    (LevelTwo.c'X (LevelTwoCover.mixK j) : Equiv.Perm (Fin 1782)) = cP' j := rfl

theorem perms_parts :
    permOK h1Arr = true ∧ permOK h2Arr = true ∧ permOK aArr = true ∧ permOK bArr = true ∧
      permOK p1A = true ∧ permOK sA = true ∧ permOK (cA 0) = true ∧ permOK (cpA 0) = true ∧
      permOK (cA 2) = true ∧ permOK (cpA 2) = true := by
  have h := perms_check
  simp only [mcPermsOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem members_parts :
    inM h1Arr = true ∧ inM h2Arr = true ∧ inM aArr = true ∧ inM bArr = true := by
  have h := members_check
  simp only [mcMembersOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem comm_parts :
    commA h1Arr t1A = true ∧ commA h1Arr rhoArr = true ∧ commA h2Arr t1A = true ∧
      commA h2Arr rhoArr = true ∧ commA aArr rhoArr = true ∧ normR0 aArr = true ∧
      commA bArr rhoArr = true ∧ normR0 bArr = true := by
  have h := comm_check
  simp only [mcCommOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem rep_h1 : Rep 1782 h1Arr h1 :=
  (rep_permC perms_parts.1).1

theorem rep_h2 : Rep 1782 h2Arr h2 :=
  (rep_permC perms_parts.2.1).1

theorem rep_ja : Rep 1782 aArr ja :=
  (rep_permC perms_parts.2.2.1).1

theorem rep_jb : Rep 1782 bArr jb :=
  (rep_permC perms_parts.2.2.2.1).1

theorem rep_p1 : Rep 1782 p1A p1P :=
  (rep_permC perms_parts.2.2.2.2.1).1

theorem rep_s : Rep 1782 sA sP :=
  (rep_permC perms_parts.2.2.2.2.2.1).1

theorem rep_c (j : Fin 2) : Rep 1782 (cA (2 * j.val)) (cP j) := by
  fin_cases j
  · exact (rep_permC perms_parts.2.2.2.2.2.2.1).1
  · exact (rep_permC perms_parts.2.2.2.2.2.2.2.2.1).1

theorem rep_c' (j : Fin 2) :
    Rep 1782 (cpA (2 * j.val)) (cP' j) := by
  fin_cases j
  · exact (rep_permC perms_parts.2.2.2.2.2.2.2.1).1
  · exact (rep_permC perms_parts.2.2.2.2.2.2.2.2.2).1

theorem rep_w : Rep 1782 wA wP :=
  rep_compA ModelGroups.rep_t1 rep_p1

theorem rep_e (j : Fin 2) :
    Rep 1782 (eA (2 * j.val)) ((cP j)⁻¹ * sP * cP' j) := by
  have h := rep_compA (ModelGroups.rep_invCand (rep_c j)) (rep_compA rep_s (rep_c' j))
  rwa [← mul_assoc] at h

theorem rep_conjInv {g a : Array ℕ} {G A : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (ha : Rep 1782 a A) : Rep 1782 (conjInvA g a) (G⁻¹ * A * G) := by
  rw [mul_assoc]
  exact rep_compA (ModelGroups.rep_invCand hg) (rep_compA ha hg)

theorem rep_letter
    {i : ℕ} (hi : i < 8) : Rep 1782 mcGens[i]! (letter i) := by
  interval_cases i
  · simpa [mcGens, letter] using rep_h1
  · simpa [mcGens, letter] using rep_h2
  · simpa [mcGens, letter] using ModelGroups.rep_rho1
  · simpa [mcGens, letter] using rep_ja
  · simpa [mcGens, letter] using rep_jb
  · simpa [mcGens, letter] using rep_s
  · simpa [mcGens, letter] using ModelGroups.rep_tau0
  · simpa [mcGens, letter] using ModelGroups.rep_w0

theorem rep_code
    {c : ℕ} (hc : c < 16) : Rep 1782 (mcCodeA c) (genM c) := by
  unfold mcCodeA genM
  split
  · exact rep_letter (by omega)
  · exact ModelGroups.rep_invCand (rep_letter (by omega))

theorem rep_word :
    ∀ {w : List ℕ}, (∀ c ∈ w, c < 16) → Rep 1782 (mcWordA w) (evalWord genM w)
  | [], _ => rep_idA
  | c :: w, hw => by
    rw [evalWord_cons]
    exact rep_compA (rep_code (hw c (by simp))) (rep_word fun c' hc' => hw c' (by simp [hc']))

theorem h1_mem :
    h1 ∈ invE 1 ⊓ Model.Crho1 :=
  mem_inf.2 ⟨ModelGroups.mem_invE_one_iff.2
      ⟨(ModelGroups.commA_iff rep_h1 ModelGroups.rep_t1).1 comm_parts.1,
        (inM_iff rep_h1).1 members_parts.1⟩,
    ModelGroups.mem_Crho1_iff.2 ⟨(ModelGroups.commA_iff rep_h1 ModelGroups.rep_rho1).1
      comm_parts.2.1, (inM_iff rep_h1).1 members_parts.1⟩⟩

theorem h2_mem :
    h2 ∈ invE 1 ⊓ Model.Crho1 :=
  mem_inf.2 ⟨ModelGroups.mem_invE_one_iff.2
      ⟨(ModelGroups.commA_iff rep_h2 ModelGroups.rep_t1).1 comm_parts.2.2.1,
        (inM_iff rep_h2).1 members_parts.2.1⟩,
    ModelGroups.mem_Crho1_iff.2 ⟨(ModelGroups.commA_iff rep_h2 ModelGroups.rep_rho1).1
      comm_parts.2.2.2.1, (inM_iff rep_h2).1 members_parts.2.1⟩⟩

theorem ja_mem :
    ja ∈ Model.Crho1 ⊓ Model.NR0 :=
  mem_inf.2 ⟨ModelGroups.mem_Crho1_iff.2 ⟨(ModelGroups.commA_iff rep_ja ModelGroups.rep_rho1).1
      comm_parts.2.2.2.2.1, (inM_iff rep_ja).1 members_parts.2.2.1⟩,
    ModelGroups.mem_NR0.2 ⟨(inM_iff rep_ja).1 members_parts.2.2.1,
      ModelGroups.mem_normalizer_R0_of_normR0 rep_ja comm_parts.2.2.2.2.2.1⟩⟩

theorem jb_mem :
    jb ∈ Model.Crho1 ⊓ Model.NR0 :=
  mem_inf.2 ⟨ModelGroups.mem_Crho1_iff.2 ⟨(ModelGroups.commA_iff rep_jb ModelGroups.rep_rho1).1
      comm_parts.2.2.2.2.2.2.1, (inM_iff rep_jb).1 members_parts.2.2.2⟩,
    ModelGroups.mem_NR0.2 ⟨(inM_iff rep_jb).1 members_parts.2.2.2,
      ModelGroups.mem_normalizer_R0_of_normR0 rep_jb comm_parts.2.2.2.2.2.2.2⟩⟩

theorem genM_mem {H : Subgroup (Equiv.Perm (Fin 1782))} {c : ℕ} (h : letter (c / 2) ∈ H) :
    genM c ∈ H := by
  unfold genM
  split
  · exact h
  · exact inv_mem h

theorem genM_mem_invE :
    ∀ c, c < 6 ∨ (12 ≤ c ∧ c < 16) → genM c ∈ invE 1 := by
  intro c hc
  refine genM_mem ?_
  have : c / 2 = 0 ∨ c / 2 = 1 ∨ c / 2 = 2 ∨ c / 2 = 6 ∨ c / 2 = 7 := by omega
  rcases this with h | h | h | h | h <;> rw [h]
  · exact (mem_inf.1 h1_mem).1
  · exact (mem_inf.1 h2_mem).1
  · exact C1Model.rho1_mem_invE
  · exact C1Model.tau0_mem_invE
  · exact C1Model.w0_mem_invE

theorem genM_mem_NR0 :
    ∀ c, 4 ≤ c → c < 10 → genM c ∈ Model.NR0 := by
  intro c hc hc'
  refine genM_mem ?_
  have : c / 2 = 2 ∨ c / 2 = 3 ∨ c / 2 = 4 := by omega
  rcases this with h | h | h <;> rw [h]
  · exact ModelGroups.rho1_mem_NR0
  · exact (mem_inf.1 ja_mem).2
  · exact (mem_inf.1 jb_mem).2

theorem letters_parts :
    (∀ r ∈ relsH1, ∀ c ∈ r, c < 6) ∧ (∀ r ∈ relsH2, ∀ c ∈ r, 4 ≤ c ∧ c < 10) ∧
      (∀ p ∈ relsA, (∀ c ∈ p.1, c < 6) ∧ ∀ c ∈ p.2, 4 ≤ c ∧ c < 10) ∧
      (∀ p ∈ edge, (∀ c ∈ p.1, c < 6) ∧ ∀ c ∈ p.2, c < 6) ∧ (∀ c ∈ sq, c < 6) ∧
      (∀ k ∈ [0, 2], ((((((∀ c ∈ cW k, c < 6) ∧ ∀ c ∈ cpW k, c < 6) ∧
        ∀ c ∈ eW k, 4 ≤ c ∧ c < 10) ∧ ∀ w ∈ deltaW k, ∀ c ∈ w, c < 4) ∧
          (deltaW k).length = 16) ∧ ∀ w ∈ boundW k, ∀ c ∈ w, c < 6 ∨ 12 ≤ c ∧ c < 16)) ∧
      (∀ c ∈ kGenAW, c < 4) ∧ (∀ c ∈ kGenBW, c < 4) ∧ ∀ c ∈ xW, c < 4 := by
  have h := letters_check
  simp only [mcLettersOK, codesLt, codesPsi, codesBound, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem relsH1_codes : ∀ r ∈ relsH1, ∀ c ∈ r, c < 6 :=
  letters_parts.1

theorem relsH2_codes :
    ∀ r ∈ relsH2, ∀ c ∈ r, 4 ≤ c ∧ c < 10 :=
  letters_parts.2.1

theorem relsA_codes :
    ∀ p ∈ relsA, (∀ c ∈ p.1, c < 6) ∧ ∀ c ∈ p.2, 4 ≤ c ∧ c < 10 :=
  letters_parts.2.2.1

theorem edge_codes :
    ∀ p ∈ edge, (∀ c ∈ p.1, c < 6) ∧ ∀ c ∈ p.2, c < 6 :=
  letters_parts.2.2.2.1

theorem sq_codes : ∀ c ∈ sq, c < 6 :=
  letters_parts.2.2.2.2.1

theorem two_mul_mem (j : Fin 2) : 2 * j.val ∈ ([0, 2] : List ℕ) := by
  fin_cases j <;> simp

theorem cell_codes (j : Fin 2) :
    (∀ c ∈ cW (2 * j.val), c < 6) ∧ (∀ c ∈ cpW (2 * j.val), c < 6) ∧
      ∀ c ∈ eW (2 * j.val), 4 ≤ c ∧ c < 10 := by
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩ := letters_parts.2.2.2.2.2.1 _ (two_mul_mem j)
  exact ⟨h1, h2, h3⟩

theorem delta_codes (j : Fin 2) :
    ∀ n, ∀ c ∈ (deltaW (2 * j.val)).getD n [], c < 4 := by
  have h := (letters_parts.2.2.2.2.2.1 _ (two_mul_mem j)).1.1.2
  intro n c hc
  by_cases hn : n < (deltaW (2 * j.val)).length
  · rw [List.getD_eq_getElem _ _ hn] at hc
    exact h _ (List.getElem_mem hn) c hc
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hn)] at hc
    simp at hc

theorem bound_codes (j : Fin 2) :
    ∀ w ∈ boundW (2 * j.val), ∀ c ∈ w, c < 6 ∨ (12 ≤ c ∧ c < 16) :=
  (letters_parts.2.2.2.2.2.1 _ (two_mul_mem j)).2

theorem kGen_codes :
    (∀ c ∈ kGenAW, c < 4) ∧ ∀ c ∈ kGenBW, c < 4 :=
  ⟨letters_parts.2.2.2.2.2.2.1, letters_parts.2.2.2.2.2.2.2.1⟩

theorem xW_codes : ∀ c ∈ xW, c < 4 :=
  letters_parts.2.2.2.2.2.2.2.2

theorem rels_parts :
    (∀ w ∈ relsH1 ++ relsH2, eqA 1782 (mcWordA w) (idA 1782) = true) ∧
      (∀ p ∈ relsA, eqA 1782 (mcWordA p.1) (mcWordA p.2) = true) ∧
      (∀ p ∈ edge, commA (mcWordA p.1) p1A = true ∧
        eqA 1782 (mcWordA p.2) (conjA sA (mcWordA p.1)) = true) ∧
      eqA 1782 (mcWordA sq) (compA 1782 sA sA) = true := by
  have h := rels_check
  simp only [mcRelsOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem cells_parts :
    (∀ k ∈ [0, 2], (((eqA 1782 (mcWordA (cW k)) (cA k) = true ∧
      eqA 1782 (mcWordA (cpW k)) (cpA k) = true) ∧ eqA 1782 (mcWordA (eW k)) (eA k) = true) ∧
        (deltaW k).getD 0 [0] = []) ∧ eqA 1782 (mcWordA ((deltaW k).getD 1 [])) wA = true) ∧
      eqA 1782 (mcWordA kGenAW) RootTwistData.kGenAArr = true ∧
      eqA 1782 (mcWordA kGenBW) RootTwistData.kGenBArr = true ∧
      eqA 1782 (conjA sA t1A) p1A = true ∧ eqA 1782 (conjA sA p1A) t1A = true := by
  have h := cells_check
  simp only [mcCellsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem relsH1_val :
    ∀ r ∈ relsH1, evalWord genM r = 1 := fun r hr =>
  eq_of_eqA (rep_word fun c hc => by have := relsH1_codes r hr c hc; omega) rep_idA
    (rels_parts.1 r (List.mem_append_left _ hr))

theorem relsH2_val :
    ∀ r ∈ relsH2, evalWord genM r = 1 := fun r hr =>
  eq_of_eqA (rep_word fun c hc => by have := relsH2_codes r hr c hc; omega) rep_idA
    (rels_parts.1 r (List.mem_append_right _ hr))

theorem relsA_val :
    ∀ p ∈ relsA, evalWord genM p.1 = evalWord genM p.2 := fun p hp =>
  eq_of_eqA (rep_word fun c hc => by have := (relsA_codes p hp).1 c hc; omega)
    (rep_word fun c hc => by have := (relsA_codes p hp).2 c hc; omega) (rels_parts.2.1 p hp)

theorem edge_val :
    ∀ p ∈ edge, Commute (evalWord genM p.1) p1P ∧
      evalWord genM p.2 = sP * evalWord genM p.1 * sP⁻¹ := by
  intro p hp
  have h1 := rep_word fun c hc => by have := (edge_codes p hp).1 c hc; omega
  have h2 := rep_word fun c hc => by have := (edge_codes p hp).2 c hc; omega
  exact ⟨(ModelGroups.commA_iff h1 rep_p1).1 (rels_parts.2.2.1 p hp).1,
    eq_of_eqA h2 (ModelGroups.rep_conjA rep_s h1) (rels_parts.2.2.1 p hp).2⟩

theorem sq_val :
    evalWord genM sq = sP * sP :=
  eq_of_eqA (rep_word fun c hc => by have := sq_codes c hc; omega) (rep_compA rep_s rep_s)
    rels_parts.2.2.2

theorem cW_val
    (j : Fin 2) :
    evalWord genM (cW (2 * j.val)) = cP j :=
  eq_of_eqA (rep_word fun c hc => by have := (cell_codes j).1 c hc; omega) (rep_c j)
    (cells_parts.1 _ (two_mul_mem j)).1.1.1.1

theorem cpW_val
    (j : Fin 2) :
    evalWord genM (cpW (2 * j.val)) = cP' j :=
  eq_of_eqA (rep_word fun c hc => by have := (cell_codes j).2.1 c hc; omega) (rep_c' j)
    (cells_parts.1 _ (two_mul_mem j)).1.1.1.2

theorem eW_val
    (j : Fin 2) :
    evalWord genM (eW (2 * j.val)) = (cP j)⁻¹ * sP * cP' j :=
  eq_of_eqA (rep_word fun c hc => by have := (cell_codes j).2.2 c hc; omega) (rep_e j)
    (cells_parts.1 _ (two_mul_mem j)).1.1.2

theorem delta_zero (j : Fin 2) : (deltaW (2 * j.val)).getD 0 [] = [] := by
  fin_cases j <;> rfl

theorem delta_length (j : Fin 2) : (deltaW (2 * j.val)).length = 16 := by
  fin_cases j <;> rfl

theorem delta_one_val
    (j : Fin 2) :
    evalWord genM ((deltaW (2 * j.val)).getD 1 []) = wP :=
  eq_of_eqA (rep_word fun c hc => by have := delta_codes j 1 c hc; omega) rep_w
    (cells_parts.1 _ (two_mul_mem j)).2

theorem kGenA_val :
    evalWord genM kGenAW = RootTwist.kGenA :=
  eq_of_eqA (rep_word fun c hc => by have := kGen_codes.1 c hc; omega) RootTwist.rep_kGenA
    cells_parts.2.1

theorem kGenB_val :
    evalWord genM kGenBW = RootTwist.kGenB :=
  eq_of_eqA (rep_word fun c hc => by have := kGen_codes.2 c hc; omega) RootTwist.rep_kGenB
    cells_parts.2.2.1

theorem sP_conj_p1 :
    sP * p1P * sP⁻¹ = suzInv 1 :=
  eq_of_eqA (ModelGroups.rep_conjA rep_s rep_p1) ModelGroups.rep_t1 cells_parts.2.2.2.2

theorem bound_check_j (j : Fin 2) :
    mcBoundOK (2 * j.val) = true := by
  fin_cases j
  · exact bound0_check
  · exact bound2_check

theorem bound_parts (j : Fin 2) :
    (boundW (2 * j.val)).getD 0 [] = [4] ∧
      eqA 1782 (mcWordA ((boundW (2 * j.val)).getD 1 [])) t1A = true ∧
      (∀ w ∈ boundW (2 * j.val), ((commA (mcWordA w) p1A = true ∧
        normR0 (conjInvA (cpA (2 * j.val)) (mcWordA w)) = true) ∧
        commA (conjA (eA (2 * j.val)) (conjInvA (cpA (2 * j.val)) (mcWordA w))) t1A = true) ∧
        commA (conjA sA (mcWordA w)) t1A = true) ∧
      ∀ i < 3456, (!((boundW (2 * j.val)).all fun w =>
        commA RootTwistCheck.kEls[i]! (mcWordA w)) || (deltaW (2 * j.val)).any fun d =>
          eqA 1782 RootTwistCheck.kEls[i]! (mcWordA d)) = true := by
  have h := bound_check_j j
  simp only [mcBoundOK, Bool.and_eq_true, decide_eq_true_eq, List.all_map, List.any_map,
    Function.comp_def, allLt_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  rw [List.all_eq_true] at h3
  intro w hw
  have := h3 w hw
  simp only [Bool.and_eq_true] at this
  exact this

theorem bound_zero (j : Fin 2) :
    (boundW (2 * j.val)).getD 0 [] = [4] :=
  (bound_parts j).1

theorem bound_one_val
    (j : Fin 2) :
    evalWord genM ((boundW (2 * j.val)).getD 1 []) = suzInv 1 := by
  have hc : ∀ c ∈ (boundW (2 * j.val)).getD 1 [], c < 16 := by
    intro c hc
    by_cases hn : 1 < (boundW (2 * j.val)).length
    · rw [List.getD_eq_getElem _ _ hn] at hc
      have := bound_codes j _ (List.getElem_mem hn) c hc
      omega
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hn)] at hc
      simp at hc
  exact eq_of_eqA (rep_word hc) ModelGroups.rep_t1 (bound_parts j).2.1

theorem bound_facts
    (j : Fin 2) :
    ∀ w ∈ boundW (2 * j.val), Commute (evalWord genM w) p1P ∧
      (cP' j)⁻¹ * evalWord genM w * cP' j ∈ normalizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ∧
      Commute ((cP j)⁻¹ * sP * cP' j * ((cP' j)⁻¹ * evalWord genM w * cP' j) *
        ((cP j)⁻¹ * sP * cP' j)⁻¹) (suzInv 1) ∧
      Commute (sP * evalWord genM w * sP⁻¹) (suzInv 1) := by
  intro w hw
  have hm := rep_word fun c hc => by have := bound_codes j w hw c hc; omega
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (bound_parts j).2.2.1 w hw
  have hcm := rep_conjInv (rep_c' j) hm
  exact ⟨(ModelGroups.commA_iff hm rep_p1).1 h1, ModelGroups.mem_normalizer_R0_of_normR0 hcm h2,
    (ModelGroups.commA_iff (ModelGroups.rep_conjA (rep_e j) hcm) ModelGroups.rep_t1).1 h3,
    (ModelGroups.commA_iff (ModelGroups.rep_conjA rep_s hm) ModelGroups.rep_t1).1 h4⟩

theorem bound_cut
    (j : Fin 2) :
    ∀ i < 3456, (∀ w ∈ boundW (2 * j.val), Commute (RootTwist.kElt i) (evalWord genM w)) →
      ∃ n < 16, RootTwist.kElt i = evalWord genM ((deltaW (2 * j.val)).getD n []) := by
  intro i hi hcomm
  have hk := RootTwist.rep_kElt hi
  have h := (bound_parts j).2.2.2 i hi
  have hall : ((boundW (2 * j.val)).all fun w =>
      commA RootTwistCheck.kEls[i]! (mcWordA w)) = true := by
    rw [List.all_eq_true]
    intro w hw
    exact (ModelGroups.commA_iff hk
      (rep_word fun c hc => by have := bound_codes j w hw c hc; omega)).2 (hcomm w hw)
  rw [hall, Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨d, hd, hde⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hd
  refine ⟨n, (delta_length j) ▸ hn, ?_⟩
  rw [List.getD_eq_getElem _ _ hn]
  exact eq_of_eqA hk (rep_word fun c hc => by
    have := delta_codes j n c (by rwa [List.getD_eq_getElem _ _ hn]); omega) hde

theorem remark_parts :
    commA (mcWordA xW) w0Arr = true ∧ commA (mcWordA xW) w1A = true ∧
      eqA 1782 (conjA (mcWordA xW) tauA) (compA 1782 tauA t1A) = true ∧
      eqA 1782 (compA 1782 (mcWordA xW) (mcWordA xW)) (idA 1782) = true ∧
      C1Model.v0Enum.tabs.all (fun v => !commA v w1A || commA v (mcWordA xW)) = true ∧
      ∀ t ∈ badPairs, ∀ kn ∈ [(0, t.1), (2, t.2.1)],
        (eqA 1782 (compA 1782 (conjInvA sA (conjA (cA kn.1) (mcWordA xW)))
            (compA 1782 (mcWordA ((deltaW kn.1).getD kn.2 [])) (conjA (cpA kn.1) (mcWordA xW))))
            (if t.2.2 = 0 then idA 1782 else wA) = true ∧
          commA (conjA (cA kn.1) (mcWordA xW)) p1A = true) ∧
          commA (conjInvA sA (conjA (cA kn.1) (mcWordA xW))) t1A = true := by
  have h := remark_check
  simp only [mcRemarkOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem evalWord_genM_mem {H : Subgroup (Equiv.Perm (Fin 1782))} :
    ∀ {w : List ℕ}, (∀ c ∈ w, genM c ∈ H) → evalWord genM w ∈ H
  | [], _ => one_mem _
  | c :: w, hw => by
    rw [evalWord_cons]
    exact mul_mem (hw c (by simp)) (evalWord_genM_mem fun c' hc' => hw c' (by simp [hc']))

theorem rep_xM
    : Rep 1782 (mcWordA xW) xM :=
  rep_word fun c hc => by have := xW_codes c hc; omega

theorem xM_mem
    : xM ∈ invE 1 ⊓ Model.Crho1 := by
  refine evalWord_genM_mem fun c hc => genM_mem ?_
  have : c / 2 = 0 ∨ c / 2 = 1 := by have := xW_codes c hc; omega
  rcases this with h | h <;> rw [h]
  · exact h1_mem
  · exact h2_mem

theorem xM_tau0 :
    xM * C1Model.tau0 * xM⁻¹ = C1Model.tau0 * suzInv 1 :=
  eq_of_eqA (ModelGroups.rep_conjA rep_xM ModelGroups.rep_tau0)
    (rep_compA ModelGroups.rep_tau0 ModelGroups.rep_t1) remark_parts.2.2.1

theorem xM_mul_self
    : xM * xM = 1 :=
  eq_of_eqA (rep_compA rep_xM rep_xM) rep_idA remark_parts.2.2.2.1

theorem xM_V0 :
    ∀ v ∈ C1Model.V0, v * C1Model.r1 = C1Model.r1 * v → v * xM = xM * v := by
  intro v hv hvr
  obtain ⟨k, hk, hrep⟩ := C1Model.enumerates_V0.exists_pos hv
  have hr : Rep 1782 C1Model.v0Enum.tabs[k]! v := hrep.2
  have h := (Array.all_eq_true.1 remark_parts.2.2.2.2.1) k hk
  rw [← getElem!_pos C1Model.v0Enum.tabs k hk, (ModelGroups.commA_iff hr ModelGroups.rep_r1).2 hvr,
    Bool.not_true, Bool.false_or] at h
  exact (ModelGroups.commA_iff hr rep_xM).1 h

theorem badPair_mem (j : Fin 2) {i₀ i₂ u : ℕ} :
    (2 * j.val, if j.val = 0 then i₀ else i₂) ∈ [(0, (i₀, i₂, u).1), (2, (i₀, i₂, u).2.1)] := by
  fin_cases j <;> simp

theorem bad_val
    (j : Fin 2) {i₀ i₂ u : ℕ} (ht : (i₀, i₂, u) ∈ badPairs) :
    sP⁻¹ * (cP j * xM * (cP j)⁻¹) * sP *
        evalWord genM ((deltaW (2 * j.val)).getD (if j.val = 0 then i₀ else i₂) []) *
        (cP' j * xM * (cP' j)⁻¹) = if u = 0 then 1 else wP := by
  have h := (remark_parts.2.2.2.2.2 _ ht _ (badPair_mem j (u := u))).1.1
  have ha := ModelGroups.rep_conjA (rep_c j) rep_xM
  have hb := ModelGroups.rep_conjA (rep_c' j) rep_xM
  have hd := rep_word fun c hc => by
    have := delta_codes j (if j.val = 0 then i₀ else i₂) c hc; omega
  have hl := rep_compA (rep_conjInv rep_s ha) (rep_compA hd hb)
  have hr : Rep 1782 (if u = 0 then idA 1782 else wA) (if u = 0 then 1 else wP) := by
    split
    · exact rep_idA
    · exact rep_w
  rw [← mul_assoc] at hl
  exact eq_of_eqA hl hr h

theorem bad_comm
    (j : Fin 2) :
    Commute (cP j * xM * (cP j)⁻¹) p1P ∧
      Commute (sP⁻¹ * (cP j * xM * (cP j)⁻¹) * sP) (suzInv 1) := by
  have ht : ((15, 7, 0) : ℕ × ℕ × ℕ) ∈ badPairs := List.mem_cons_self
  have h := remark_parts.2.2.2.2.2 _ ht _ (badPair_mem j (u := 0))
  have ha := ModelGroups.rep_conjA (rep_c j) rep_xM
  exact ⟨(ModelGroups.commA_iff ha rep_p1).1 h.1.2,
    (ModelGroups.commA_iff (rep_conjInv rep_s ha) ModelGroups.rep_t1).1 h.2⟩

end CFSG.Sporadic.SuzRecog.MixedCell
