module

public import CFSG.Quasithin.Vol2.KGFactC31J4Set
public import Certificates.Certificate7253

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4
open scoped Matrix

theorem chkF_true : chkF () = true :=
  Certificates.certificate7253.1

@[expose] noncomputable def baseJ (m : ℕ) : G₀ := if m = 0 then a else if m = 1 then b else 1

theorem coe_wordProd (gs : ℕ → G₀) (w : List ℤ) :
    ((wordProd gs w : G₀) : GL (Fin 112) (ZMod 2)) =
      wordProd (fun m => (gs m : GL (Fin 112) (ZMod 2))) w := by
  unfold wordProd
  rw [← Subgroup.coe_subtype, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, Subgroup.coe_subtype]
  split_ifs <;> simp

theorem wordProd_invW {G : Type*} [Group G] (gs : ℕ → G) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0) :
    wordProd gs (invW w) = (wordProd gs w)⁻¹ := by
  unfold wordProd invW
  rw [List.prod_inv_reverse, List.map_map, List.map_map, ← List.map_reverse]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl0 : l ≠ 0 := hw l (List.mem_reverse.mp hl)
  simp only [Function.comp_apply]
  rcases lt_or_gt_of_ne hl0 with h | h
  · rw [ite_eq_left (by omega : 0 < -l), ite_eq_right (by omega : ¬ 0 < l)]
    simp
  · rw [ite_eq_right (by omega : ¬ 0 < -l), ite_eq_left h]
    simp

theorem coe_baseJ (m : ℕ) : ((baseJ m : G₀) : GL (Fin 112) (ZMod 2)) = baseGL m := by
  unfold baseJ baseGL
  split_ifs <;> simp [a_coe, b_coe]

theorem coe_wordProd_baseJ (w : List ℤ) :
    ((wordProd baseJ w : G₀) : GL (Fin 112) (ZMod 2)) = wordProd baseGL w := by
  rw [coe_wordProd]
  congr 1
  funext m
  exact coe_baseJ m

theorem w1_eq : CFSG.Quasithin.KGJ4.w1 = wordProd baseJ w1Word := by
  simp [CFSG.Quasithin.KGJ4.w1, wordProd, w1Word, baseJ, pow_succ, mul_assoc]

theorem w2_eq : CFSG.Quasithin.KGJ4.w2 = wordProd baseJ w2Word := by
  simp [CFSG.Quasithin.KGJ4.w2, wordProd, w2Word, baseJ, pow_succ, mul_assoc]

@[expose] noncomputable def m4gen (m : ℕ) : G₀ :=
  if m = 0 then CFSG.Quasithin.KGJ4.w1 else if m = 1 then CFSG.Quasithin.KGJ4.w2 else 1

theorem m4gen_mem (m : ℕ) : m4gen m ∈ CFSG.Quasithin.KGJ4.M4 := by
  unfold m4gen
  split_ifs
  · exact CFSG.Quasithin.KGJ4.w1_mem_M4
  · exact CFSG.Quasithin.KGJ4.w2_mem_M4
  · exact Subgroup.one_mem _

section Mat

variable (hM : MatFacts)
include hM

theorem Mx_wordProd_baseJ (w : List ℤ) :
    Mx (wordProd baseJ w) = rowsMatrix (wordRows baseMats baseInvs w) := by
  rw [Mx_apply, coe_wordProd_baseJ, rowsMatrix_wordRows (baseMats_spec hM) (baseInvs_spec hM) w]

theorem m4Mats_spec (m : ℕ) : rowsMatrix ((m4Mats ())[m]?.getD idRows) =
    ((m4gen m : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
  · rw [← Mx_apply, show m4gen 0 = CFSG.Quasithin.KGJ4.w1 from rfl, w1_eq, Mx_wordProd_baseJ hM]
    simp only [m4Mats, List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some]
  · rw [← Mx_apply, show m4gen 1 = CFSG.Quasithin.KGJ4.w2 from rfl, w2_eq, Mx_wordProd_baseJ hM]
    simp only [m4Mats, List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some]
  · have h1 : (m4Mats ())[m]? = none := by
      rw [Array.getElem?_eq_none_iff]
      simp only [m4Mats, List.size_toArray, List.length_cons, List.length_nil]
      omega
    have h2 : m4gen m = 1 := by unfold m4gen; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [h1, h2, Option.getD_none, rowsMatrix_idRows]
    rfl

theorem m4Invs_spec (m : ℕ) : rowsMatrix ((m4Invs ())[m]?.getD idRows) =
    (((m4gen m : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
  · have e : ((m4gen 0 : GL (Fin 112) (ZMod 2)))⁻¹ = wordProd baseGL (invW w1Word) := by
      rw [wordProd_invW _ (by decide), show m4gen 0 = CFSG.Quasithin.KGJ4.w1 from rfl, w1_eq,
        coe_wordProd_baseJ]
    rw [e]
    exact rowsMatrix_wordRows (baseMats_spec hM) (baseInvs_spec hM) _
  · have e : ((m4gen 1 : GL (Fin 112) (ZMod 2)))⁻¹ = wordProd baseGL (invW w2Word) := by
      rw [wordProd_invW _ (by decide), show m4gen 1 = CFSG.Quasithin.KGJ4.w2 from rfl, w2_eq,
        coe_wordProd_baseJ]
    rw [e]
    exact rowsMatrix_wordRows (baseMats_spec hM) (baseInvs_spec hM) _
  · have h1 : (m4Invs ())[m]? = none := by
      rw [Array.getElem?_eq_none_iff]
      simp only [m4Invs, List.size_toArray, List.length_cons, List.length_nil]
      omega
    have h2 : m4gen m = 1 := by unfold m4gen; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [h1, h2, Option.getD_none, rowsMatrix_idRows]
    simp

theorem Mx_wordProd_m4gen (w : List ℤ) :
    Mx (wordProd m4gen w) = rowsMatrix (wordRows m4Mats m4Invs w) := by
  rw [Mx_apply, coe_wordProd]
  exact (rowsMatrix_wordRows (gs := fun m => (m4gen m : GL (Fin 112) (ZMod 2)))
    (m4Mats_spec hM) (m4Invs_spec hM) w).symm

end Mat

@[expose] noncomputable def fJn (n : ℕ) : G₀ := wordProd m4gen (fWords.getD n [])

@[expose] noncomputable def fJ (j : Fin 10) : G₀ := fJn j

theorem fJn_mem (n : ℕ) : fJn n ∈ CFSG.Quasithin.KGJ4.M4 := wordProd_mem _ m4gen_mem _

@[expose] def codeVec (c : ℕ) : Fin 10 → ZMod 2 := fun i => if c.testBit i then 1 else 0

theorem eElt_codeVec_eq_eta {G : Type*} [Group G] (u : ℕ → G) :
    ∀ (n c : ℕ), eElt (fun i : Fin n => u i) (fun i => if c.testBit i then 1 else 0) = eta u n c
  | 0, c => by simp [eElt, eta]
  | n + 1, c => by
    rw [eta_succ, ← eElt_codeVec_eq_eta u n c]
    unfold eElt
    rw [List.ofFn_succ', List.prod_concat]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases h : c.testBit n
    · simp [h, show (1 : ZMod 2).val = 1 from rfl]
    · simp [h]

theorem eElt_fJ (c : ℕ) : eElt fJ (codeVec c) = eta fJn 10 c := eElt_codeVec_eq_eta fJn 10 c

theorem exists_codeVec (v : Fin 10 → ZMod 2) : ∃ c < 1024, codeVec c = v := by
  have hinj : Function.Injective (fun c : Fin 1024 => codeVec c) := by
    intro c d h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 10
    · have := congrFun h ⟨i, hi⟩
      simp only [codeVec] at this
      by_cases h1 : (c : ℕ).testBit i <;> by_cases h2 : (d : ℕ).testBit i <;> simp_all
    · have h10 : (2 : ℕ) ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hc : (c : ℕ) < 2 ^ i := lt_of_lt_of_le (show (c : ℕ) < 2 ^ 10 from c.2) h10
      have hd : (d : ℕ) < 2 ^ i := lt_of_lt_of_le (show (d : ℕ) < 2 ^ 10 from d.2) h10
      rw [Nat.testBit_lt_two_pow hc, Nat.testBit_lt_two_pow hd]
  have hbij : Function.Bijective (fun c : Fin 1024 => codeVec c) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  obtain ⟨c, hc⟩ := hbij.2 v
  exact ⟨c, c.2, hc⟩

section Chk

variable (hM : MatFacts) (hc : chkF () = true)
include hM hc

omit hM hc in
theorem fTab_get {n : ℕ} (hn : n < 10) :
    (fTab ())[n]?.getD idRows = wordRows m4Mats m4Invs (fWords.getD n []) := by
  have hlen : fWords.length = 10 := by decide
  unfold fTab
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem (by rw [hlen]; exact hn),
    List.getD_eq_getElem _ _ (by rw [hlen]; exact hn)]
  rfl

omit hc in
theorem Mx_fJn {n : ℕ} (hn : n < 10) : Mx (fJn n) = rowsMatrix ((fTab ())[n]?.getD idRows) := by
  rw [fTab_get hn, fJn, Mx_wordProd_m4gen hM]

omit hc in
theorem Mx_eta_fJ : ∀ n ≤ 10, ∀ c, Mx (eta fJn n c) =
    rowsMatrix ((List.range n).foldl (fun acc j =>
      if c.testBit j then mulRows acc ((fTab ())[j]?.getD idRows) else acc) idRows)
  | 0, _, c => by simp [eta, rowsMatrix_idRows]
  | n + 1, hn, c => by
    rw [eta_succ, map_mul, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs with h
    · rw [Mx_eta_fJ n (by omega) c, Mx_fJn hM (by omega), rowsMatrix_mulRows]
    · rw [map_one, Mx_eta_fJ n (by omega) c, mul_one]

omit hc in
theorem fVec_toVec : ∀ n ≤ 10, ∀ c,
    ((List.range n).foldl (fun acc j =>
      if c.testBit j then frApply (((fTab ()).map frTable)[j]?.getD #[]) acc else acc)
        rootV).toVec = rootV.toVec ᵥ* Mx (eta fJn n c)
  | 0, _, c => by simp [eta]
  | n + 1, hn, c => by
    rw [eta_succ, map_mul, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs with h
    · have hsz : n < (fTab ()).size := by
        have : (fTab ()).size = 10 := by
          unfold fTab
          simp [show fWords.length = 10 by decide]
        omega
      rw [Array.getElem?_map, Array.getElem?_eq_getElem hsz]
      simp only [Option.map_some, Option.getD_some]
      rw [frApply_toVec_eq_vecMul, fVec_toVec n (by omega) c, Matrix.vecMul_vecMul,
        Mx_fJn hM (by omega), Array.getElem?_eq_getElem hsz, Option.getD_some]
    · rw [map_one, Matrix.mul_one, fVec_toVec n (by omega) c]

omit hM in
theorem chkF_parts :
    ((List.range 10).all fun i =>
        eqRows (mulRows ((fTab ())[i]?.getD idRows) ((fTab ())[i]?.getD idRows)) idRows &&
          (List.range 10).all fun j =>
            eqRows (mulRows ((fTab ())[i]?.getD idRows) ((fTab ())[j]?.getD idRows))
              (mulRows ((fTab ())[j]?.getD idRows) ((fTab ())[i]?.getD idRows))) = true ∧
      ((List.range 1024).all fun c =>
        c == 0 || differs (fVec ((fTab ()).map frTable) rootV c) rootV) = true ∧
      ((List.range 2).all fun w => (List.range 10).all fun j =>
        eqRows (mulRows (mulRows ((m4Mats ())[w]?.getD idRows) ((fTab ())[j]?.getD idRows))
            ((m4Invs ())[w]?.getD idRows))
          (fRows (fTab ()) ((cTab.getD w []).getD j 0))) = true := by
  have h := hc
  unfold chkF at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fJ_basis : EBasis fJ := by
  obtain ⟨h1, h2, -⟩ := chkF_parts hc
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h1
  refine ⟨fun i => ?_, fun i j => ?_, fun v hv => ?_⟩
  · apply Mx_injective
    rw [map_mul, map_one, fJ, Mx_fJn hM i.2, ← rowsMatrix_mulRows,
      eqRows_iff.1 (h1 i i.2).1, rowsMatrix_idRows]
  · apply Mx_injective
    rw [map_mul, map_mul, fJ, fJ, Mx_fJn hM i.2, Mx_fJn hM j.2, ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows, eqRows_iff.1 ((h1 i i.2).2 j j.2)]
  · obtain ⟨c, hc1024, rfl⟩ := exists_codeVec v
    rw [eElt_fJ] at hv
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h2
    rcases h2 c hc1024 with h0 | h0
    · subst h0
      funext i
      simp [codeVec]
    · exfalso
      apply differs_toVec h0
      have e := fVec_toVec hM 10 le_rfl c
      rw [hv, map_one, Matrix.vecMul_one] at e
      exact e

noncomputable abbrev F4 : Subgroup G₀ := eSub (fJ_basis hM hc)

theorem conj_fJ {w : ℕ} (hw : w < 2) (j : Fin 10) :
    m4gen w * fJ j * (m4gen w)⁻¹ = eElt fJ (codeVec ((cTab.getD w []).getD j 0)) := by
  obtain ⟨-, -, h3⟩ := chkF_parts hc
  simp only [List.all_eq_true, List.mem_range] at h3
  have h := eqRows_iff.1 (h3 w hw j j.2)
  apply Mx_injective
  have e : Mx (eta fJn 10 ((cTab.getD w []).getD j 0)) =
      rowsMatrix (fRows (fTab ()) ((cTab.getD w []).getD j 0)) :=
    Mx_eta_fJ hM 10 le_rfl _
  rw [eElt_fJ, e, ← h, rowsMatrix_mulRows, rowsMatrix_mulRows, m4Mats_spec hM, m4Invs_spec hM,
    fJ, ← Mx_fJn hM j.2]
  simp [Mx_apply]

theorem M4_le_eNorm : CFSG.Quasithin.KGJ4.M4 ≤ eNorm (fJ_basis hM hc) := by
  have hgen : ∀ w < 2, m4gen w ∈ eNorm (fJ_basis hM hc) := fun w hw =>
    (mem_eNorm_iff (fJ_basis hM hc) _).mpr fun i => ⟨_, conj_fJ hM hc hw i⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact hgen 0 (by norm_num)
  · exact hgen 1 (by norm_num)

end Chk

end CFSG.Quasithin.KGC31.J4M4

end
