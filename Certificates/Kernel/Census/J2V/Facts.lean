module

public import Certificates.Kernel.Census.J2V.Checks
public import Certificates.Kernel.Census.J2V.Prod0
public import Certificates.Kernel.Census.J2V.Prod1
public import Certificates.Kernel.Census.J2V.Prod2
public import Certificates.Kernel.Census.J2V.Prod3
public import Certificates.Kernel.Census.J2V.Idx
public import Certificates.Kernel.Census.J2H.Facts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBJ2Cert
public import CFSG.GH74.Generic.S45.LEvSporSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2V

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2H CFSG.KC.J2V
open CFSG.KC.Misc.ArrEnum CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.Kernel CFSG.ComponentClassification.HarrisLit.EndB
open CertificateChecks.KernelJ2Cover CertificateChecks.KernelJ2H

noncomputable abbrev E (k : ℕ) : Equiv.Perm (Fin 315) := sgnProd gC (posW (vWords.getD k []))

theorem vWords_length : vWords.length = 128 := by decide

theorem vWords_letters : ∀ k < 128, ∀ l ∈ vWords.getD k [], 1 ≤ l ∧ l ≤ 2 := by decide +kernel

theorem vWords_lettersOK : ∀ k < 128, lettersOK 2 (posW (vWords.getD k [])) = true := by
  decide +kernel

theorem vTbls_getElem {k : ℕ} (hk : k < 128) :
    vTbls[k]! = wordTbl 315 c2AGens (vWords.getD k []) := by
  have hl : k < vWords.length := by rw [vWords_length]; exact hk
  rw [vTbls, List.getElem!_toArray, getElem!_pos _ k (by simpa using hl), List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem thRep_vTbls {k : ℕ} (hk : k < 128) : CFSG.Sporadic.Th.Rep 315 vTbls[k]! (E k) := by
  have h1 := rep_wordTbl_c2A _ (vWords_letters k hk) (idT 315) 1
    (CFSG.Sporadic.Th.Rep.idT (by norm_num))
  rw [one_mul] at h1
  rw [vTbls_getElem hk]
  exact h1

theorem tp_vTbls {k : ℕ} (hk : k < 128) : tp 315 vTbls[k]! = E k := tp_eq (thRep_vTbls hk)

theorem allN_at {n : ℕ} {f : ℕ → Bool} (h : allN n f = true) {i : ℕ} (hi : i < n) : f i = true :=
  CFSG.KS.PK.allN_iff.1 h i hi

theorem canon_VP {k : ℕ} (hk : k < 128) : canonK 315 9 (mask 9) (315 * 9) (VP k) = true :=
  allN_at vp_canon hk

theorem rep_VP {k : ℕ} (hk : k < 128) : Rep 315 (unpack 315 9 (VP k)) (E k) :=
  word_c2A (allN_at vp_words hk)

theorem compEqK_of {p q r : ℕ} (hp : canonK 315 9 (mask 9) (315 * 9) p = true)
    (hq : canonK 315 9 (mask 9) (315 * 9) q = true)
    (h : Nat.beq (pcomp 315 9 (mask 9) p q) r = true) :
    compEqK 315 9 (mask 9) (315 * 9) p q r = true := by
  unfold compEqK
  rw [hp, hq]
  exact h

theorem rep_prod {p q r : ℕ} {g h : Equiv.Perm (Fin 315)} (hg : Rep 315 (unpack 315 9 p) g)
    (hh : Rep 315 (unpack 315 9 q) h) (hp : canonK 315 9 (mask 9) (315 * 9) p = true)
    (hq : canonK 315 9 (mask 9) (315 * 9) q = true)
    (he : Nat.beq (pcomp 315 9 (mask 9) p q) r = true) : Rep 315 (unpack 315 9 r) (g * h) := by
  rw [← compEqK_sound (compEqK_of hp hq he)]
  exact rep_compA hg hh

theorem tabT_lt (Tt i j : ℕ) : tabT Tt i j < 128 := by
  unfold tabT
  split
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem tabI_lt (It i : ℕ) : tabI It i < 128 := by
  unfold tabI
  split
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem E_mul {i j : ℕ} (hi : i < 128) (hj : j < 128) : E (tabT vTt i j) = E i * E j := by
  have hrow : prodRows (32 * (i / 32)) 32 = true := by
    have : i / 32 < 4 := by omega
    obtain h | h | h | h : i / 32 = 0 ∨ i / 32 = 1 ∨ i / 32 = 2 ∨ i / 32 = 3 := by omega
    · rw [h]; exact prod0
    · rw [h]; exact prod1
    · rw [h]; exact prod2
    · rw [h]; exact prod3
  have he := allN_at (allN_at hrow (i := i % 32) (by omega)) hj
  have hi' : 32 * (i / 32) + i % 32 = i := by omega
  rw [hi'] at he
  exact ((rep_prod (rep_VP hi) (rep_VP hj) (canon_VP hi) (canon_VP hj) he).unique
    (rep_VP (tabT_lt _ _ _))).symm

theorem E_inv {i : ℕ} (hi : i < 128) : E (tabI vIt i) = (E i)⁻¹ := by
  have h := rep_prod (rep_VP hi) (rep_VP (tabI_lt vIt i)) (canon_VP hi)
    (canon_VP (tabI_lt vIt i)) (allN_at vp_inv hi)
  exact eq_inv_of_mul_eq_one_right (h.unique rep_pidn)

theorem E_inj {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : E i = E j) : i = j := by
  have hd := allN_at (allN_at vp_dist hi) hj
  by_contra hne
  have hb : Nat.beq i j = false := by
    cases h : Nat.beq i j
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hne
  rw [hb, Bool.false_or, Bool.not_eq_true'] at hd
  have hn : neK 315 9 (mask 9) (315 * 9) (VP i) (VP j) = true := by
    unfold neK
    rw [canon_VP hi, canon_VP hj, hd]
  have := neK_sound hn
  rw [(eqA_iff (rep_VP hi) (rep_VP hj)).2 h] at this
  exact Bool.noConfusion this

theorem E_zero : E 0 = 1 := by
  have h := rep_VP (k := 0) (by norm_num)
  rw [Nat.eq_of_beq_eq_true vp_zero] at h
  exact h.unique rep_pidn

theorem E_one : E 1 = permTwoA := by
  have h := rep_VP (k := 1) (by norm_num)
  rw [← arrBind_sound vp_one] at h
  exact (CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep h).symm

theorem E_mem {k : ℕ}
    (hk : k < 128) : E k ∈ centralizerIn P permTwoA :=
  sgnProd_mem (fun i hi => gC_mem hi) _ (vWords_lettersOK k hk)

noncomputable abbrev cR (j : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 crTStrong[j]!

noncomputable abbrev U : Equiv.Perm (Fin 315) := cR 0 * cR 2

theorem rep_crt {j : ℕ} (hj : j < 7) : Rep 315 (unpack 315 9 (CRT.S j)) (cR j) := by
  rw [← crT_binds'.2.2.2.2.1 j hj]
  exact (rep_of_binds crT_binds' crT_perm hj).1

theorem rep_UP : Rep 315 (unpack 315 9 UP) U :=
  rep_prod (rep_crt (by norm_num)) (rep_crt (by norm_num)) crt_canon.1 crt_canon.2
    (Nat.beq_refl _)

theorem tp_u0Tbl :
    CFSG.Sporadic.Th.Rep 315 u0Tbl U := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have h0 := rep_arrTable_chain crT_parts.1 (j := 0) (by decide)
  have h2 := rep_arrTable_chain crT_parts.1 (j := 2) (by decide)
  have hT : u0Tbl = compT 315 (compT 315 (idT 315) (arrTable 315 crTStrong[0]!))
      (arrTable 315 crTStrong[2]!) := by
    simp only [u0Tbl, wordTbl, List.foldl_cons, List.foldl_nil, crTGens, Nat.sub_self,
      show (3 : ℕ) - 1 = 0 + 1 + 1 from rfl, List.getD_cons_zero, List.getD_cons_succ]
  have hw := CFSG.Sporadic.Th.Rep.compT (CFSG.Sporadic.Th.Rep.compT
    (CFSG.Sporadic.Th.Rep.idT hn) h0) h2
  rw [one_mul] at hw
  rw [hT]
  exact hw

theorem U_conj {k : ℕ} (hk : k < 128) : U * E k * U⁻¹ = E (tabI vCut k) := by
  have hc := Nat.eq_of_beq_eq_true (allN_at up_conj hk)
  have h1 := rep_prod rep_UP (rep_VP hk) up_canon (canon_VP hk) (Nat.beq_refl _)
  have h2 := rep_prod (rep_VP (tabI_lt vCut k)) rep_UP (canon_VP (tabI_lt vCut k)) up_canon
    (Nat.beq_refl _)
  rw [hc] at h1
  have := h1.unique h2
  rw [this, mul_inv_cancel_right]

theorem U_sq : U * U = E vUsqt := by
  have hu : vUsqt < 128 := by decide
  exact (rep_prod rep_UP rep_UP up_canon up_canon up_sq).unique (rep_VP hu)

theorem vFind_eq {x : Table} {k₀ : ℕ} (hk₀ : k₀ < 128)
    (hx : CFSG.Sporadic.Th.Rep 315 x (E k₀)) : vFind x = k₀ := by
  have hp : ∀ k < 128, tblEq 315 x vTbls[k]! = true ↔ k = k₀ := fun k hk => by
    rw [tblEq_iff_eq hx (thRep_vTbls hk)]
    exact ⟨fun h => (E_inj hk hk₀ h.symm), fun h => h ▸ rfl⟩
  unfold vFind
  rw [(List.find?_range_eq_some).2 ⟨(hp k₀ hk₀).2 rfl, List.mem_range.2 hk₀, fun j hj => ?_⟩]
  · rfl
  · rw [Bool.not_eq_true']
    cases h : tblEq 315 x vTbls[j]!
    · rfl
    · exact absurd ((hp j (by omega)).1 h) (by omega)

theorem ofFn_getElem! {α : Type*} [Inhabited α] (f : Fin 128 → α) {i : ℕ} (hi : i < 128) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ofFn_getElem!_neg {α : Type*} [Inhabited α] (f : Fin 128 → α) {i : ℕ} (hi : ¬ i < 128) :
    (Array.ofFn f)[i]! = default :=
  getElem!_neg _ i (by simpa using hi)

theorem vT_eq : vT = tabT vTt := by
  funext i j
  unfold vT vMulTab
  by_cases hi : i < 128
  · rw [ofFn_getElem! _ hi]
    by_cases hj : j < 128
    · rw [ofFn_getElem! _ hj]
      have hr := CFSG.Sporadic.Th.Rep.compT (thRep_vTbls hi) (thRep_vTbls hj)
      rw [← E_mul hi hj] at hr
      exact vFind_eq (tabT_lt _ _ _) hr
    · rw [ofFn_getElem!_neg _ hj, tabT, if_neg (by omega)]
      rfl
  · rw [ofFn_getElem!_neg _ hi, tabT, if_neg (by omega)]
    rfl

theorem vI_eq : vI = tabI vIt := by
  funext i
  unfold vI vInvTab
  by_cases hi : i < 128
  · rw [ofFn_getElem! _ hi]
    have hr := CFSG.GH74.Generic.S45.EvSpor.rep_invT_of_rep (by norm_num) (thRep_vTbls hi)
    rw [← E_inv hi] at hr
    exact vFind_eq (tabI_lt _ _) hr
  · rw [ofFn_getElem!_neg _ hi, tabI, if_neg hi]
    rfl

theorem vCu_eq :
    vCu = tabI vCut := by
  funext k
  unfold vCu vCuTab
  by_cases hk : k < 128
  · rw [ofFn_getElem! _ hk]
    have hr := CFSG.Sporadic.Th.Rep.compT (CFSG.Sporadic.Th.Rep.compT tp_u0Tbl (thRep_vTbls hk))
      (CFSG.GH74.Generic.S45.EvSpor.rep_invT_of_rep (by norm_num) tp_u0Tbl)
    rw [U_conj hk] at hr
    exact vFind_eq (tabI_lt _ _) hr
  · rw [ofFn_getElem!_neg _ hk, tabI, if_neg hk]
    rfl

theorem vUsq_eq :
    vUsq = vUsqt := by
  have hr := CFSG.Sporadic.Th.Rep.compT tp_u0Tbl tp_u0Tbl
  rw [U_sq] at hr
  exact vFind_eq (by decide) hr

theorem all_perm {l l' : List ℕ} (h : l.Perm l') (p : ℕ → Bool) : l.all p = l'.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall_congr' fun x => imp_congr_left h.mem_iff

theorem contains_perm {l l' : List ℕ} (h : l.Perm l') (a : ℕ) : l.contains a = l'.contains a := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact h.mem_iff

theorem subIndexCheckWith_perm {T : ℕ → ℕ → ℕ} {I Cu : ℕ → ℕ} {usq : ℕ} {C C' : List ℕ}
    (h : C.Perm C') : subIndexCheckWith T I Cu usq C = subIndexCheckWith T I Cu usq C' := by
  simp only [subIndexCheckWith, all_perm h, contains_perm h]

theorem commOf_perm : (commOf (tabT vTt) (tabI vIt)).Perm vCommL := by
  have hc := comm_ok
  simp only [commCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    List.contains_iff_mem, beq_iff_eq] at hc
  obtain ⟨h1, h2⟩ := hc
  unfold commOf
  rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) (by decide)]
  intro a
  rw [List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨⟨i, j⟩, hp, rfl⟩
    rw [List.mem_product, List.mem_range, List.mem_range] at hp
    exact h1 i hp.1 j hp.2
  · intro ha
    obtain ⟨i, hi, j, hj, he⟩ := h2 a ha
    exact ⟨(i, j), List.mem_product.2 ⟨List.mem_range.2 hi, List.mem_range.2 hj⟩, he⟩

theorem subIndexCheck_true :
    subIndexCheck = true := by
  rw [subIndexCheck_eq, vT_eq, vI_eq, vCu_eq, vUsq_eq, subIndexCheckWith_perm commOf_perm]
  exact idx_ok

open Certificates in
open CFSG.ComponentClassification.HarrisLit.EndB CFSG.ComponentClassification.J2Cover in
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem facts22401 : ((∀ i < 128, ∀ j < 128, vT i j < 128 ∧
        tp 315 vTbls[vT i j]! = tp 315 vTbls[i]! * tp 315 vTbls[j]!) ∧
      (∀ i < 128, vI i < 128 ∧ tp 315 vTbls[vI i]! = (tp 315 vTbls[i]!)⁻¹) ∧
      tp 315 vTbls[0]! = 1 ∧ tp 315 vTbls[1]! = permTwoA ∧
      (∀ i < 128, ∀ j < 128, tp 315 vTbls[i]! = tp 315 vTbls[j]! → i = j) ∧
      (∀ k < 128, tp 315 vTbls[k]! ∈ centralizerIn P permTwoA) ∧
      (∀ k < 128, vCu k < 128 ∧
        tp 315 u0Tbl * tp 315 vTbls[k]! * (tp 315 u0Tbl)⁻¹ = tp 315 vTbls[vCu k]!) ∧
      vUsq < 128 ∧ tp 315 u0Tbl * tp 315 u0Tbl = tp 315 vTbls[vUsq]!) ∧
    subIndexCheck = true := by
  refine ⟨⟨fun i hi j hj => ?_, fun i hi => ?_, ?_, ?_, fun i hi j hj h => ?_, fun k hk => ?_,
    fun k hk => ?_, ?_, ?_⟩, subIndexCheck_true⟩
  · rw [vT_eq, tp_vTbls hi, tp_vTbls hj, tp_vTbls (tabT_lt _ _ _)]
    exact ⟨tabT_lt _ _ _, E_mul hi hj⟩
  · rw [vI_eq, tp_vTbls hi, tp_vTbls (tabI_lt _ _)]
    exact ⟨tabI_lt _ _, E_inv hi⟩
  · rw [tp_vTbls (by norm_num)]
    exact E_zero
  · rw [tp_vTbls (by norm_num)]
    exact E_one
  · rw [tp_vTbls hi, tp_vTbls hj] at h
    exact E_inj hi hj h
  · rw [tp_vTbls hk]
    exact E_mem hk
  · rw [vCu_eq, tp_vTbls hk, tp_vTbls (tabI_lt _ _), tp_eq tp_u0Tbl]
    exact ⟨tabI_lt _ _, U_conj hk⟩
  · rw [vUsq_eq]
    decide
  · rw [vUsq_eq, tp_vTbls (by decide), tp_eq tp_u0Tbl]
    exact U_sq

end CertificateChecks.KernelJ2V
