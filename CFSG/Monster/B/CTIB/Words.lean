module

public import CFSG.Monster.B.CTIB.CosetBase
public import CFSG.Monster.B.CTIB.WordsInputs
public import Certificates.Certificate3110
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Word

variable {α : Type*} (L : α → Sbp) (T : α → Array ℕ) (P : α → Prop)
  (hL : ∀ a, P a → (L a).unop ∈ Jbar)
  (hT : ∀ a, P a → ∀ i < 22, (L a)⁻¹ * es i * L a = qS ((T a).getD i 0))

include hL hT in
theorem conj_word :
    ∀ (w : List α) (Pm : Sbp) (A : Array ℕ), Pm.unop ∈ Jbar →
    A.size = 22 →
    (∀ i < 22, Pm⁻¹ * es i * Pm = qS (A.getD i 0)) → (∀ a ∈ w, P a) →
    (∀ i < 22, (Pm * (w.map L).prod)⁻¹ * es i * (Pm * (w.map L).prod) =
      qS ((w.foldl (fun A a => autComp gArr A (T a)) A).getD i 0)) ∧
    (w.foldl (fun A a => autComp gArr A (T a)) A).size = 22 ∧
    (Pm * (w.map L).prod).unop ∈ Jbar
  | [], Pm, A, hP, hA, hPA, _ => by
    simp only [List.map_nil, List.prod_nil, mul_one, List.foldl_nil]
    exact ⟨hPA, hA, hP⟩
  | a :: w, Pm, A, hP, hA, hPA, hw => by
    have ha := hw a (List.mem_cons_self ..)
    have hP' : (Pm * L a).unop ∈ Jbar := by
      rw [unop_mul]; exact Jbar.mul_mem (hL a ha) hP
    have hA' : (autComp gArr A (T a)).size = 22 := by rw [autComp_size, hA]
    have hPA' : ∀ i < 22, (Pm * L a)⁻¹ * es i * (Pm * L a) =
        qS ((autComp gArr A (T a)).getD i 0) := by
      intro i hi
      rw [autComp_getD (by rw [hA]; exact hi), ← conj_qS (hL a ha) (hT a ha), ← hPA i hi]
      group
    have ih := conj_word w (Pm * L a) _ hP' hA' hPA' fun b h => hw b (List.mem_cons_of_mem _ h)
    have e : Pm * ((a :: w).map L).prod = Pm * L a * (w.map L).prod := by
      rw [List.map_cons, List.prod_cons, mul_assoc]
    rw [e, List.foldl_cons]
    exact ih

end Word

theorem conj_pow
    {g : Sbp} (hg : g.unop ∈ Jbar) {A : Array ℕ} (hA : A.size = 22)
    (hgA : ∀ i < 22, g⁻¹ * es i * g = qS (A.getD i 0)) :
    ∀ m, (∀ i < 22, (g ^ m)⁻¹ * es i * g ^ m = qS ((autPow gArr A m).getD i 0)) ∧
      (autPow gArr A m).size = 22
  | 0 => ⟨fun i hi => by
      rw [pow_zero, inv_one, one_mul, mul_one, autPow, id23_getD hi, qS_two_pow hi],
    by simp [autPow, id23]⟩
  | m + 1 => by
    obtain ⟨ih, hs⟩ := conj_pow hg hA hgA m
    refine ⟨fun i hi => ?_, by rw [autPow, autComp_size, hs]⟩
    rw [autPow, autComp_getD (by rw [hs]; exact hi), ← conj_qS hg hgA, ← ih i hi, pow_succ]
    group

theorem gs1_pow_48 :
    gs 1 ^ 48 = 1 := by
  rw [show gs 1 = etaS gSeq iotaS dB from rfl, ← map_pow, ← orderOf_dB, pow_orderOf_eq_one,
    map_one]

theorem gs1_inv :
    (gs 1)⁻¹ = gs 1 ^ 47 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', gs1_pow_48]

theorem gs0_inv :
    (gs 0)⁻¹ = gs 0 := etaS_cB_inv gSeq iotaS

abbrev IsLetter2 (l : ℤ) : Prop := l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2

theorem letterS_eq
    {l : ℤ} (hl : IsLetter2 l) :
    letterS l = if l = 1 ∨ l = -1 then gs 0 else if l = 2 then gs 1 else (gs 1)⁻¹ := by
  rcases hl with rfl | rfl | rfl | rfl
  · rw [letterS, ite_eq_left (by decide), ite_eq_left (by decide),
      show (1 : ℤ).toNat - 1 = 0 by decide]
  · rw [letterS, ite_eq_right (by decide), ite_eq_left (by decide),
      show (- -1 : ℤ).toNat - 1 = 0 by decide, gs0_inv]
  · rw [letterS, ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_left (by decide),
      show (2 : ℤ).toNat - 1 = 1 by decide]
  · rw [letterS, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      show (- -2 : ℤ).toNat - 1 = 1 by decide]

theorem letterS_mem_Jbar
    {l : ℤ} (hl : IsLetter2 l) : (letterS l).unop ∈ Jbar := by
  rw [letterS_eq hl]
  split_ifs
  · exact gs0_mem_Jbar
  · exact gs1_mem_Jbar
  · rw [unop_inv]; exact Jbar.inv_mem gs1_mem_Jbar

theorem genInvImgs_spec :
    (∀ i < 22, ((gs 1)⁻¹)⁻¹ * es i * (gs 1)⁻¹ = qS ((genInvImgs ()).getD i 0)) ∧
      (genInvImgs ()).size = 22 := by
  have h := conj_pow gs1_mem_Jbar (genImgs_size 1) (fun i hi => conj_gs (by norm_num) hi) 47
  rw [gs1_inv]
  exact h

theorem conj_letterS
    {l : ℤ} (hl : IsLetter2 l) {i : ℕ}
    (hi : i < 22) :
    (letterS l)⁻¹ * es i * letterS l = qS ((letterImgs (genInvImgs ()) l).getD i 0) := by
  rw [letterS_eq hl, letterImgs]
  split_ifs
  · exact conj_gs (by norm_num) hi
  · exact conj_gs (by norm_num) hi
  · exact genInvImgs_spec.1 i hi

theorem conj_wordS'
    {w : List ℤ}
    (hw : ∀ l ∈ w, IsLetter2 l) :
    (∀ i < 22, (wordS' w)⁻¹ * es i * wordS' w = qS ((wordAut (genInvImgs ()) w).getD i 0)) ∧
      (wordAut (genInvImgs ()) w).size = 22 ∧ (wordS' w).unop ∈ Jbar := by
  have h := conj_word letterS (letterImgs (genInvImgs ())) IsLetter2
    (fun _ hl => letterS_mem_Jbar hl)
    (fun _ hl _ hi => conj_letterS hl hi) w 1 id23 (by simp) (by simp [id23])
    (fun j hj => by rw [inv_one, one_mul, mul_one, id23_getD hj, qS_two_pow hj]) hw
  simp only [one_mul] at h
  exact h

theorem wordS'_nil :
    wordS' [] = 1 := rfl

theorem wordS'_append
    (a b : List ℤ) : wordS' (a ++ b) = wordS' a * wordS' b := by
  rw [wordS', List.map_append, List.prod_append]; rfl

theorem letterS_neg
    {l : ℤ} (hl : IsLetter2 l) : letterS (-l) = (letterS l)⁻¹ := by
  rcases hl with rfl | rfl | rfl | rfl
  · rw [letterS_eq (Or.inr (Or.inl rfl)), letterS_eq (Or.inl rfl), ite_eq_left (by decide),
      ite_eq_left (by decide), gs0_inv]
  · rw [show -(-1 : ℤ) = 1 from rfl, letterS_eq (Or.inl rfl), letterS_eq (Or.inr (Or.inl rfl)),
      ite_eq_left (by decide), ite_eq_left (by decide), gs0_inv]
  · rw [letterS_eq (Or.inr (Or.inr (Or.inr rfl))), letterS_eq (Or.inr (Or.inr (Or.inl rfl))),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left (by decide)]
  · rw [show -(-2 : ℤ) = 2 from rfl, letterS_eq (Or.inr (Or.inr (Or.inl rfl))),
      letterS_eq (Or.inr (Or.inr (Or.inr rfl))), ite_eq_right (by decide),
      ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide), inv_inv]

theorem wordS'_invWord :
    ∀
    {w : List ℤ}, (∀ l ∈ w, IsLetter2 l) →
    wordS' (invWord w) = (wordS' w)⁻¹
  | [], _ => by rw [invWord, List.map_nil, List.reverse_nil, wordS'_nil, inv_one]
  | l :: w, hw => by
    have hl := hw l (List.mem_cons_self ..)
    rw [invWord, List.map_cons, List.reverse_cons, ← invWord, wordS'_append,
      wordS'_invWord fun l' h => hw l' (List.mem_cons_of_mem _ h)]
    rw [show wordS' [-l] = letterS (-l) by rw [wordS']; simp, letterS_neg hl,
      show wordS' (l :: w) = letterS l * wordS' w by rw [wordS']; simp [wordS'],
      _root_.mul_inv_rev]

theorem invWord_letters {w : List ℤ} (hw : ∀ l ∈ w, IsLetter2 l) :
    ∀ l ∈ invWord w, IsLetter2 l := by
  intro l hl
  rw [invWord, List.mem_reverse, List.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  rcases hw a ha with rfl | rfl | rfl | rfl <;> decide

@[expose] def liftWordZ (k : ℕ) : List ℤ :=
  (if k = 6 then liftWord6 else if k = 8 then liftWord8 else liftWord10).map
    fun l : ℕ => (l : ℤ) + 1

theorem liftWordZ_letters {k : ℕ} (hk : IsRank k) : ∀ l ∈ liftWordZ k, IsLetter2 l := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem wordS'_liftWordZ
    {k : ℕ} (hk : IsRank k) : wordS' (liftWordZ k) = hs k := by
  rw [hs_eq_liftWordS hk, liftWordS, wordS', liftWordZ, List.map_map]
  have hk' : (if k = 6 then liftWord6 else if k = 8 then liftWord8 else liftWord10) =
      liftWordK k := rfl
  rw [hk']
  refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
  have h := liftWordK_lt hk l hl
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · simp only [Function.comp_apply, Nat.cast_zero, zero_add]
    rw [letterS, ite_eq_left (by decide), show (1 : ℤ).toNat - 1 = 0 by decide]
  · simp only [Function.comp_apply, Nat.cast_one]
    rw [letterS, ite_eq_left (by decide), show ((1 : ℤ) + 1).toNat - 1 = 1 by decide]

theorem mul_self_mem {y : Sbp} (hy : y ∈ Qs) : y * y = 1 ∨ y * y = xs := by
  have h := eq_of_psiS_eq (Qs.mul_mem hy hy) Qs.one_mem (by
    rw [psiS_mul hy hy, psiS_one]
    exact ZModModule.add_self (psiS y))
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h, mul_one])

theorem pow_four_of_mem {y : Sbp} (hy : y ∈ Qs) : y * y * y * y = 1 := by
  rcases mul_self_mem hy with h | h
  · rw [h, one_mul, h]
  · rw [mul_assoc (y * y), h, xs_mul_self]

theorem qS_sqCode_sq (k : ℕ) : qS (sqCode k) * qS (sqCode k) = 1 := by
  rw [sqCode]
  split_ifs
  · rw [qS_zero, one_mul]
  · rw [qS_two_pow_22, xs_mul_self]

theorem hs_mul_hs_mul_hs_mul_hs
    {k : ℕ} (hk : IsRank k) : hs k *
    hs k * hs k * hs k = 1 := by
  calc hs k * hs k * hs k * hs k = (hs k * hs k) * (hs k * hs k) := by group
    _ = 1 := by rw [hs_sq_code hk, qS_sqCode_sq]

theorem hs_inv
    {k : ℕ} (hk : IsRank k) : (hs k)⁻¹
    = hs k * hs k * hs k := by
  rw [inv_eq_iff_mul_eq_one]
  calc hs k * (hs k * hs k * hs k) = hs k * hs k * hs k * hs k := by group
    _ = 1 := hs_mul_hs_mul_hs_mul_hs hk

@[expose] noncomputable def centElt
    (k j : ℕ) : Sbp := wordS' (centWordN k j)

@[expose] noncomputable def deltaElt
    (k j : ℕ) : Sbp :=
  (hs k)⁻¹ * (centElt k j)⁻¹ * hs k * centElt k j

theorem centLettersOK_eq_true : centLettersOK = true :=
  Certificates.certificate3110.2

theorem centWordN_eq_L (k j : ℕ) :
    centWordN k j = centWordsL.getD (rankOff k + j) [] := by
  rw [centWordN, Certificates.certificate3110.1]

theorem centWordN_letters {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    ∀ l ∈ centWordN k j, IsLetter2 l := by
  rw [centWordN_eq_L]
  have h := centLettersOK_eq_true
  rw [centLettersOK, List.all_eq_true] at h
  have hoff : rankOff k + j < 45 := by
    rcases hk with rfl | rfl | rfl <;> simp [rankOff] <;> omega
  have ht := h (rankOff k + j) (List.mem_range.2 hoff)
  rw [List.all_eq_true] at ht
  intro l hl
  have := ht l hl
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem centElt_mem_Jbar
    {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    (centElt k j).unop ∈ Jbar :=
  (conj_wordS' (centWordN_letters hk hj)).2.2

theorem qS_qinv
    (d : ℕ) : qS (qinv d) = (qS d)⁻¹ := by
  rw [qinv, ← qS_mul, ← qS_mul, eq_inv_iff_mul_eq_one]
  exact pow_four_of_mem (qS_mem d)

abbrev GoodPair (p : Sbp × Array ℕ) : Prop :=
  p.1.unop ∈ Jbar ∧ ∀ i < 22, p.1⁻¹ * es i * p.1 = qS (p.2.getD i 0)

theorem conj_delta_eq
    {k j : ℕ} (hk : IsRank k) (hj : j < 15)
    (hok : deltaAutOK (genInvImgs ()) (liftImgsK k).toArray (wordAut (genInvImgs ())
      (centWordN k j)) (centWordN k j) (deltaN k j) = true) {i : ℕ} (hi : i < 22) :
    (deltaElt k j)⁻¹ * es i * deltaElt k j = (qS (deltaN k j))⁻¹ * es i * qS (deltaN k j) := by
  have hg := centWordN_letters hk hj
  obtain ⟨hgc, hgs, hgJ⟩ := conj_wordS' hg
  obtain ⟨hic, his, hiJ⟩ := conj_wordS' (invWord_letters hg)
  rw [wordS'_invWord hg] at hic hiJ
  have hH : ∀ i < 22, (hs k)⁻¹ * es i * hs k = qS (((liftImgsK k).toArray).getD i 0) :=
    fun i hi => by rw [liftImgsK_getD]; exact conj_hs hk hi
  have hHs : ((liftImgsK k).toArray).size = 22 := by
    rw [List.size_toArray, ← List.length_map (· % 2 ^ 22), lift_rows hk, lift_len hk]
  obtain ⟨h3, h3s⟩ := conj_pow (hs_mem_Jbar hk) hHs hH 3
  have hw := conj_word Prod.fst Prod.snd GoodPair (fun _ hp => hp.1) (fun _ hp => hp.2)
    [((wordS' (centWordN k j))⁻¹, wordAut (genInvImgs ()) (invWord (centWordN k j))),
      (hs k, (liftImgsK k).toArray),
      (wordS' (centWordN k j), wordAut (genInvImgs ()) (centWordN k j))] (hs k ^ 3)
    (autPow gArr (liftImgsK k).toArray 3)
    (by rw [unop_pow]; exact Jbar.pow_mem (hs_mem_Jbar hk) 3) h3s h3 (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨hiJ, hic⟩
      · exact ⟨hs_mem_Jbar hk, hH⟩
      · exact ⟨hgJ, hgc⟩)
  have hprod : hs k ^ 3 * ([((wordS' (centWordN k j))⁻¹,
      wordAut (genInvImgs ()) (invWord (centWordN k j))), (hs k, (liftImgsK k).toArray),
      (wordS' (centWordN k j), wordAut (genInvImgs ()) (centWordN k j))].map Prod.fst).prod =
      deltaElt k j := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [deltaElt, centElt, hs_inv hk, pow_three]
    group
  rw [hprod] at hw
  rw [hw.1 i hi]
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [deltaAutOK, innerOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  have hsz := hok.1
  have hci := hok.2 i hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hi),
    Option.getD_some, ← getElem!_pos _ i (by rw [hsz]; exact hi), hci, ← qS_mul, ← qS_mul,
    qS_two_pow hi, qS_qinv]

theorem closure_es :
    Subgroup.closure (es '' {m | m < 22}) = Qs := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨m, -, rfl⟩
    exact es_mem m
  · intro y hy
    obtain ⟨n, -, rfl⟩ := exists_qS hy
    have hes : ∀ m < 22, es m ∈ Subgroup.closure (es '' {m | m < 22}) :=
      fun m hm => Subgroup.subset_closure ⟨m, hm, rfl⟩
    have hx : xs ∈ Subgroup.closure (es '' {m | m < 22}) := by
      have h : es 4 * es 0 = es 0 * es 4 * xpow xs ((gArr.getD 0 0).testBit 4) :=
        es_comm ⟨4, by norm_num⟩ ⟨0, by norm_num⟩
      have hb : (gArr.getD 0 0).testBit 4 = true := by decide
      rw [hb, xpow_true] at h
      have : xs = (es 0 * es 4)⁻¹ * (es 4 * es 0) := by rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hes 0 (by norm_num))
        (hes 4 (by norm_num)))) (Subgroup.mul_mem _ (hes 4 (by norm_num)) (hes 0 (by norm_num)))
    have hP : ∀ v m, m ≤ 22 → ordProd es v m ∈ Subgroup.closure (es '' {m | m < 22}) := by
      intro v m hm
      induction m with
      | zero => exact Subgroup.one_mem _
      | succ m ih =>
        rw [ordProd_succ]
        refine Subgroup.mul_mem _ (ih (by omega)) ?_
        split_ifs
        · exact hes m (by omega)
        · exact Subgroup.one_mem _
    refine Subgroup.mul_mem _ ?_ (hP n 22 le_rfl)
    cases n.testBit 22
    · exact Subgroup.one_mem _
    · exact hx

theorem deltaElt_mem_Jbar
    {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    (deltaElt k j).unop ∈ Jbar := by
  have hg := centElt_mem_Jbar hk hj
  have hh := hs_mem_Jbar hk
  rw [deltaElt, unop_mul, unop_mul, unop_mul, unop_inv, unop_inv]
  exact Jbar.mul_mem hg (Jbar.mul_mem hh (Jbar.mul_mem (Jbar.inv_mem hg) (Jbar.inv_mem hh)))

theorem delta_cases
    {k j : ℕ} (hk : IsRank k) (hj : j < 15)
    (hok : deltaAutOK (genInvImgs ()) (liftImgsK k).toArray (wordAut (genInvImgs ())
      (centWordN k j)) (centWordN k j) (deltaN k j) = true) :
    deltaElt k j = qS (deltaN k j) ∨ deltaElt k j = xs * qS (deltaN k j) := by
  set d := deltaN k j
  obtain ⟨c, hcdef⟩ : ∃ c, c = deltaElt k j * (qS d)⁻¹ := ⟨_, rfl⟩
  have hc : ∀ i < 22, es i * c = c * es i := by
    intro i hi
    have h := conj_delta_eq hk hj hok hi
    have h' : c⁻¹ * es i * c = es i := by
      rw [hcdef, _root_.mul_inv_rev, inv_inv]
      calc qS d * (deltaElt k j)⁻¹ * es i * (deltaElt k j * (qS d)⁻¹)
          = qS d * ((deltaElt k j)⁻¹ * es i * deltaElt k j) * (qS d)⁻¹ := by group
        _ = qS d * ((qS d)⁻¹ * es i * qS d) * (qS d)⁻¹ := by rw [h]
        _ = es i := by group
    calc es i * c = c * (c⁻¹ * es i * c) := by group
      _ = c * es i := by rw [h']
  have hcJ : c.unop ∈ Jbar := by
    rw [hcdef, unop_mul, unop_inv]
    exact Jbar.mul_mem (Jbar.inv_mem (Ebar_le_Jbar (qS_mem d))) (deltaElt_mem_Jbar hk hj)
  have hle : Subgroup.closure (es '' {m | m < 22}) ≤ Subgroup.centralizer {c} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hc m hm)
  have hz : c.unop ∈ Subgroup.zpowers xbar := by
    rw [← centralizer_Ebar]
    refine ⟨hcJ, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : op y ∈ Subgroup.centralizer {c} := hle (by rw [closure_es]; exact hy)
    have e := congrArg unop (Subgroup.mem_centralizer_singleton_iff.1 hy')
    rw [unop_mul, unop_mul, unop_op] at e
    exact e.symm
  rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar).1 hz with h1 | h1
  · left
    have : c = 1 := unop_injective h1
    rw [hcdef, mul_inv_eq_one] at this
    exact this
  · right
    have : c = xs := unop_injective h1
    rw [hcdef, mul_inv_eq_iff_eq_mul] at this
    exact this

theorem delta_word
    {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    wordS' (liftWordZ k ++ liftWordZ k ++ liftWordZ k ++ invWord (centWordN k j) ++ liftWordZ k ++
      centWordN k j) = deltaElt k j := by
  rw [wordS'_append, wordS'_append, wordS'_append, wordS'_append, wordS'_append,
    wordS'_liftWordZ hk, wordS'_invWord (centWordN_letters hk hj), deltaElt, centElt, hs_inv hk]

theorem delta_letters {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    ∀ l ∈ liftWordZ k ++ liftWordZ k ++ liftWordZ k ++ invWord (centWordN k j) ++ liftWordZ k ++
      centWordN k j, IsLetter2 l := by
  intro l hl
  simp only [List.mem_append] at hl
  rcases hl with ((((h | h) | h) | h) | h) | h
  · exact liftWordZ_letters hk l h
  · exact liftWordZ_letters hk l h
  · exact liftWordZ_letters hk l h
  · exact invWord_letters (centWordN_letters hk hj) l h
  · exact liftWordZ_letters hk l h
  · exact centWordN_letters hk hj l h

theorem rankOfT_eq {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    Dyadic.rankOfT (rankOff k + j) = k := by
  rcases hk with rfl | rfl | rfl <;> simp only [Dyadic.rankOfT, rankOff] <;> split_ifs <;> omega

theorem liftWordZK_eq {k : ℕ} (hk : IsRank k) : Dyadic.liftWordZK k = liftWordZ k := by
  rcases hk with rfl | rfl | rfl <;> rfl

theorem deltaWord_eq {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    Dyadic.deltaWord (rankOff k + j) = Dyadic.freeRed (invWord (liftWordZ k) ++
      invWord (centWordN k j) ++ liftWordZ k ++ centWordN k j) := by
  rw [Dyadic.deltaWord, rankOfT_eq hk hj, liftWordZK_eq hk, centWordN_eq_L k j]
  rfl

theorem commWord_letters {k j : ℕ} (hk : IsRank k) (hj : j < 15) :
    ∀ l ∈ invWord (liftWordZ k) ++ invWord (centWordN k j) ++ liftWordZ k ++ centWordN k j,
      IsLetter2 l := by
  intro l hl
  simp only [List.mem_append] at hl
  rcases hl with ((h | h) | h) | h
  · exact invWord_letters (liftWordZ_letters hk) l h
  · exact invWord_letters (centWordN_letters hk hj) l h
  · exact liftWordZ_letters hk l h
  · exact centWordN_letters hk hj l h

section Kernel


theorem wordS'_single (l : ℤ) : wordS' [l] = letterS l := by
  rw [wordS', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem wordS'_cons (l : ℤ) (w : List ℤ) : wordS' (l :: w) = letterS l * wordS' w := by
  rw [wordS', List.map_cons, List.prod_cons]
  rfl

theorem gs0_mul_self : gs 0 * gs 0 = 1 := mul_eq_one_iff_eq_inv.2 gs0_inv.symm

theorem letterS_cancel {x y : ℤ} (hx : IsLetter2 x) (hy : IsLetter2 y)
    (h : y = -x ∨ (x.natAbs = 1 ∧ y.natAbs = 1)) : letterS y * letterS x = 1 := by
  rcases h with rfl | ⟨h1, h2⟩
  · rw [letterS_neg hx, inv_mul_cancel]
  · have hx1 : x = 1 ∨ x = -1 := by rcases hx with rfl | rfl | rfl | rfl <;> simp_all
    have hy1 : y = 1 ∨ y = -1 := by rcases hy with rfl | rfl | rfl | rfl <;> simp_all
    rw [letterS_eq hx, letterS_eq hy, ite_eq_left hx1, ite_eq_left hy1, gs0_mul_self]

theorem wordS'_redStep : ∀ (acc : List ℤ) {x : ℤ}, IsLetter2 x → (∀ l ∈ acc, IsLetter2 l) →
    wordS' (Dyadic.redStep acc x).reverse = wordS' acc.reverse * letterS x ∧
      ∀ l ∈ Dyadic.redStep acc x, IsLetter2 l
  | [], x, hx, _ => by
    refine ⟨?_, fun l hl => ?_⟩
    · rw [Dyadic.redStep, List.reverse_singleton, wordS'_single, List.reverse_nil, wordS'_nil,
        one_mul]
    · rw [Dyadic.redStep, List.mem_singleton] at hl
      rw [hl]
      exact hx
  | y :: r, x, hx, hacc => by
    have hy := hacc y List.mem_cons_self
    rw [Dyadic.redStep]
    split_ifs with h
    · refine ⟨?_, fun l hl => hacc l (List.mem_cons_of_mem _ hl)⟩
      rw [List.reverse_cons, wordS'_append, wordS'_single, mul_assoc, letterS_cancel hx hy h,
        mul_one]
    · refine ⟨?_, fun l hl => ?_⟩
      · rw [List.reverse_cons, wordS'_append, wordS'_single]
      · rcases List.mem_cons.1 hl with rfl | hl
        · exact hx
        · exact hacc l hl

theorem wordS'_foldl_redStep : ∀ (w acc : List ℤ), (∀ l ∈ w, IsLetter2 l) →
    (∀ l ∈ acc, IsLetter2 l) →
    wordS' (w.foldl Dyadic.redStep acc).reverse = wordS' acc.reverse * wordS' w
  | [], acc, _, _ => by rw [List.foldl_nil, wordS'_nil, mul_one]
  | x :: w, acc, hw, hacc => by
    obtain ⟨e, hl⟩ := wordS'_redStep acc (hw x List.mem_cons_self) hacc
    rw [List.foldl_cons, wordS'_foldl_redStep w _ (fun l h => hw l (List.mem_cons_of_mem _ h)) hl,
      e, wordS'_cons, mul_assoc]

theorem foldl_redStep_letters : ∀ (w acc : List ℤ), (∀ l ∈ w, IsLetter2 l) →
    (∀ l ∈ acc, IsLetter2 l) → ∀ l ∈ w.foldl Dyadic.redStep acc, IsLetter2 l
  | [], _, _, hacc => hacc
  | x :: w, acc, hw, hacc => foldl_redStep_letters w _ (fun l h => hw l (List.mem_cons_of_mem _ h))
      (wordS'_redStep acc (hw x List.mem_cons_self) hacc).2

theorem freeRed_letters {w : List ℤ} (hw : ∀ l ∈ w, IsLetter2 l) :
    ∀ l ∈ Dyadic.freeRed w, IsLetter2 l := by
  intro l hl
  rw [Dyadic.freeRed, List.mem_reverse] at hl
  exact foldl_redStep_letters w [] hw (by simp) l hl

theorem wordS'_freeRed {w : List ℤ} (hw : ∀ l ∈ w, IsLetter2 l) :
    wordS' (Dyadic.freeRed w) = wordS' w := by
  rw [Dyadic.freeRed, wordS'_foldl_redStep w [] hw (by simp), List.reverse_nil, wordS'_nil,
    one_mul]

section Beta


theorem beta_letterS {l : ℤ} (hl : IsLetter2 l) : (βr (letterS l)) = Dyadic.letterK l := by
  rcases hl with rfl | rfl | rfl | rfl
  · have e : Dyadic.letterK 1 = Dyadic.G1K := rfl
    rw [(letterS_eq (Or.inl rfl)).trans (ite_eq_left (Or.inl rfl)), beta_g0K, e]
  · have e : Dyadic.letterK (-1) = Dyadic.G1K := rfl
    rw [(letterS_eq (Or.inr (Or.inl rfl))).trans (ite_eq_left (Or.inr rfl)), beta_g0K, e]
  · have e : Dyadic.letterK 2 = Dyadic.G2K := rfl
    rw [(letterS_eq (Or.inr (Or.inr (Or.inl rfl)))).trans
      ((ite_eq_right (by decide)).trans (ite_eq_left rfl)), beta_g1K, e]
  · have e : Dyadic.letterK (-2) = Dyadic.Gi2K := rfl
    rw [(letterS_eq (Or.inr (Or.inr (Or.inr rfl)))).trans
      ((ite_eq_right (by decide)).trans (ite_eq_right (by decide))), beta_g1iK, e]

theorem beta_wordS' : ∀ {w : List ℤ}, (∀ l ∈ w, IsLetter2 l) →
    (βr (wordS' w)) = Dyadic.wordK w
  | [], _ => by rw [wordS'_nil, map_one, Units.val_one, Dyadic.wordK, List.map_nil, Dyadic.prodK]
  | l :: w, hw => by
    rw [wordS'_cons, map_mul, Units.val_mul, beta_letterS (hw l List.mem_cons_self),
      beta_wordS' fun l' h => hw l' (List.mem_cons_of_mem _ h), Dyadic.wordK, Dyadic.wordK,
      List.map_cons, Dyadic.prodK]

end Beta

theorem deltaWord_letters {k j : ℕ} (hk : IsRank k)
    (hj : j < 15) : ∀ l ∈ Dyadic.deltaWord (rankOff k + j), IsLetter2 l := by
  rw [deltaWord_eq hk hj]
  exact freeRed_letters (commWord_letters hk hj)

theorem deltaElt_eq_word {k j : ℕ}
    (hk : IsRank k) (hj : j < 15) : deltaElt k j = wordS' (Dyadic.deltaWord (rankOff k + j)) := by
  rw [deltaWord_eq hk hj, wordS'_freeRed (commWord_letters hk hj), wordS'_append, wordS'_append,
    wordS'_append, wordS'_invWord (liftWordZ_letters hk), wordS'_invWord (centWordN_letters hk hj),
    wordS'_liftWordZ hk, deltaElt, centElt]

end Kernel

end CFSG.Monster.B.CTIB
