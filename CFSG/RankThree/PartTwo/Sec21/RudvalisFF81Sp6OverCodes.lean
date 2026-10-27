module

public import Certificates.Certificate899108
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6OverLin
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH mat6_zH mat6_tH tH_conj dec6_powCode
  card_wreathW_zH powCode zCode tCode)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (wreathW baseA)
open CFSG.Quasithin.H13.MatNCert Matrix

section Generic

theorem eq_of_mat6_dec6 {g h : H6} {c : List ℕ} (hg : mat6 g = dec6 c) (hh : mat6 h = dec6 c) :
    g = h :=
  mat6_injective (hg.trans hh.symm)

theorem length_getD3 {n : ℕ} {a b c : List ℕ} (ha : a.length = n) (hb : b.length = n)
    (hc : c.length = n) (i : ℕ) : ([a, b, c].getD i (oneN n)).length = n := by
  rcases i with _ | _ | _ | i <;> simp [ha, hb, hc, oneN]

theorem validN_nGc : ValidN 7 nGc := validB_iff.mp (by decide)

theorem validN_nHc : ValidN 7 nHc := validB_iff.mp (by decide)

theorem validN_xSc : ValidN 7 xSc := validB_iff.mp (by decide)

theorem validN_xIc : ValidN 7 xIc := validB_iff.mp (by decide)

theorem n2c_eq : n2c = [1, 2, 8, 12, 16, 64, 112] := by decide

theorem list_eq_seven {l : List ℕ} (h : l.length = 7) :
    ∃ x0 x1 x2 x3 x4 x5 x6 : ℕ, l = [x0, x1, x2, x3, x4, x5, x6] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all

theorem mulN_n2c (x0 x1 x2 x3 x4 x5 x6 : ℕ) :
    mulN [x0, x1, x2, x3, x4, x5, x6] n2c = [x0, x1, x3, x2 ^^^ x3, x4, x6, x4 ^^^ x5 ^^^ x6] := by
  simp [n2c_eq, mulN, mvN, Nat.xor_assoc]

theorem xor_aux (a b c : ℕ) : (a ^^^ b ^^^ c) ^^^ a = (b ^^^ a) ^^^ (c ^^^ a) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem xor_xor_cancel (a b : ℕ) : a ^^^ b ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem vecN_one : vecN 7 1 = Pi.single 0 1 := by
  ext i
  fin_cases i <;> rfl

theorem nG_eq : nG = decN 7 nGc := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem nH_eq : nH = decN 7 nHc := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Generic

section Cert


theorem cert899108_parts :
    (pairCheck (ovGamC, ovGamI) = true ∧ pairCheck (ovHC, ovHI) = true ∧
      pairCheck (ovCC, ovCI) = true ∧ relW.all (fun r => powCode (wordC r.1) r.2 == one6) = true ∧
      powCode ovGamC 7 = one6 ∧ ovGamC ≠ one6 ∧ powCode ovHC 6 = one6 ∧
      mul6 ovHC ovGamC = mul6 (powCode ovGamC 3) ovHC ∧
      mul6 ovCC (mul6 ovHC ovHC) = mul6 (mul6 ovHC ovHC) ovCC ∧
      wordC wZ0 = zCode 0 ∧ wordC wZ1 = zCode 1 ∧ wordC wT = tCode ∧
      wS.map wordC = sylowP.map Prod.fst ∧ powCode (wordC [0, 1, 2]) 5 = one6 ∧
      wordC [0, 1, 2] ≠ one6) ∧
    ((∀ c < 128, mvN n2c c = c → c ∈ fixL) ∧
      (∀ c < 128, mvN n2c (mvN n2c c) = (c ^^^ mvN n2c c) → c ∈ wL) ∧
      (∀ a ∈ fixL, ∀ u ∈ wL, ∀ b ∈ fixL, ∀ v ∈ wL, relsOK (cand a u b v) = true →
        cand a u b v = xSc ∨ cand a u b v = xIc)) ∧
    (∀ x : List ℕ, x = xSc ∨ x = xIc →
      (∀ m, 0 < m → m < 64 → ∃ s ∈ genSubN 7 [nGc, nHc, x],
        decN 7 (kC m) = ((s : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          decN 7 (kC 1) * ((s⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) ∧
      ((List.range 128).filter fun v => mvN (bbarC x) v == v).length = 32 ∧
      (∀ g ∈ rGens x, mulN g (bbarC x) = mulN (bbarC x) g) ∧
      (∀ m ∈ [6, 8, 17, 33], mulN (kC m) (kC m) = oneN 7) ∧
      Nat.card (genSubN 7 (rGens x)) = 32) ∧
    (piC xIc = piC xSc ∧
      (∀ u ∈ uGens, mulN u u = oneN 6 ∧ mulN u pibbarC = mulN pibbarC u) ∧
      Nat.card (genSubN 6 uGens) = 32) ∧
    ((∀ g ∈ sbGens, (decN 6 g)ᵀ * decN 6 w0c * decN 6 g = decN 6 w0c) ∧
      (∀ g ∈ sbGens ++ grs, ∃ u : GL (Fin 6) (ZMod 2),
        (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) = decN 6 g) ∧
      ∃ T : ℕ → List (Matrix (Fin 6) (Fin 6) (ZMod 2)), T 0 = [decN 6 w0c] ∧
        (∀ r < 5, (T (r + 1)).length = [315, 2880, 2880, 3780, 4032].getD r 0) ∧
        ((List.range 6).flatMap T).Nodup ∧
        ∀ r < 5, ∀ x ∈ T (r + 1), ∃ u : GL (Fin 6) (ZMod 2),
          (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) = decN 6 (grs.getD r []) ∧
          ∃ s ∈ genSubN 6 sbGens,
            x = ((u * s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * decN 6 w0c *
              ((u * s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) :=
  Certificates.certificate899108

theorem h6_parts : pairCheck (ovGamC, ovGamI) = true ∧ pairCheck (ovHC, ovHI) = true ∧
    pairCheck (ovCC, ovCI) = true ∧ relW.all (fun r => powCode (wordC r.1) r.2 == one6) = true ∧
    powCode ovGamC 7 = one6 ∧ ovGamC ≠ one6 ∧ powCode ovHC 6 = one6 ∧
    mul6 ovHC ovGamC = mul6 (powCode ovGamC 3) ovHC ∧
    mul6 ovCC (mul6 ovHC ovHC) = mul6 (mul6 ovHC ovHC) ovCC ∧
    wordC wZ0 = zCode 0 ∧ wordC wZ1 = zCode 1 ∧ wordC wT = tCode ∧
    wS.map wordC = sylowP.map Prod.fst ∧ powCode (wordC [0, 1, 2]) 5 = one6 ∧
    wordC [0, 1, 2] ≠ one6 :=
  cert899108_parts.1

@[expose] noncomputable def gamH : H6 := ofCode (ovGamC, ovGamI) h6_parts.1

@[expose] noncomputable def hH : H6 := ofCode (ovHC, ovHI) h6_parts.2.1

@[expose] noncomputable def cH : H6 := ofCode (ovCC, ovCI) h6_parts.2.2.1

theorem mat6_gamH : mat6 gamH = dec6 ovGamC := mat6_ofCode _ _

theorem mat6_hH : mat6 hH = dec6 ovHC := mat6_ofCode _ _

theorem mat6_cH : mat6 cH = dec6 ovCC := mat6_ofCode _ _

@[expose] noncomputable def genH (i : ℕ) : H6 :=
  if i = 0 then gamH else if i = 1 then hH else if i = 2 then cH else 1

@[expose] noncomputable def wordH (w : List ℕ) : H6 := (w.map genH).prod

theorem mat6_genH (i : ℕ) : mat6 (genH i) = dec6 (genC.getD i one6) := by
  rcases i with _ | _ | _ | i
  · simp [genH, genC, mat6_gamH]
  · simp [genH, genC, mat6_hH]
  · simp [genH, genC, mat6_cH]
  · simp [genH, genC, dec6_one6]

theorem wordH_cons (i : ℕ) (w : List ℕ) : wordH (i :: w) = genH i * wordH w := by
  rw [wordH, List.map_cons, List.prod_cons, ← wordH]

theorem mat6_wordH (w : List ℕ) : mat6 (wordH w) = dec6 (wordC w) := by
  induction w with
  | nil => simp [wordH, wordC, dec6_one6]
  | cons i w ih =>
    rw [wordH_cons, map_mul, ih, mat6_genH,
      show wordC (i :: w) = mul6 (genC.getD i one6) (wordC w) from rfl, dec6_mul6]

theorem wordH_pow_eq_one {w : List ℕ} {k : ℕ} (h : powCode (wordC w) k = one6) :
    wordH w ^ k = 1 := by
  apply mat6_injective
  rw [map_pow, mat6_wordH, ← dec6_powCode, h, dec6_one6, map_one]

theorem wordH_rel {r : List ℕ × ℕ} (hr : r ∈ relW) : wordH r.1 ^ r.2 = 1 :=
  wordH_pow_eq_one (by simpa using List.all_eq_true.mp h6_parts.2.2.2.1 r hr)

theorem gamH_pow_seven : gamH ^ 7 = 1 := by
  apply mat6_injective
  rw [map_pow, mat6_gamH, ← dec6_powCode, h6_parts.2.2.2.2.1, dec6_one6, map_one]

theorem gamH_ne_one : gamH ≠ 1 := by
  intro h
  have e := congrArg mat6 h
  rw [mat6_gamH, map_one, ← dec6_one6] at e
  exact h6_parts.2.2.2.2.2.1 (dec6_injective (pairCheck_spec h6_parts.1).1 canon6_one6 e)

theorem hH_pow_six : hH ^ 6 = 1 := by
  apply mat6_injective
  rw [map_pow, mat6_hH, ← dec6_powCode, h6_parts.2.2.2.2.2.2.1, dec6_one6, map_one]

theorem hH_mul_gamH : hH * gamH = gamH ^ 3 * hH := by
  apply mat6_injective
  rw [map_mul, map_mul, map_pow, mat6_hH, mat6_gamH, ← dec6_powCode, ← dec6_mul6, ← dec6_mul6,
    h6_parts.2.2.2.2.2.2.2.1]

theorem cH_comm : cH * (hH * hH) = hH * hH * cH := by
  apply mat6_injective
  simp only [map_mul, mat6_hH, mat6_cH, ← dec6_mul6]
  rw [h6_parts.2.2.2.2.2.2.2.2.1]

theorem orderOf_gamH : orderOf gamH = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime gamH_pow_seven gamH_ne_one

theorem orderOf_ghc : orderOf (wordH [0, 1, 2]) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (wordH_pow_eq_one h6_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  intro h
  have e := congrArg mat6 h
  rw [mat6_wordH, map_one, ← dec6_one6] at e
  have hc : canon6 (wordC [0, 1, 2]) = true := by
    rw [wordC, List.foldr_cons]
    exact canon6_mul6 _ _
  exact h6_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (dec6_injective hc canon6_one6 e)

end Cert

section Gen


theorem genH_mem (i : ℕ) : genH i ∈ Subgroup.closure ({gamH, hH, cH} : Set H6) := by
  unfold genH
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact one_mem _

theorem wordH_mem (w : List ℕ) : wordH w ∈ Subgroup.closure ({gamH, hH, cH} : Set H6) := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih => rw [wordH_cons]; exact mul_mem (genH_mem i) ih


theorem zH_zero_eq : zH 0 = wordH wZ0 :=
  eq_of_mat6_dec6 (mat6_zH 0) ((mat6_wordH _).trans (by rw [h6_parts.2.2.2.2.2.2.2.2.2.1]))

theorem zH_one_eq : zH 1 = wordH wZ1 :=
  eq_of_mat6_dec6 (mat6_zH 1) ((mat6_wordH _).trans (by rw [h6_parts.2.2.2.2.2.2.2.2.2.2.1]))

theorem tH_eq : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH = wordH wT :=
  eq_of_mat6_dec6 mat6_tH ((mat6_wordH _).trans (by rw [h6_parts.2.2.2.2.2.2.2.2.2.2.2.1]))

theorem wreathW_le :
    wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ≤
      Subgroup.closure ({gamH, hH, cH} : Set H6) := by
  set Cl := Subgroup.closure ({gamH, hH, cH} : Set H6)
  have h0 : zH 0 ∈ Cl := zH_zero_eq ▸ wordH_mem _
  have h1 : zH 1 ∈ Cl := zH_one_eq ▸ wordH_mem _
  have ht : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ∈ Cl := tH_eq ▸ wordH_mem _
  have h2 : zH 2 ∈ Cl := by
    have e := tH_conj 1
    rw [show (1 : Fin 3) + 1 = 2 from rfl] at e
    rw [← e]
    exact mul_mem (mul_mem ht h1) (inv_mem ht)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact (Subgroup.zpowers_le).mpr h0
  · exact (Subgroup.zpowers_le).mpr h1
  · exact (Subgroup.zpowers_le).mpr h2
  · exact (Subgroup.zpowers_le).mpr ht

theorem SH_le : SH ≤ Subgroup.closure ({gamH, hH, cH} : Set H6) := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro _ ⟨cc, hm, rfl⟩
  have hc : cc.1 ∈ wS.map wordC := by
    rw [h6_parts.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact List.mem_map_of_mem hm
  obtain ⟨w, -, hw⟩ := List.mem_map.mp hc
  rw [eq_of_mat6_dec6 (mat6_ofCode _ _) ((mat6_wordH w).trans (by rw [hw]))]
  exact wordH_mem w

theorem closure_gens_eq_top : Subgroup.closure ({gamH, hH, cH} : Set H6) = ⊤ := by
  set Cl := Subgroup.closure ({gamH, hH, cH} : Set H6)
  have d512 : 512 ∣ Nat.card Cl := card_SH ▸ Subgroup.card_dvd_of_le SH_le
  have d81 : 81 ∣ Nat.card Cl := card_wreathW_zH ▸ Subgroup.card_dvd_of_le wreathW_le
  have d7 : 7 ∣ Nat.card Cl := by
    rw [← orderOf_gamH]
    exact Subgroup.orderOf_dvd_natCard Cl (Subgroup.subset_closure (by simp))
  have d5 : 5 ∣ Nat.card Cl := by
    rw [← orderOf_ghc]
    exact Subgroup.orderOf_dvd_natCard Cl (wordH_mem _)
  have hd : 1451520 ∣ Nat.card Cl := by
    have h1 : 512 * 81 ∣ Nat.card Cl := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d512 d81
    have h2 : 512 * 81 * 5 ∣ Nat.card Cl := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 d5
    have h3 : 512 * 81 * 5 * 7 ∣ Nat.card Cl :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 d7
    simpa using h3
  have hle : Nat.card Cl ≤ 1451520 := card_H6 ▸ Subgroup.card_le_card_group Cl
  have hpos : 0 < Nat.card Cl := Nat.card_pos
  have heq : Nat.card Cl = Nat.card H6 := by
    rw [card_H6]
    exact le_antisymm hle (Nat.le_of_dvd hpos hd)
  exact Subgroup.card_eq_iff_eq_top Cl |>.mp heq

end Gen

section Words

variable {n : ℕ}

theorem coe_wordH (σ : H6 →* GL (Fin n) (ZMod 2)) {a b c : List ℕ} (ha : a.length = n)
    (hb : b.length = n) (hc : c.length = n)
    (hσa : ((σ gamH : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n a)
    (hσb : ((σ hH : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n b)
    (hσc : ((σ cH : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n c)
    (w : List ℕ) : ((σ (wordH w) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      decN n (evalW n [a, b, c] w) := by
  induction w with
  | nil => simp [wordH, evalW, decN_oneN]
  | cons i w ih =>
    rw [wordH_cons, map_mul, Units.val_mul, ih, evalW_cons,
      decN_mulN (length_getD3 ha hb hc i) (length_evalW _ _)]
    congr 1
    rcases i with _ | _ | _ | i
    · simpa [genH] using hσa
    · simpa [genH] using hσb
    · simpa [genH] using hσc
    · simp [genH, decN_oneN]

theorem colsN_wordH (σ : H6 →* GL (Fin n) (ZMod 2)) {a b c : List ℕ} (ha : ValidN n a)
    (hb : ValidN n b) (hc : ValidN n c)
    (hσa : ((σ gamH : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n a)
    (hσb : ((σ hH : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n b)
    (hσc : ((σ cH : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n c)
    (w : List ℕ) : colsN ((σ (wordH w) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      evalW n [a, b, c] w := by
  rw [coe_wordH σ ha.1 hb.1 hc.1 hσa hσb hσc w, colsN_decN]
  refine validN_evalW _ (fun g hg => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> assumption

end Words

section Pin


theorem pin_parts : (∀ c < 128, mvN n2c c = c → c ∈ fixL) ∧
    (∀ c < 128, mvN n2c (mvN n2c c) = (c ^^^ mvN n2c c) → c ∈ wL) ∧
    (∀ a ∈ fixL, ∀ u ∈ wL, ∀ b ∈ fixL, ∀ v ∈ wL, relsOK (cand a u b v) = true →
      cand a u b v = xSc ∨ cand a u b v = xIc) :=
  cert899108_parts.2.1

theorem pin (σ : H6 →* GL (Fin 7) (ZMod 2))
    (hg : ((σ gamH : GL (Fin 7) (ZMod 2)) : M7) = decN 7 nGc)
    (hh : ((σ hH : GL (Fin 7) (ZMod 2)) : M7) = decN 7 nHc)
    (h0 : ((σ cH : GL (Fin 7) (ZMod 2)) : M7) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    ((σ cH : GL (Fin 7) (ZMod 2)) : M7) = decN 7 xSc ∨
      ((σ cH : GL (Fin 7) (ZMod 2)) : M7) = decN 7 xIc := by
  set X : M7 := ((σ cH : GL (Fin 7) (ZMod 2)) : M7) with hXdef
  have hxv : ValidN 7 (colsN X) := validN_colsN X
  have hX : X = decN 7 (colsN X) := (decN_colsN X).symm
  have hrel : relsOK (colsN X) = true := by
    unfold relsOK
    rw [List.all_eq_true]
    intro r hr
    have e := colsN_wordH σ validN_nGc validN_nHc hxv hg hh hX r.1
    have h1 : (σ (wordH r.1)) ^ r.2 = 1 := by rw [← map_pow, wordH_rel hr, map_one]
    have h2 := congrArg (fun u : GL (Fin 7) (ZMod 2) => colsN (u : M7)) h1
    rw [colsN_pow, Units.val_one, colsN_one, e] at h2
    simp [h2]
  have hcomm : mulN (colsN X) n2c = mulN n2c (colsN X) := by
    have hn2 : decN 7 n2c = decN 7 nHc * decN 7 nHc := decN_mulN rfl rfl
    have e := congrArg (fun u : GL (Fin 7) (ZMod 2) => (u : M7)) (congrArg σ cH_comm)
    simp only [map_mul, Units.val_mul] at e
    rw [hh] at e
    have hv2 : ValidN 7 n2c := validN_mulN validN_nHc validN_nHc
    refine decN_injOn (validN_mulN hxv hv2) (validN_mulN hv2 hxv) ?_
    rw [decN_mulN hxv.1 hv2.1, decN_mulN hv2.1 hxv.1, ← hX, hn2]
    exact e
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, hx⟩ := list_eq_seven hxv.1
  have hlt : ∀ c ∈ colsN X, c < 128 := hxv.2
  rw [hx] at hcomm hlt hrel
  rw [mulN_n2c] at hcomm
  simp only [mulN, List.map_cons, List.map_nil, List.cons.injEq] at hcomm
  obtain ⟨-, e1, e3, e23, e4, e6, e456, -⟩ := hcomm
  have l1 : x1 < 128 := hlt x1 (by simp)
  have l2 : x2 < 128 := hlt x2 (by simp)
  have l4 : x4 < 128 := hlt x4 (by simp)
  have l5 : x5 < 128 := hlt x5 (by simp)
  have l0 : x0 < 128 := hlt x0 (by simp)
  have hx0 : x0 = 1 := by
    have e := h0
    rw [hX, hx, ← vecN_one, decN_mulVec (by rfl)] at e
    have e' : vecN 7 x0 = vecN 7 1 := by simpa [mvN] using e
    exact vecN_inj (n := 7) (by simpa using l0) (by norm_num) e'
  have m1 : x1 ∈ fixL := pin_parts.1 x1 l1 e1.symm
  have m4 : x4 ∈ fixL := pin_parts.1 x4 l4 e4.symm
  have m2 : x2 ∈ wL := pin_parts.2.1 x2 l2 (by rw [← e3, ← e23])
  set v := x5 ^^^ x4 with hv
  have hmv : mvN n2c v = x6 ^^^ x4 := by rw [hv, mvN_xor, ← e6, ← e4]
  have lv : v < 128 := Nat.xor_lt_two_pow (n := 7) l5 l4
  have m5 : v ∈ wL := by
    refine pin_parts.2.1 v lv ?_
    rw [hmv, mvN_xor, ← e456, ← e4, hv, xor_aux]
  have hcand : [x0, x1, x2, x3, x4, x5, x6] = cand x1 x2 x4 v := by
    rw [cand, hx0, ← e3, hmv, hv, xor_xor_cancel, xor_xor_cancel]
  rw [hcand] at hrel
  rcases pin_parts.2.2 x1 m1 x2 m2 x4 m4 v m5 hrel with h | h
  · left; rw [hX, hx, hcand, h]
  · right; rw [hX, hx, hcand, h]

end Pin

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
