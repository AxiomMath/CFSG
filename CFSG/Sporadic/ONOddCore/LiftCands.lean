module

public import CFSG.Sporadic.ONOddCore.LiftCheck
public import CFSG.Sporadic.ONOddCore.LiftBasics
public import CFSG.Sporadic.ONOddCore.QuotTauIso

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native

@[expose] def hGen
    (i : ℕ) : onM := hGens.getD i 1

theorem hGens_length :
    hGens.length = 3 := rfl

theorem hGen_val
    {i : ℕ} (hi : i < 3) :
    (hGen i : Equiv.Perm (Fin N)) = onMgens[i]'(by rw [onMgens_length]; exact hi) := by
  rw [hGen, List.getD_eq_getElem _ _ (by rw [hGens_length]; exact hi)]
  interval_cases i
  · exact mGen_val _
  · exact mGen_val _
  · exact mGen_val _

theorem hA_size :
    (wordArrs Data.MWords).size = 3 := by
  rw [wordArrs_size]
  exact onMgens_length

theorem prep_hA
    {i : ℕ} (hi : i < 3) :
    PRep N (wordArrs Data.MWords)[i]! (hGen i : Equiv.Perm (Fin N)) := by
  rw [hGen_val hi]
  exact prep_onMgens i _

theorem hGens_map_val :
    hGens.map (fun h => (h : Equiv.Perm (Fin N))) =
    [(hGen 0 : Equiv.Perm (Fin N)), hGen 1, hGen 2] := rfl

theorem prep_posArr_h
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    PRep N (posArr nPts (wordArrs Data.MWords) w)
      ((evalPos hGens w : onM) : Equiv.Perm (Fin N)) := by
  have e : ((evalPos hGens w : onM) : Equiv.Perm (Fin N)) =
      evalPos (hGens.map onM.subtype) w := map_evalPos onM.subtype hGens w
  rw [e]
  refine prep_posArr (fun l h1 h2 => ?_) w (fun l hl => ⟨(hw l hl).1, by
    rw [List.length_map, hGens_length]; exact (hw l hl).2⟩)
  rw [List.length_map, hGens_length] at h2
  have hl3 : l - 1 < 3 := by omega
  have e1 : (wordArrs Data.MWords).getD (l - 1) (pid nPts) = (wordArrs Data.MWords)[l - 1]! := by
    rw [Array.getD_eq_getD_getElem?, getElem!_pos _ _ (by rw [hA_size]; exact hl3),
      getElem?_pos _ _ (by rw [hA_size]; exact hl3), Option.getD_some]
  have e2 : (hGens.map onM.subtype).getD (l - 1) 1 = (hGen (l - 1) : Equiv.Perm (Fin N)) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hGens_length]; exact hl3),
      List.getElem_map, hGen, List.getD_eq_getElem _ _ (by rw [hGens_length]; exact hl3)]
    rfl
  rw [e1, e2]
  exact prep_hA hl3

theorem posPt_eq {gs : Array (Array ℕ)} {G : List (Equiv.Perm (Fin N))}
    (hG : ∀ l, 1 ≤ l → l ≤ G.length → PRep N (gs.getD (l - 1) #[]) (G.getD (l - 1) 1) ∧
      (gs.getD (l - 1) #[]).size = N) :
    ∀ w : List ℕ, (∀ l ∈ w, 1 ≤ l ∧ l ≤ G.length) → ∀ p : Fin N,
      posPt gs w p = (evalPos G w p : ℕ)
  | [], _, p => by simp [posPt, evalPos]
  | l :: w, hw, p => by
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    have ih := posPt_eq hG w (fun i hi => hw i (List.mem_cons_of_mem _ hi)) p
    have hpw : posPt gs (l :: w) p = (gs.getD (l - 1) #[])[posPt gs w p]?.getD (posPt gs w p) :=
      rfl
    rw [hpw, ih, evalPos_cons, Equiv.Perm.mul_apply]
    obtain ⟨hp, hs⟩ := hG l h1 h2
    rw [getElem?_pos _ _ (by rw [hs]; exact (evalPos G w p).2), Option.getD_some,
      ← getElem!_pos _ _ (by rw [hs]; exact (evalPos G w p).2)]
    exact hp _

theorem cand_facts :
    peq nPts (posArr nPts (wordArrs Data.MWords) liftData.qWord) qArr = true ∧
      (∀ l ∈ liftData.qWord, 1 ≤ l ∧ l ≤ 3) ∧
      (∀ i < 3, blockImgOK (wordArrs Data.MWords)[i]! Data.quotientBlocks
        (bTab (wordArrs Data.MWords)[i]!) = true ∧
        peq 120 (piArr (wordArrs Data.MWords)[i]!)
          (posArr 120 #[qgArr 0, qgArr 1] piWords[i]!) = true) ∧
      ∀ k < 12, candCheck (wordArrs Data.MWords) (localCert.records.getD k default)
        (liftData.lw.getD k []) (liftData.cands.getD k []) = true := by
  have h := cand_cert
  simp only [candidatesCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, -⟩, -⟩, h7⟩ := h
  refine ⟨h2, h1, fun i hi => ?_, h7⟩
  have := allBelowN_spec h4 hi
  simpa only [Bool.and_eq_true] using this

theorem candCheck_facts {k : ℕ} (hk : k < 12) :
    (liftData.lw.getD k []).length = 3 ∧
      (∀ w ∈ liftData.lw.getD k [], ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) ∧
      (∀ i < 3, blockImgOK (((liftData.lw.getD k []).map
          (posArr nPts (wordArrs Data.MWords))).toArray[i]!) Data.quotientBlocks
          (bTab (((liftData.lw.getD k []).map (posArr nPts (wordArrs Data.MWords))).toArray[i]!))
          = true ∧
        peq 120 (piArr (((liftData.lw.getD k []).map
          (posArr nPts (wordArrs Data.MWords))).toArray[i]!))
          (posArr 120 #[qiArr (recK k) 0, qiArr (recK k) 1] piWords[i]!) = true) ∧
      (liftData.cands.getD k []).length = 64 ∧
      ∀ a < 64, candOK (wordArrs Data.MWords)
        ((liftData.lw.getD k []).map (posArr nPts (wordArrs Data.MWords))).toArray (recK k) a
          ((liftData.cands.getD k []).getD a default) = true := by
  have h := cand_facts.2.2.2 k hk
  simp only [candCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun i hi => ?_, h4, h5⟩
  have := allBelowN_spec h3 hi
  rw [Bool.and_eq_true] at this
  exact this

theorem qM_eq :
    qM = evalPos hGens liftData.qWord :=
  Subtype.ext (eq_of_peq (prep_posArr_h cand_facts.2.1) prep_q cand_facts.1).symm

theorem prep_piArr
    {g : onM} {garr : Array ℕ} (hg : PRep N garr (g : Equiv.Perm (Fin N)))
    (hb : blockImgOK garr Data.quotientBlocks (bTab garr) = true) :
    PRep 120 (piArr garr) (piR g : Equiv.Perm (Fin 120)) := by
  have h := prep_pcomp prep_u (prep_pcomp (prep_rhoM hg hb) prep_u_inv)
  rw [← mul_assoc] at h
  exact h

theorem piWords_ok {i : ℕ} (hi : i < 3) : ∀ l ∈ piWords[i]!, 1 ≤ l ∧ l ≤ 2 := by
  interval_cases i <;> decide

theorem prep_pair_posArr {a b : Array ℕ} {A B : Equiv.Perm (Fin 120)} (ha : PRep 120 a A)
    (hb : PRep 120 b B) {i : ℕ} (hi : i < 3) :
    PRep 120 (posArr 120 #[a, b] piWords[i]!) (evalPos [A, B] piWords[i]!) := by
  refine prep_posArr (fun l h1 h2 => ?_) _ fun l hl => ⟨(piWords_ok hi l hl).1, by
    simpa using (piWords_ok hi l hl).2⟩
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases l
  · exact ha
  · exact hb

theorem piR_hGen
    {i : ℕ} (hi : i < 3) :
    (piR (hGen i) : Equiv.Perm (Fin 120)) = evalPos [qGenPerm 0, qGenPerm 1] piWords[i]! := by
  obtain ⟨hb, hp⟩ := cand_facts.2.2.1 i hi
  exact eq_of_peq (prep_piArr (prep_hA hi) hb)
    (prep_pair_posArr (prep_qgArr (by norm_num)).1 (prep_qgArr (by norm_num)).1 hi) hp

@[expose] def lwElem
    (k i : ℕ) : onM := evalPos hGens ((liftData.lw.getD k []).getD i [])

theorem prep_lwArr
    {k : ℕ} (hk : k < 12) {i : ℕ} (hi : i < 3) :
    PRep N (((liftData.lw.getD k []).map (posArr nPts (wordArrs Data.MWords))).toArray[i]!)
      (lwElem k i : Equiv.Perm (Fin N)) := by
  obtain ⟨hl, hw, -⟩ := candCheck_facts hk
  have hil : i < (liftData.lw.getD k []).length := by rw [hl]; exact hi
  rw [getElem!_pos _ _ (by simpa using hil), List.getElem_toArray, List.getElem_map, lwElem,
    List.getD_eq_getElem _ _ hil]
  exact prep_posArr_h (hw _ (List.getElem_mem hil))

theorem piR_lwElem
    {k : ℕ} (hk : k < 12) {i : ℕ} (hi : i < 3) :
    (piR (lwElem k i) : Equiv.Perm (Fin 120)) =
      evalPos [qImgPerm (recK k) 0, qImgPerm (recK k) 1] piWords[i]! := by
  obtain ⟨-, -, h3, -⟩ := candCheck_facts hk
  obtain ⟨hb, hp⟩ := h3 i hi
  have hr := recK_mem hk
  exact eq_of_peq (prep_piArr (prep_lwArr hk hi) hb)
    (prep_pair_posArr (prep_qiArr hr (by norm_num)).1 (prep_qiArr hr (by norm_num)).1 hi) hp

@[expose] def rq
    (j : ℕ) : RM := if hj : j < 2 then ⟨qGenPerm j, qGenPerm_mem_RM hj⟩ else 1

theorem tau_piR_hGen
    {k : ℕ} (hk : k < 12) {i : ℕ} (hi : i < 3) :
    tauAut k (piR (hGen i)) = piR (lwElem k i) := by
  have e1 : piR (hGen i) = evalPos [rq 0, rq 1] piWords[i]! := by
    apply Subtype.ext
    rw [piR_hGen hi]
    show _ = RM.subtype (evalPos [rq 0, rq 1] piWords[i]!)
    rw [map_evalPos]
    rfl
  apply Subtype.ext
  rw [e1, ← MulEquiv.coe_toMonoidHom, map_evalPos, piR_lwElem hk hi]
  have e2 := map_evalPos RM.subtype ([rq 0, rq 1].map (tauAut k).toMonoidHom) piWords[i]!
  rw [Subgroup.coe_subtype] at e2
  rw [e2]
  simp only [List.map_cons, List.map_nil, MulEquiv.coe_toMonoidHom]
  rw [show rq 0 = ⟨qGenPerm 0, qGenPerm_mem_RM (by norm_num)⟩ from rfl,
    show rq 1 = ⟨qGenPerm 1, qGenPerm_mem_RM (by norm_num)⟩ from rfl,
    tauAut_gen hk (by norm_num), tauAut_gen hk (by norm_num)]

@[expose] def liftSet
    (k : ℕ) : Set (MulAut onM) := {β | descendAut β = tauAut k}

theorem fibre
    {k : ℕ} (hk : k < 12) {β : MulAut onM} (hβ : β ∈ liftSet k) {i : ℕ} (hi : i < 3) :
    ∃ a < 4, β (hGen i) = lwElem k i * qM ^ a := by
  have h1 : piR (β (hGen i)) = piR (lwElem k i) := by
    rw [← descendAut_piR, show descendAut β = tauAut k from hβ, tau_piR_hGen hk hi]
  have h2 : piR ((lwElem k i)⁻¹ * β (hGen i)) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨a, ha, he⟩ := eq_qM_pow_of_piR h2
  exact ⟨a, ha, by rw [← he, mul_inv_cancel_left]⟩

theorem posPt_spec {gs : Array (Array ℕ)} {G : ℕ → Equiv.Perm (Fin N)} {m : ℕ}
    (hG : ∀ i < m, PRep N (gs.getD i #[]) (G i) ∧ (gs.getD i #[]).size = N) :
    ∀ w : List ℕ, (∀ l ∈ w, 1 ≤ l ∧ l ≤ m) → ∀ p : Fin N,
      posPt gs w p = ((w.map fun l => G (l - 1)).prod p : ℕ)
  | [], _, p => by simp [posPt]
  | l :: w, hw, p => by
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    have ih := posPt_spec hG w (fun i hi => hw i (List.mem_cons_of_mem _ hi)) p
    have hpw : posPt gs (l :: w) p = (gs.getD (l - 1) #[])[posPt gs w p]?.getD (posPt gs w p) :=
      rfl
    obtain ⟨hp, hs⟩ := hG (l - 1) (by omega)
    set x : Fin N := (w.map fun l => G (l - 1)).prod p
    rw [hpw, ih, getElem?_pos _ _ (by rw [hs]; exact x.2), Option.getD_some,
      ← getElem!_pos _ _ (by rw [hs]; exact x.2), hp x, List.map_cons, List.prod_cons,
      Equiv.Perm.mul_apply]

theorem evalPos_eq_prod {H : Type*} [Group H] (imgs : List H) (w : List ℕ) :
    evalPos imgs w = (w.map fun l => imgs.getD (l - 1) 1).prod := rfl

theorem hA_getD
    {i : ℕ} (hi : i < 3) :
    PRep N ((wordArrs Data.MWords).getD i #[]) (hGen i : Equiv.Perm (Fin N)) ∧
      ((wordArrs Data.MWords).getD i #[]).size = N := by
  have e : (wordArrs Data.MWords).getD i #[] = (wordArrs Data.MWords)[i]! := by
    rw [Array.getD_eq_getD_getElem?, getElem!_pos _ _ (by rw [hA_size]; exact hi),
      getElem?_pos _ _ (by rw [hA_size]; exact hi), Option.getD_some]
  rw [e]
  refine ⟨prep_hA hi, ?_⟩
  rw [wordArrs, pwords_eq, getElem!_map' _ _ (by
    rw [show Data.MWords.size = 3 by decide]; exact hi)]
  exact pword_size _ _ _ _

theorem getD_map_subtype
    (L : List onM) (i : ℕ) :
    (L.map onM.subtype).getD i 1 = ((L.getD i 1 : onM) : Equiv.Perm (Fin N)) := by
  rw [← map_one onM.subtype, List.getD_map]
  rfl

theorem coe_evalPos
    (L : List onM) (w : List ℕ) :
    ((evalPos L w : onM) : Equiv.Perm (Fin N)) =
      (w.map fun l => ((L.getD (l - 1) 1 : onM) : Equiv.Perm (Fin N))).prod := by
  rw [← onM.subtype_apply, map_evalPos, evalPos_eq_prod]
  congr 1
  apply List.map_congr_left
  intro l _
  exact getD_map_subtype L (l - 1)

theorem coe_evalPos_hGens
    (w : List ℕ) :
    ((evalPos hGens w : onM) : Equiv.Perm (Fin N)) =
      (w.map fun l => (hGen (l - 1) : Equiv.Perm (Fin N))).prod :=
  coe_evalPos hGens w

@[expose] def digit (a : ℕ) : ℕ → ℕ
  | 0 => a / 16
  | 1 => a / 4 % 4
  | _ => a % 4

@[expose] def candElem
    (k a i : ℕ) : onM := lwElem k i * qM ^ digit a i

theorem coe_qM_pow
    (e : ℕ) : ((qM ^ e : onM) : Equiv.Perm (Fin N)) = onq ^ e := by
  rw [Subgroup.coe_pow]
  rfl

theorem candImgs_getD_zero (lw : Array (Array ℕ)) (a : ℕ) :
    (candImgs lw a).getD 0 #[] = pcomp nPts lw[0]! (qPowArr (a / 16)) := by
  simp [candImgs]

theorem candImgs_getD_one (lw : Array (Array ℕ)) (a : ℕ) :
    (candImgs lw a).getD 1 #[] = pcomp nPts lw[1]! (qPowArr (a / 4 % 4)) := by
  simp [candImgs]

theorem candImgs_getD_two (lw : Array (Array ℕ)) (a : ℕ) :
    (candImgs lw a).getD 2 #[] = pcomp nPts lw[2]! (qPowArr (a % 4)) := by
  simp [candImgs]

theorem pcomp_size_gen (n : ℕ) (t u : Array ℕ) : (pcomp n t u).size = n := Array.size_ofFn

theorem pcomp_size_N (t u : Array ℕ) : (pcomp nPts t u).size = N := pcomp_size_gen nPts t u

theorem candImgs_getD
    {k : ℕ} (hk : k < 12) (a : ℕ) {i : ℕ} (hi : i < 3) :
    PRep N ((candImgs ((liftData.lw.getD k []).map (posArr nPts (wordArrs Data.MWords))).toArray
      a).getD i #[]) (candElem k a i : Equiv.Perm (Fin N)) ∧
      ((candImgs ((liftData.lw.getD k []).map (posArr nPts (wordArrs Data.MWords))).toArray
        a).getD i #[]).size = N := by
  interval_cases i
  · rw [candImgs_getD_zero]
    refine ⟨?_, pcomp_size_N _ _⟩
    have := prep_pcomp (prep_lwArr hk (i := 0) (by norm_num)) (prep_qPow (a / 16))
    rw [candElem, Subgroup.coe_mul, coe_qM_pow]
    exact this
  · rw [candImgs_getD_one]
    refine ⟨?_, pcomp_size_N _ _⟩
    have := prep_pcomp (prep_lwArr hk (i := 1) (by norm_num)) (prep_qPow (a / 4 % 4))
    rw [candElem, Subgroup.coe_mul, coe_qM_pow]
    exact this
  · rw [candImgs_getD_two]
    refine ⟨?_, pcomp_size_N _ _⟩
    have := prep_pcomp (prep_lwArr hk (i := 2) (by norm_num)) (prep_qPow (a % 4))
    rw [candElem, Subgroup.coe_mul, coe_qM_pow]
    exact this

theorem mem_base3Arr {p : ℕ} (hp : p ∈ base3Arr) : p < N := by
  simp only [base3Arr, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem not_hom_of_rel
    {k : ℕ} (hk : k < 12) {a : ℕ} (ha : a < 64) {w w' : List ℕ}
    (hc : (liftData.cands.getD k []).getD a default = .rel w w') (φ : onM →* onM)
    (hφ : ∀ i < 3, φ (hGen i) = candElem k a i) : False := by
  have hok := (candCheck_facts hk).2.2.2.2 a ha
  rw [hc] at hok
  simp only [candOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Array.all_eq_true',
    Array.any_eq_true', beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨hw, hw'⟩, hh⟩, ⟨p, hp, hne⟩⟩ := hok
  have hpt : ∀ v ∈ [w, w'], ∀ (p : ℕ) (hp : p < N),
      posPt (wordArrs Data.MWords) v p =
        ((evalPos hGens v : onM) : Equiv.Perm (Fin N)) ⟨p, hp⟩ := by
    intro v hv p hp
    have hvl : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hw
      · exact hw'
    rw [posPt_spec (m := 3) (fun i hi => hA_getD hi) v hvl ⟨p, hp⟩, coe_evalPos_hGens]
  have hagree : ∀ p (hp : p < N), p ∈ base3Arr →
      ((evalPos hGens w : onM) : Equiv.Perm (Fin N)) ⟨p, hp⟩ =
        ((evalPos hGens w' : onM) : Equiv.Perm (Fin N)) ⟨p, hp⟩ := by
    intro p hp hpb
    apply Fin.ext
    rw [← hpt w (by simp) p hp, ← hpt w' (by simp) p hp]
    exact hh p hpb
  have heq : evalPos hGens w = evalPos hGens w' := by
    apply Subtype.ext
    exact eq_of_three (onM_le (evalPos hGens w).2) (onM_le (evalPos hGens w').2)
      (hagree 0 (by norm_num) (by simp [base3Arr]))
      (hagree 227759 (by norm_num) (by simp [base3Arr]))
      (hagree 100817 (by norm_num) (by simp [base3Arr]))
  have himg : hGens.map φ = [candElem k a 0, candElem k a 1, candElem k a 2] := by
    simp only [hGens, List.map_cons, List.map_nil]
    rw [← hφ 0 (by norm_num), ← hφ 1 (by norm_num), ← hφ 2 (by norm_num)]
    rfl
  have heq' := congrArg φ heq
  rw [map_evalPos, map_evalPos, himg] at heq'
  apply hne
  have hpN := mem_base3Arr hp
  have hc3 : ∀ v ∈ [w, w'], posPt (candImgs ((liftData.lw.getD k []).map
      (posArr nPts (wordArrs Data.MWords))).toArray a) v p =
        ((evalPos [candElem k a 0, candElem k a 1, candElem k a 2] v : onM) :
          Equiv.Perm (Fin N)) ⟨p, hpN⟩ := by
    intro v hv
    have hvl : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hw
      · exact hw'
    rw [posPt_spec (m := 3) (fun i hi => candImgs_getD hk a hi) v hvl ⟨p, hpN⟩, coe_evalPos]
    congr 3
    apply List.map_congr_left
    intro l hl
    have h1 := hvl l hl
    have hl3 : l - 1 < 3 := by omega
    interval_cases hl' : l - 1 <;> rfl
  rw [hc3 w (by simp), hc3 w' (by simp), heq']

end CFSG.Sporadic.ONOddCore
