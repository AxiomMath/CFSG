module

public import Certificates.Kernel.AE5X.Checks
public import Certificates.Kernel.AE5Sq.Glue
public import CFSG.Certificates.Kernel.WrPackXSound
public import Certificates.Data.AE5X

public section

namespace CFSG.KD.AE5X

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.KC.WrPackX CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117 Certificates.AE5Sq CFSG.KD.AE5Sq
  Certificates.AE5X

theorem pinsX : P120lit = P120 ∧
    Ms3lit = M10lit.map (List.map fun m => (m, pm 5 m pilit, ord4P 5 e10L pilit m)) ∧
    Mall2lit = dbl 5 pilit M10lit.flatten := by
  have h := x5_pins
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem heX : enc (1 : Wr 5) = e10L := he5

theorem mem_P120lit (σ : Equiv.Perm (Fin 5)) : lvl σ ∈ P120lit := by
  rw [pinsX.1]
  exact mem_P120 σ

theorem hP60 : ∀ t ∈ P60lit, ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ t = lvl σ := by
  intro t ht
  rw [pins2.1] at ht
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 ht
  exact ⟨σ, of_decide_eq_true (List.mem_filter.1 hσ).2, rfl⟩

theorem hV16 : ∀ v ∈ V16lit, ∃ x : Fin 5 → ZMod 2, ∑ i, x i = 0 ∧ v = enc (ofVec x) := by
  intro v hv
  rw [pins2.2.1, Veven_eq] at hv
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
  unfold VevenW at hy
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
  exact ⟨vecL l, of_decide_eq_true (List.mem_filter.1 hl).2, rfl⟩

theorem isAE_of (σ : Equiv.Perm (Fin 5)) (x : Fin 5 → ZMod 2) (hσ : Equiv.Perm.sign σ = 1)
    (hx : ∑ i, x i = 0) : isAE (ofVec x * ofPerm σ) = true := by
  have h : ofVec x * ofPerm σ = (⟨x, σ⟩ : Wr 5) := ofVec_mul_ofPerm ⟨x, σ⟩
  rw [h]
  simp only [isAE, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hx, hσ⟩

theorem pm5 (x y : Wr 5) : pm 5 (enc x) (enc y) = enc (x * y) := pm_enc hn5 x y

theorem eqPiP5 (x y : Wr 5) : eqPiP 5 pilit (enc x) (enc y) = eqPi x y := eqPiP_enc hn5 hp5 x y

theorem inPiP5 (x : Wr 5) : inPiP e10L pilit (enc x) = inPi x := inPiP_enc hn5 heX hp5 x

theorem cj5g (x w v : Wr 5) : cj 5 (enc x) (enc w) (enc v) = enc (w * x * v) := by
  unfold cj
  rw [pm5, pm5]

theorem inVP5 (x : Wr 5) : inVP 5 e10L (enc x) = inV x := by
  unfold inVP inV
  rw [← heX]
  refine Bool.eq_iff_iff.2 ?_
  rw [samePerm_iff hn5, decide_eq_true_iff]
  rfl

theorem ord4W_eq (x : Wr 5) : ord4W x = ord4Pi x := rfl

theorem getD_map' {α β : Type} (f : α → β) :
    ∀ (L : List α) (i : Nat) (d : α), (L.map f).getD i (f d) = f (L.getD i d)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: L, i + 1, d => getD_map' f L i d

theorem mem_M10W {l : Lab} (hl : l ∈ labs) : memL l ∈ M10W := by
  simp only [labs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hl
  obtain ⟨α, hα, hl⟩ := hl
  obtain ⟨q, hq, hm⟩ := memAtL_of_alphas hα
  refine List.mem_flatMap.2 ⟨q, hq, ?_⟩
  rcases hl with rfl | rfl
  · exact List.mem_map.2 ⟨true, by simp, (hm true).symm⟩
  · exact List.mem_map.2 ⟨false, by simp, (hm false).symm⟩

theorem enc_M10 {l : Lab} (hl : l ∈ labs) : (memL l).map enc ∈ M10lit := by
  rw [pins2.2.2.1]
  exact List.mem_map_of_mem (mem_M10W hl)

theorem labs_map : labs.map memL = M10W := by
  simp only [labs, alphas, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.append_nil, List.map_cons, List.map_nil, memL, memAtL₀, memAtL₁, memAtL₂, memAtL₃,
    memAtL₄]
  rfl

theorem enc_zW (l : Lab) : ((memL l).map enc).getD 1 e10L = enc (zW l) := by
  rw [← heX, getD_map']
  rfl

theorem twin_eq (p q : Lab) :
    twin p q = twinP 5 pilit ((memL p).map enc) ((memL q).map enc) := by
  simp only [twin, twinP, List.all_map, Function.comp_def, pm5, eqPiP5]

theorem prodL_eq (p q : Lab) :
    (prodL p q).map enc = prodLP 5 ((memL p).map enc) ((memL q).map enc) := by
  simp only [prodL, prodLP, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    pm5]

theorem L18_eq (p q : Lab) :
    (L18 p q).map enc = L18P 5 e10L pilit ((memL p).map enc) ((memL q).map enc) := by
  dsimp only [L18, L18P]
  rw [← prodL_eq, enc_zW, List.filter_map]
  refine congrArg (List.map enc) (List.filter_congr fun x _ => ?_)
  simp only [Function.comp_apply, inv18P, inv18With, List.any_map, Function.comp_def, eqPiP5,
    inPiP5, pm5]

theorem normG_eq (p q : Lab) (w : Wr 5) {P2 : List Nat}
    (hP2 : P2 = dbl 5 pilit (prodLP 5 ((memL p).map enc) ((memL q).map enc))) :
    normG p q w = normGP 5 ((memL p).map enc) ((memL q).map enc) P2 (enc w) (enc w⁻¹) := by
  rw [hP2, ← prodL_eq]
  dsimp only [normG, normGP]
  rw [← List.map_append, List.all_map]
  congr 1
  funext g
  simp only [Function.comp_apply, memB, cj5g, any_dbl, List.any_map, Function.comp_def, eqPiP5]

theorem Ms3_eq : Ms3lit = M10W.map (List.map fun m => (enc m, enc (m * allOnes 5), ord4Pi m)) := by
  rw [pinsX.2.1, pins2.2.2.1, List.map_map]
  refine List.map_congr_left fun L _ => ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  rw [Function.comp_apply, ord4P_enc hn5 heX hp5, ← hp5, pm5]
  rfl

theorem excOK_eq (c : Wr 5) : excOK c = excOKP 5 Ms3lit (enc c) (enc c⁻¹) := by
  rw [Ms3_eq, ← labs_map]
  unfold excOK excOKP
  simp only [List.all_map, Function.comp_def, strictB_eq, cj5g, beq_enc hn5]
  rfl

theorem chkCent_k : chkCent () = true := by
  have hc : centOK 5 pilit ([a0 (), b0 ()].map enc) P120lit Vlit ([(1 : Wr 5)].map enc) = true := by
    have h1 : [a0lit, b0lit] = [a0 (), b0 ()].map enc := by
      rw [pins.2.2.1, pins.2.2.2.1]
      rfl
    have h2 : [e10L] = [(1 : Wr 5)].map enc := by
      rw [List.map_singleton, heX]
    rw [← h1, ← h2]
    exact x5_cent
  unfold chkCent
  rw [finAll_iff']
  intro c _
  by_cases hcond : (eqPi (c * a0 ()) (a0 () * c) && eqPi (c * b0 ()) (b0 () * c)) = true
  · rw [hcond, Bool.not_true, Bool.false_or]
    rw [Bool.and_eq_true] at hcond
    have hs : ∀ s ∈ [a0 (), b0 ()], eqPi (s * c) (c * s) = true := by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · rw [eqPi_symm]
        exact hcond.1
      · rw [eqPi_symm]
        exact hcond.2
    obtain ⟨c', hc', hcc⟩ := centOK_sound hn5 hp5 hc c (mem_P120lit c.perm) (mem_Vlit c.vec) hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    exact inPi_of_eqPi_one hcc
  · rw [Bool.not_eq_true] at hcond
    rw [hcond]
    rfl

theorem chkOdd_k : chkOdd () = true := by
  have hC : Mall2lit = (M10W.flatten ++ M10W.flatten.map (· * allOnes 5)).map enc := by
    rw [pinsX.2.2, pins2.2.2.1, ← List.map_flatten, dbl_enc hn5 hp5]
  unfold chkOdd
  rw [List.all_eq_true]
  intro l hl
  rw [finAll_iff']
  intro c _
  by_cases hcm : ((memL l).all fun m => eqPi (c * m) (m * c)) = true
  · rw [hcm, Bool.not_true, Bool.false_or]
    have hcent := List.all_eq_true.1 x5_odd _ (enc_M10 hl)
    rw [hC] at hcent
    have hs : ∀ s ∈ memL l, eqPi (s * c) (c * s) = true := by
      intro s hs
      rw [eqPi_symm]
      exact List.all_eq_true.1 hcm s hs
    obtain ⟨c', hc', hcc⟩ :=
      centOK_sound hn5 hp5 hcent c (mem_P120lit c.perm) (mem_Vlit c.vec) hs
    have hmem := mem_dbl_of_eqPi hc' hcc
    have h15 := List.all_eq_true.1 x5_odd15 (enc c) (by rw [hC]; exact List.mem_map_of_mem hmem)
    rw [pw_enc hn5 heX c 15, inPiP5, inPiP5] at h15
    exact h15
  · rw [Bool.not_eq_true] at hcm
    rw [hcm]
    rfl

theorem chkInv_k : chkInv () = true := by
  unfold chkInv
  rw [List.all_eq_true]
  intro l hl
  have h := List.all_eq_true.1 x5_inv _ (enc_M10 hl)
  rw [enc_zW] at h
  simpa only [List.all_map, Function.comp_def, pm5, inPiP5, eqPiP5] using h

theorem chkZV_k : chkZV () = true := by
  unfold chkZV
  rw [List.all_eq_true]
  intro l hl
  have h := List.all_eq_true.1 x5_zv _ (enc_M10 hl)
  rw [enc_zW] at h
  rw [← inVP5]
  exact h

theorem chkA2_of (p q : Lab) {P2 : List Nat} {W : List ((Nat × Nat) × Nat)}
    (hP2 : P2 = dbl 5 pilit (prodLP 5 ((memL p).map enc) ((memL q).map enc)))
    (h : a2P 5 e10L pilit ((memL p).map enc) ((memL q).map enc) P2 ((L18 p q).map enc) P60lit
      V16lit W = true) : chkA2 p q = true := by
  unfold a2P at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hW, hs⟩ := h
  have hdec : ∀ w ∈ W, ∃ a : Wr 5, wx 5 w = enc a ∧ wxi 5 w = enc a⁻¹ ∧ a ∈ nrm p q := by
    intro w hw
    have hw' := List.all_eq_true.1 hW w hw
    simp only [Bool.and_eq_true] at hw'
    obtain ⟨⟨hok, hz⟩, hn⟩ := hw'
    obtain ⟨σ, x, hσ, hx, h1, h2⟩ := okW_sound hn5 hP60 hV16 hok
    refine ⟨ofVec x * ofPerm σ, h1, h2, ?_⟩
    simp only [nrm, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]
    refine ⟨⟨isAE_of σ x hσ hx, ?_⟩, ?_⟩
    · rw [h1, h2, enc_zW, cj5g, eqPiP5] at hz
      exact hz
    · rw [normG_eq p q _ hP2, ← h1, ← h2]
      exact hn
  dsimp only [chkA2]
  rw [List.all_eq_true] at hs ⊢
  intro v hv
  have hv' := hs v hv
  rw [List.any_map, List.any_eq_true] at hv'
  obtain ⟨x0, hx0, hx0'⟩ := hv'
  simp only [Function.comp_apply, Bool.and_eq_true] at hx0'
  obtain ⟨hv0, hall⟩ := hx0'
  refine List.any_eq_true.2 ⟨x0, hx0, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by rwa [inVP5] at hv0, ?_⟩
  rw [List.all_map, List.all_eq_true] at hall
  rw [List.all_eq_true]
  intro x1 hx1
  have h1 := hall x1 hx1
  simp only [Function.comp_apply, inVP5, Bool.or_eq_true] at h1 ⊢
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · right
    rw [List.any_eq_true] at h1
    obtain ⟨w, hw, hc⟩ := h1
    obtain ⟨a, ha1, ha2, ha3⟩ := hdec w hw
    rw [ha1, ha2, cj5g, eqPiP5] at hc
    exact decide_eq_true ⟨a, ha3, hc⟩

theorem conj_inv_self (w z : Wr 5) (hz : z.perm = 1) : (w * z * w⁻¹)⁻¹ = w * z * w⁻¹ := by
  rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_of_perm_one _ hz, mul_assoc]

theorem chkA3_of (p q : Lab) {w3 : (Nat × Nat) × Nat}
    (h : a3P 5 e10L pilit M10lit ((memL p).map enc) ((memL q).map enc) P60lit P120lit V16lit w3 =
      true) : chkA3 p q = true := by
  unfold a3P at h
  simp only [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hok, hX1⟩, hX2⟩, hX3⟩, hX4⟩, hzp⟩, hQ⟩ := h
  obtain ⟨σ, x, hσ, hx, h1, h2⟩ := okW_sound hn5 hP60 hV16 hok
  rw [enc_zW, h1, h2, cj5g] at hX1 hX2 hX3 hX4 hQ
  rw [enc_zW, ← heX, samePerm_iff hn5] at hzp
  have hzp' : (zW p).perm = 1 := hzp
  have hsinv := conj_inv_self (ofVec x * ofPerm σ) (zW p) hzp'
  refine decide_eq_true ⟨ofVec x * ofPerm σ, Finset.mem_univ _, ?_⟩
  unfold swapOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨isAE_of σ x hσ hx, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hsinv]
    simpa only [List.all_map, List.any_map, Function.comp_def, cj5g, eqPiP5] using hX1
  · rw [hsinv]
    simpa only [List.all_map, List.any_map, Function.comp_def, cj5g, eqPiP5] using hX2
  · simpa only [eqPiP5] using hX3
  · rw [pins2.2.2.1, ← labs_map, List.map_map] at hX4
    simpa only [List.any_map, Function.comp_def, pm5, ord4P_enc hn5 heX hp5, eqPiP5, ord4W_eq]
      using hX4
  · rw [finAll_iff']
    intro c _
    rw [conj_perm_only c _ hzp']
    have hc := List.all_eq_true.1 hQ _ (mem_P120lit c.perm)
    rw [lvl_fst, lvl_snd, cj5g, pm5, eqPiP5] at hc
    exact hc

theorem chkA5_of (p q : Lab) {P2 : List Nat}
    (hP2 : P2 = dbl 5 pilit (prodLP 5 ((memL p).map enc) ((memL q).map enc)))
    (h : a5P 5 e10L pilit a0lit b0lit Ms3lit ((memL p).map enc) ((memL q).map enc) P2
      ((L18 p q).map enc) P120lit Vlit = true) : chkA5 p q = true := by
  rw [pins.2.2.1, pins.2.2.2.1] at h
  unfold a5P at h
  dsimp only [chkA5]
  rw [finAll_iff']
  intro c _
  by_cases hcond : (eqPi (c * c * a0 ()) (a0 () * (c * c)) &&
      eqPi (c * c * b0 ()) (b0 () * (c * c))) = true
  · rw [Bool.and_eq_true] at hcond
    have hg : (strictB (pm 5 (enc (ofPerm c.perm)) (enc (ofPerm c.perm))) fun t2 =>
        !(samePerm 5 (pm 5 t2 (enc (a0 ()))) (pm 5 (enc (a0 ())) t2) &&
          samePerm 5 (pm 5 t2 (enc (b0 ()))) (pm 5 (enc (b0 ())) t2))) = false := by
      rw [strictB_eq, pm5, pm5, pm5, pm5, pm5]
      have ha0 : (c * c * a0 ()).perm = (a0 () * (c * c)).perm := eqPi_perm' hcond.1
      have hb0 : (c * c * b0 ()).perm = (b0 () * (c * c)).perm := eqPi_perm' hcond.2
      have ha : samePerm 5 (enc (ofPerm c.perm * ofPerm c.perm * a0 ()))
          (enc (a0 () * (ofPerm c.perm * ofPerm c.perm))) = true :=
        (samePerm_iff hn5 _ _).2 ha0
      have hb : samePerm 5 (enc (ofPerm c.perm * ofPerm c.perm * b0 ()))
          (enc (b0 () * (ofPerm c.perm * ofPerm c.perm))) = true :=
        (samePerm_iff hn5 _ _).2 hb0
      rw [ha, hb]
      rfl
    have hf := allPF_sound hn5 h c (mem_P120lit c.perm) (mem_Vlit c.vec) hg
    simp only [strictB_eq, pm5, eqPiP5] at hf
    rw [← normG_eq p q c hP2, ← excOK_eq c, List.any_map, List.any_map] at hf
    simpa only [Function.comp_def, inVP5, cj5g, eqPiP5] using hf
  · rw [Bool.not_eq_true] at hcond
    rw [hcond]
    rfl

theorem twin_sound (p q : Lab) (d : PairD) (hA : (memL p).map enc = d.1)
    (hB : (memL q).map enc = d.2.1) (h1 : pairChk d = true) (h5 : a5Chk d = true) :
    chkTwin p q = true := by
  obtain ⟨A0, B0, P2, L, W, w3⟩ := d
  dsimp only at hA hB
  subst hA hB
  simp only [pairChk, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨⟨hP2, hL⟩, ha1⟩, ha2⟩, ha3⟩ := h1
  rw [← L18_eq] at hL
  subst hL
  have hA1 : chkA1 p q = true := by
    simpa only [a1P, chkA1, List.any_map, Function.comp_def, inVP5] using ha1
  unfold chkTwin
  rw [hA1, chkA2_of p q hP2 ha2, chkA3_of p q ha3, chkA5_of p q hP2 h5]
  rfl

theorem PD_ok : ∀ d ∈ PD, pairChk d = true ∧ a5Chk d = true := by
  intro d hd
  simp only [PD, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨x5_pair_0, x5_a5_0⟩, ⟨x5_pair_1, x5_a5_1⟩, ⟨x5_pair_2, x5_a5_2⟩, ⟨x5_pair_3, x5_a5_3⟩,
    ⟨x5_pair_4, x5_a5_4⟩, ⟨x5_pair_5, x5_a5_5⟩, ⟨x5_pair_6, x5_a5_6⟩, ⟨x5_pair_7, x5_a5_7⟩,
    ⟨x5_pair_8, x5_a5_8⟩, ⟨x5_pair_9, x5_a5_9⟩]

theorem chkTwin_k (p q : Lab) (hp : p ∈ labs) (hq : q ∈ labs) (ht : twin p q = true) :
    chkTwin p q = true := by
  rw [twin_eq] at ht
  have hx := List.all_eq_true.1 (List.all_eq_true.1 x5_twins _ (enc_M10 hp)) _ (enc_M10 hq)
  rw [ht, Bool.not_true, Bool.false_or, List.any_eq_true] at hx
  obtain ⟨d, hd, hAB⟩ := hx
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hAB
  obtain ⟨h1, h5⟩ := PD_ok d hd
  exact twin_sound p q d hAB.1 hAB.2 h1 h5

theorem checkX_k : Certificates.AE5X.checkX () = true := by
  unfold checkX
  rw [chkCent_k, chkOdd_k, chkInv_k, chkZV_k, Bool.true_and, Bool.true_and, Bool.true_and,
    Bool.true_and, List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro q hq
  cases ht : twin p q
  · rfl
  · rw [chkTwin_k p q hp hq ht]
    rfl

end CFSG.KD.AE5X

end
