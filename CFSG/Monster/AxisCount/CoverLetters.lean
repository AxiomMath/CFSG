module

public import CFSG.Monster.AxisCount.FrameStab
public import CFSG.Monster.AxisCount.DenseWord

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.B.Rep4371

theorem native_sumToC : Native.Cover.sumToC = sumTo := by
  funext f n
  induction n with
  | zero => rfl
  | succ n ih => rw [Native.Cover.sumToC, sumTo, ih]

theorem native_ellC : Native.Cover.ellC = ellN := rfl

theorem native_ginvListC : Native.Cover.ginvListC = ginvList := rfl

theorem native_xiAct : Native.Cover.xiAct = xiN := rfl

theorem native_permAct : Native.Cover.permAct = permN := rfl

theorem native_signAct : Native.Cover.signAct = signN := rfl

theorem native_actGo (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, Native.Cover.actGo rows v n acc = actGo rows v n acc
  | 0, _ => rfl
  | n + 1, acc => by rw [Native.Cover.actGo, actGo, native_actGo rows v n]

theorem native_actRows (rows : Array ℕ) (v : ℕ) : Native.Cover.actRows rows v = actRows rows v :=
  native_actGo rows v 24 0

theorem pairBit_eq (w : ℕ → ℤ) (k : ℕ) :
    Native.Cover.pairBit w k = decide ((sumTo (fun i => w i * ellN k i) 24 / 8) % 2 = 1) := by
  unfold Native.Cover.pairBit
  rw [native_sumToC, native_ellC]
  rfl

theorem popc_ginv_gram (j l : ℕ) (hj : j < 24) (hl : l < 24) :
    (popc 24 (ginvRow l &&& gramRow j) : ZMod 2) = if j = l then 1 else 0 := by
  have h := bvec_dotProduct_ginv ⟨j, hj⟩ ⟨l, hl⟩
  rw [bvec_dotProduct, Nat.and_comm] at h
  rw [h]
  simp only [Fin.mk.injEq]

theorem popc_xor_and (a b c : ℕ) :
    (popc 24 ((a ^^^ b) &&& c) : ZMod 2) = (popc 24 (a &&& c) : ZMod 2) + popc 24 (b &&& c) := by
  rw [← bvec_dotProduct, ← bvec_dotProduct, ← bvec_dotProduct, bvec_xor, add_dotProduct]

theorem solveGo_dot (w : ℕ → ℤ) (k : ℕ) (hk : k < 24) :
    ∀ n acc, n ≤ 24 → (popc 24 (Native.Cover.solveGo w n acc &&& gramRow k) : ZMod 2) =
      (popc 24 (acc &&& gramRow k) : ZMod 2) +
        ∑ i ∈ Finset.range n, if Native.Cover.pairBit w i then (if i = k then 1 else 0) else 0
  | 0, acc, _ => by
    show (popc 24 (acc &&& gramRow k) : ZMod 2) = _
    rw [Finset.range_zero, Finset.sum_empty, add_zero]
  | n + 1, acc, hn => by
    rw [Native.Cover.solveGo, solveGo_dot w k hk n _ (by omega), Finset.sum_range_succ]
    by_cases hb : Native.Cover.pairBit w n = true
    · rw [ite_eq_left hb, ite_eq_left hb, native_ginvListC, popc_xor_and]
      have : ginvList.getD n 0 = ginvRow n := rfl
      rw [this, popc_ginv_gram k n hk (by omega)]
      by_cases hnk : n = k
      · subst hnk
        simp only [ite_true]
        ring
      · have : ¬ k = n := fun h => hnk h.symm
        simp only [this, hnk, ite_false]
        ring
    · rw [ite_eq_right hb, ite_eq_right hb]
      simp only [add_zero]

theorem popc_zero_and (c : ℕ) : (popc 24 (0 &&& c) : ZMod 2) = 0 := by
  rw [← bvec_dotProduct, bvec_zero, zero_dotProduct]

theorem popc_solveGo (w : ℕ → ℤ) (k : ℕ) (hk : k < 24) :
    (popc 24 (Native.Cover.clsCoord w &&& gramRow k) : ZMod 2) =
      if Native.Cover.pairBit w k then 1 else 0 := by
  rw [Native.Cover.clsCoord, solveGo_dot w k hk 24 0 le_rfl, popc_zero_and, zero_add,
    Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [hik]
  · intro hk'
    exact absurd (Finset.mem_range.2 hk) hk'

theorem rowCheck_clsCoord (w : ℕ → ℤ) : rowCheck w (Native.Cover.clsCoord w) = true := by
  rw [rowCheck, allTo_iff]
  intro k hk
  rw [beq_iff_eq]
  have h1 := popc_solveGo w k hk
  have h2 : popc 24 (Native.Cover.clsCoord w &&& gramRow k) % 2 =
      if Native.Cover.pairBit w k then 1 else 0 := by
    have := (ZMod.natCast_eq_natCast_iff' (popc 24 (Native.Cover.clsCoord w &&& gramRow k))
      (if Native.Cover.pairBit w k then 1 else 0) 2).1 (by rw [h1]; split_ifs <;> simp)
    rw [this]
    split_ifs <;> rfl
  rw [h2, pairBit_eq]
  have h3 := Int.emod_two_eq_zero_or_one (sumTo (fun i => w i * ellN k i) 24 / 8)
  rcases h3 with h3 | h3
  · simp [h3]
  · simp [h3]

theorem cls_eq_dec_clsCoord {w : ℕ → ℤ} (hw : (fun i : Fin 24 => w i) ∈ codeLattice C) :
    cls (fun i : Fin 24 => w i) hw = dec (Native.Cover.clsCoord w) :=
  cls_eq_dec_of_rowCheck hw (rowCheck_clsCoord w)

theorem cls_eq_dec_clsCoord' {w : ℕ → ℤ} {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (e : u = fun i : Fin 24 => w i) : cls u hu = dec (Native.Cover.clsCoord w) := by
  subst e
  exact cls_eq_dec_clsCoord hu

theorem signVec_bvec (m : ℕ) (U : ℕ → ℤ) :
    signVec (bvec 24 m) (fun i : Fin 24 => U i) = fun i : Fin 24 => signN m U i := by
  funext i
  rw [signVec_apply, bvec_apply, signN]
  split_ifs
  · rw [bitLift_one]
    ring
  · rw [show bitLift (0 : ZMod 2) = 0 from rfl]
    ring

theorem l2Rows_eq (g : Native.Gen) : g.l2Rows = Native.Cover.rowsOfAct g.latAct := by
  cases g <;> rfl

theorem l2Rows_get (g : Native.Gen) (i : Fin 24) :
    g.l2Rows[(i : ℕ)]! = Native.Cover.clsCoord (g.latAct (Native.Cover.ellC i)) := by
  rw [Native.getElem!_eq_getD_gen, l2Rows_eq]
  unfold Native.Cover.rowsOfAct
  exact Native.getD_ofFn _ _ i.2 _

theorem Native.Gen.ne_tau_of_isVis {g : Native.Gen} (hg : g.isVis = true) : ¬ g = .tau := by
  rintro rfl
  exact absurd hg (by decide)

theorem Native.Gen.toLin_eq_theta {g : Native.Gen} (hg : ¬ g = .tau) :
    g.toLin = thetaEquiv g.pair := by
  cases g <;> first | rfl | exact absurd rfl hg

theorem permInv_getD {arr : Array ℕ} (h : Native.permValid arr = true) {p : Equiv.Perm (Fin 24)}
    (hp : RepPerm p arr) (j : Fin 24) :
    (Native.permInv arr).toList.getD j 0 = ((p⁻¹ j : Fin 24) : ℕ) := by
  simp only [Native.permValid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h2⟩, h3⟩, -⟩, -⟩ := h
  have hlt : (Native.permInv arr)[(j : ℕ)]! < 24 := by
    have := List.all_eq_true.1 h2 j (List.mem_range.2 j.2)
    simpa using this
  have hr : arr[(Native.permInv arr)[(j : ℕ)]!]! = j := by
    have := List.all_eq_true.1 h3 j (List.mem_range.2 j.2)
    simpa using this
  have e : (Native.permInv arr).toList.getD j 0 = (Native.permInv arr)[(j : ℕ)]! := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e]
  have hpk : p ⟨(Native.permInv arr)[(j : ℕ)]!, hlt⟩ = j := by
    apply Fin.ext
    rw [hp]
    exact hr
  have : p⁻¹ j = ⟨(Native.permInv arr)[(j : ℕ)]!, hlt⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hpk.symm
  rw [this]

theorem modTwoEnd_pair_ellCls (g : Native.Gen) (hg : g.isVis = true) (i : Fin 24) :
    modTwoEnd g.pair.1.2 (ellCls i) = dec g.l2Rows[(i : ℕ)]! := by
  rw [l2Rows_get, ellCls_eq]
  cases g with
  | rho q =>
    show modTwoEnd 1 _ = _
    rw [modTwoEnd_one]
    exact cls_eq_dec_clsCoord' _ rfl
  | perm arr =>
    have hv : Native.permValid arr = true := hg
    obtain ⟨p, hp⟩ := permValid_spec hv
    have hpair : (Native.Gen.perm arr).pair = permPairOf p := by
      show permPairOf (permOf arr) = _
      rw [permOf_eq p hp]
    rw [hpair]
    show modTwoEnd (PO p) _ = _
    rw [modTwoEnd_PO_cls p (ellN_mem i)]
    refine cls_eq_dec_clsCoord' _ ?_
    funext j
    show ellN i ((p : Equiv.Perm (Fin 24))⁻¹ j) = Native.Cover.permAct _ (Native.Cover.ellC i) j
    rw [native_permAct, native_ellC, permN, permInv_getD hv hp j]
  | sign a =>
    show modTwoEnd (gO (toC a)) _ = _
    rw [modTwoEnd_gO_cls (toC a) (ellN_mem i)]
    refine cls_eq_dec_clsCoord' _ ?_
    show signVec _ _ =
      fun j : Fin 24 => Native.Cover.signAct (Native.wordN a) (Native.Cover.ellC i) j
    rw [coe_toC, native_signAct, native_ellC, ← signVec_bvec]
    rfl
  | xi =>
    show modTwoEnd xiO _ = _
    have hU := ellN_mem i
    rw [modTwoEnd_xiO_cls_of hU (Xi.xiInt_mem hU) (Xi.toQ_mem_latticeQ_vecMul hU)]
    refine cls_eq_dec_clsCoord' _ ?_
    show Xi.xiInt _ = fun j : Fin 24 => Native.Cover.xiAct (Native.Cover.ellC i) j
    rw [xiInt_eq_xiN, native_xiAct, native_ellC]
  | tau => exact absurd hg (by decide)

theorem psiVis_toLin_smul_ellCls (g : Native.Gen) (hg : g.isVis = true) (i : Fin 24) :
    psiVis ⟨g.toLin, Native.Gen.toLin_mem_Gvis g (Native.Gen.ne_tau_of_isVis hg)⟩ • ellCls i =
      dec g.l2Rows[(i : ℕ)]! := by
  have e : (⟨g.toLin, Native.Gen.toLin_mem_Gvis g (Native.Gen.ne_tau_of_isVis hg)⟩ : Gvis) =
      ⟨thetaEquiv g.pair, thetaEquiv_mem_Gvis g.pair⟩ :=
    Subtype.ext (Native.Gen.toLin_eq_theta (Native.Gen.ne_tau_of_isVis hg))
  rw [e, psiVis_smul_thetaEquiv]
  exact modTwoEnd_pair_ellCls g hg i

theorem smul_dec_of_ellCls {T : GLV} {rows : Array ℕ}
    (h : ∀ i : Fin 24, T • ellCls i = dec rows[(i : ℕ)]!) (v : ℕ) :
    T • dec v = dec (actRows rows v) := by
  have e : T • dec v = (T : Module.End (ZMod 2) L2) (dec v) := rfl
  rw [e, dec_actRows, dec, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact congrArg _ (h i)

theorem psiVis_toLin_smul_dec (g : Native.Gen) (hg : g.isVis = true) (v : ℕ) :
    psiVis ⟨g.toLin, Native.Gen.toLin_mem_Gvis g (Native.Gen.ne_tau_of_isVis hg)⟩ • dec v =
      dec (Native.Cover.actRows g.l2Rows v) := by
  rw [native_actRows]
  exact smul_dec_of_ellCls (psiVis_toLin_smul_ellCls g hg) v

theorem l2Word_nil (v : ℕ) : Native.Cover.l2Word [] v = v := rfl

theorem l2Word_cons (g : Native.Gen) (w : List Native.Gen) (v : ℕ) :
    Native.Cover.l2Word (g :: w) v = Native.Cover.l2Word w (Native.Cover.actRows g.l2Rows v) := rfl

theorem wordLin_mem_Gvis_of_isVis (w : List Native.Gen) (hw : ∀ g ∈ w, g.isVis = true) :
    wordLin w ∈ Gvis :=
  wordLin_mem_Gvis w fun g hg => Native.Gen.ne_tau_of_isVis (hw g hg)

theorem psiVis_wordLin_smul_dec :
    ∀ (w : List Native.Gen) (hw : ∀ g ∈ w, g.isVis = true) (v : ℕ),
      psiVis ⟨wordLin w, wordLin_mem_Gvis_of_isVis w hw⟩ • dec v =
        dec (Native.Cover.l2Word w v)
  | [], _, v => by
    have : (⟨wordLin [], wordLin_mem_Gvis_of_isVis [] (by simp)⟩ : Gvis) = 1 := rfl
    rw [this, map_one, one_smul]
    rfl
  | g :: w, hw, v => by
    have hg : g.isVis = true := hw g List.mem_cons_self
    have hw' : ∀ g' ∈ w, g'.isVis = true := fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')
    have e : (⟨wordLin (g :: w), wordLin_mem_Gvis_of_isVis _ hw⟩ : Gvis) =
        ⟨wordLin w, wordLin_mem_Gvis_of_isVis w hw'⟩ *
          ⟨g.toLin, Native.Gen.toLin_mem_Gvis g (Native.Gen.ne_tau_of_isVis hg)⟩ := rfl
    rw [e, map_mul, mul_smul, psiVis_toLin_smul_dec g hg, psiVis_wordLin_smul_dec w hw',
      l2Word_cons]

theorem dec_two_pow (i : Fin 24) : dec (2 ^ (i : ℕ)) = ellCls i := by
  rw [dec, bvec_two_pow]
  simp [Pi.single_apply]

theorem wordRows_get (w : List Native.Gen) (i : Fin 24) :
    (Native.Cover.wordRows w)[(i : ℕ)]! = Native.Cover.l2Word w (2 ^ (i : ℕ)) := by
  rw [Native.getElem!_eq_getD_gen]
  unfold Native.Cover.wordRows
  rw [Native.getD_ofFn _ _ i.2 _, Nat.one_shiftLeft]
  rfl

theorem psiVis_wordLin_smul_dec_wordRows (w : List Native.Gen) (hw : ∀ g ∈ w, g.isVis = true)
    (v : ℕ) :
    psiVis ⟨wordLin w, wordLin_mem_Gvis_of_isVis w hw⟩ • dec v =
      dec (Native.Cover.actRows (Native.Cover.wordRows w) v) := by
  rw [native_actRows]
  refine smul_dec_of_ellCls (fun i => ?_) v
  rw [wordRows_get, ← dec_two_pow, psiVis_wordLin_smul_dec w hw]

end CFSG.Monster.AxisCount
