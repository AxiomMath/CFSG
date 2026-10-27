module

public import Certificates.Certificate14961
public import CFSG.RankThree.PartOne.KS.ONPlane
public import CFSG.Sporadic.ONOddCore.PointwiseInner
public import CFSG.Sporadic.ONOddCore.LocalAutOrders

public section

namespace CFSG.RankThree.PartOne.ONPw

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ONOddCore CFSG.RankThree.Native

theorem mem_onM_iff {m : Equiv.Perm (Fin N)} : m ∈ onM ↔ m ∈ Pv ∧ onz * m = m * onz := by
  rw [onM_eq_centralizer_z, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr_right fun _ => eq_comm

theorem alpha_mem_onM {α : MulAut Pv} (hz : α zP = zP) {x : Pv}
    (hx : (x : Equiv.Perm (Fin N)) ∈ onM) : ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onM := by
  rw [mem_onM_iff] at hx ⊢
  refine ⟨(α x).2, ?_⟩
  have h1 : zP * x = x * zP := Subtype.ext hx.2
  have h2 : zP * α x = α x * zP := by
    have := congrArg α h1
    rwa [map_mul, map_mul, hz] at this
  exact congrArg Subtype.val h2

@[expose] noncomputable def restrAut (α : MulAut Pv) (hz : α zP = zP) : MulAut onM where
  toFun m := ⟨((α ⟨m, (mem_onM_iff.1 m.2).1⟩ : Pv) : Equiv.Perm (Fin N)), alpha_mem_onM hz m.2⟩
  invFun m := ⟨((α.symm ⟨m, (mem_onM_iff.1 m.2).1⟩ : Pv) : Equiv.Perm (Fin N)),
    alpha_mem_onM (α.symm_apply_eq.2 hz.symm) m.2⟩
  left_inv m := Subtype.ext (by simp)
  right_inv m := Subtype.ext (by simp)
  map_mul' m n := Subtype.ext (by
    have := map_mul α ⟨m, (mem_onM_iff.1 m.2).1⟩ ⟨n, (mem_onM_iff.1 n.2).1⟩
    exact congrArg (fun u : Pv => (u : Equiv.Perm (Fin N))) this)

theorem restrAut_apply (α : MulAut Pv) (hz : α zP = zP) (m : onM) :
    ((restrAut α hz m : onM) : Equiv.Perm (Fin N)) =
      ((α ⟨m, (mem_onM_iff.1 m.2).1⟩ : Pv) : Equiv.Perm (Fin N)) := rfl

theorem coe_evalPos_hGens (w : List ℕ) :
    ((evalPos hGens w : onM) : Equiv.Perm (Fin N)) = evalPos concreteEnv.hP w := by
  have h := map_evalPos onM.subtype hGens w
  have h2 : hGens.map onM.subtype = concreteEnv.hP := hGens_val
  rw [h2] at h
  exact h

theorem exists_decomp (hlw : liftWords.length = nLifts) (β : MulAut onM) :
    ∃ L : Equiv.Perm (Fin N), L ∈ onL ∧ ∃ q < nLifts,
      (∀ j < 3, ((β (hGen j) : onM) : Equiv.Perm (Fin N)) =
        L * concreteEnv.liftImgP q j * L⁻¹) ∧
      ((β (evalPos hGens yLetters) : onM) : Equiv.Perm (Fin N)) =
        L * concreteEnv.byP q * L⁻¹ := by
  obtain ⟨l, hl⟩ := exists_section
  obtain ⟨⟨x, k, β'⟩, hβ⟩ := (decompose_bijective hl).2 β
  have hk : (k : ℕ) < 12 := k.isLt
  obtain ⟨i, hi, hβ'⟩ := (mem_liftSet_iff hk).1 β'.2
  have he : (recK k).lifts.getD i default ∈ (recK k).lifts := getD_mem hi default
  set e := (recK k).lifts.getD i default with he_def
  have hβm : ∀ m : onM, β m = lM l x * liftAut hk he m * (lM l x)⁻¹ := by
    intro m
    rw [← hβ]
    have : (β' : MulAut onM) m = liftAut hk he m := by rw [hβ']
    simp only [decompose, MulAut.mul_apply, MulAut.conj_apply, this]
  obtain ⟨hlen3, hlet, -⟩ := lift_form hk he
  obtain ⟨q, hq, hqe⟩ : ∃ q < nLifts, liftWords[q]! = e.words := by
    have hmemr : recK k ∈ localCert.records := recK_mem hk
    have hmem : e.words ∈ liftWords := by
      simp only [liftWords, List.mem_map, List.mem_flatMap]
      exact ⟨e, ⟨recK k, hmemr, he⟩, rfl⟩
    obtain ⟨q, hq', hq⟩ := List.mem_iff_getElem.1 hmem
    exact ⟨q, by omega, by rw [getElem!_pos liftWords q hq']; exact hq⟩
  have himg : ∀ j < 3, ((liftImg e j : onM) : Equiv.Perm (Fin N)) =
      concreteEnv.liftImgP q j := by
    intro j hj
    have hjl : j < e.words.length := by omega
    have e1 : e.words.getD j [] = (liftWords[q]!)[j]! := by
      rw [hqe, List.getD_eq_getElem _ _ hjl, getElem!_pos e.words j hjl]
    rw [liftImg, Env.liftImgP, ← e1]
    exact coe_evalPos_hGens _
  have hcoe : ((lM l x : onM) : Equiv.Perm (Fin N)) = ((l x : onL) : Equiv.Perm (Fin N)) := by
    unfold lM
    rfl
  refine ⟨((l x : onL) : Equiv.Perm (Fin N)), (l x).2, q, hq, ?_, ?_⟩
  · intro j hj
    rw [hβm, liftAut_apply, liftHom_gen hk he hj]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [himg j hj, hcoe]
  · have hmap : liftAut hk he (evalPos hGens yLetters) = evalPos (CFSG.Sporadic.ONOddCore.liftImgs e) yLetters := by
      have h1 := map_evalPos (liftAut hk he).toMonoidHom hGens yLetters
      have h2 : hGens.map (liftAut hk he).toMonoidHom = CFSG.Sporadic.ONOddCore.liftImgs e := by
        rw [← hGens_map_liftHom hk he]
        exact List.map_congr_left fun m _ => rfl
      rw [h2] at h1
      exact h1
    have hlist : (CFSG.Sporadic.ONOddCore.liftImgs e).map onM.subtype = concreteEnv.liftImgsP q := by
      apply List.ext_getElem
      · simp [CFSG.Sporadic.ONOddCore.liftImgs, Env.liftImgsP, hlen3]
      · intro j h1 h2
        have hj : j < 3 := by simpa [Env.liftImgsP] using h2
        have hjl : j < e.words.length := by omega
        simp only [CFSG.Sporadic.ONOddCore.liftImgs, Env.liftImgsP, List.getElem_map, List.getElem_range]
        have := himg j hj
        rw [liftImg, List.getD_eq_getElem _ _ hjl] at this
        exact this
    rw [hβm, hmap]
    have h3 := map_evalPos onM.subtype (CFSG.Sporadic.ONOddCore.liftImgs e) yLetters
    rw [hlist] at h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show ((evalPos (CFSG.Sporadic.ONOddCore.liftImgs e) yLetters : onM) : Equiv.Perm (Fin N)) =
      concreteEnv.byP q from h3, hcoe]

theorem hP_mem (j : ℕ) : concreteEnv.hP.getD j 1 ∈ Pv := by
  by_cases hj : j < concreteEnv.hP.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact evalList_mem (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact one_mem _

theorem coe_list_prod_Pv (w : List ℕ) (f : ℕ → Pv) :
    (((w.map f).prod : Pv) : Equiv.Perm (Fin N)) = (w.map fun l => ((f l : Pv) : Equiv.Perm (Fin N))).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]

theorem wF_le : ∀ l ∈ wF, l ≤ 6 := by decide

theorem onPointwiseSeven_holds : ONPointwiseSeven := by
  intro α hfix
  obtain ⟨hF, hlw⟩ := Certificates.certificate14961
  set E := concreteEnv with hE
  let bV : Pv := ⟨E.bP, evalS_mem _⟩
  let x0V : Pv := ⟨E.x0P, evalS_mem _⟩
  let kV : ℕ → Pv := fun j => ⟨E.kP j, evalS_mem _⟩
  let kpV : ℕ → Pv := fun j => bV⁻¹ * kV j * bV
  let xV : Pv := bV⁻¹ * x0V * bV
  let hV : ℕ → Pv := fun j => ⟨E.hP.getD j 1, hP_mem j⟩
  let α' : MulAut Pv := MulAut.conj bV⁻¹ * α * MulAut.conj bV
  have hα'apply : ∀ g : Pv, α' g = bV⁻¹ * α (bV * g * bV⁻¹) * bV := by
    intro g
    simp only [α', MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have hkC : ∀ j < 4, ((kV j : Pv) : Equiv.Perm (Fin N)) ∈ onSevenC 0 := by
    intro j hj
    show E.evalS (kW j) ∈ onSevenC 0
    apply Subgroup.subset_closure
    simp only [Set.mem_ofPred_eq, evalList, List.mem_map, Array.mem_toList_iff]
    refine ⟨kW j, ?_, rfl⟩
    have hsz : (onSevenCentWords[0]!).size = 4 := by decide
    have hj' : j < (onSevenCentWords[0]!).size := by omega
    show (onSevenCentWords[0]!)[j]! ∈ onSevenCentWords[(0 : Fin 5).val]!
    rw [Fin.val_zero, getElem!_pos _ j hj']
    exact Array.getElem_mem hj'
  have hα'k : ∀ j < 4, α' (kpV j) = kpV j := by
    intro j hj
    have h1 : α (kV j) = kV j := hfix (kV j) (hkC j hj)
    rw [hα'apply]
    have : bV * kpV j * bV⁻¹ = kV j := by simp only [kpV]; group
    rw [this, h1]
  have hzpow : zP = kpV 3 ^ 14 := by
    apply Subtype.ext
    have h1 : E.bP * E.zP * E.bP⁻¹ = E.y0P ^ 14 := hF.b_conj
    show E.zP = (E.bP⁻¹ * E.y0P * E.bP) ^ 14
    calc E.zP = E.bP⁻¹ * (E.bP * E.zP * E.bP⁻¹) * E.bP := by group
      _ = E.bP⁻¹ * E.y0P ^ 14 * E.bP := by rw [h1]
      _ = (E.bP⁻¹ * E.y0P * E.bP) ^ 14 := by
        have := conj_pow (a := E.bP⁻¹) (b := E.y0P) (i := 14)
        rw [inv_inv] at this
        exact this.symm
  have hα'z : α' zP = zP := by
    rw [hzpow, map_pow, hα'k 3 (by norm_num)]
  have hyM : E.yP ∈ onM := by
    refine mem_onM_iff.2 ⟨(kpV 3).2, ?_⟩
    have h14 : E.zP = E.yP ^ 14 := congrArg Subtype.val hzpow
    show E.zP * E.yP = E.yP * E.zP
    rw [h14]
    exact (pow_succ E.yP 14).symm.trans (pow_succ' E.yP 14)
  let yM : onM := ⟨E.yP, hyM⟩
  let β : MulAut onM := restrAut α' hα'z
  have hβy : β yM = yM := by
    apply Subtype.ext
    rw [restrAut_apply]
    have : (⟨(yM : Equiv.Perm (Fin N)), (mem_onM_iff.1 yM.2).1⟩ : Pv) = kpV 3 := Subtype.ext rfl
    rw [this, hα'k 3 (by norm_num)]
    rfl
  obtain ⟨L, hL, q, hq, hgen, hy⟩ := exists_decomp hlw β
  have hyM_word : yM = evalPos hGens yLetters :=
    Subtype.ext (hF.y_word.trans (coe_evalPos_hGens yLetters).symm)
  have hcond : L * E.byP q * L⁻¹ = E.yP := by
    have := hy
    rw [← hyM_word, hβy] at this
    exact this.symm
  have hhGen : ∀ j < 3, ((hGen j : onM) : Equiv.Perm (Fin N)) = E.hP.getD j 1 := by
    intro j hj
    have hlen : j < E.hP.length := by
      have : E.hP.length = 3 := onMgens_length
      omega
    rw [hGen_val hj, List.getD_eq_getElem _ _ hlen]
    rfl
  have hα'h : ∀ j < 3, ((α' (hV j) : Pv) : Equiv.Perm (Fin N)) =
      L * E.liftImgP q j * L⁻¹ := by
    intro j hj
    rw [← hgen j hj]
    have h1 : (⟨(hGen j : Equiv.Perm (Fin N)), (mem_onM_iff.1 (hGen j).2).1⟩ : Pv) = hV j :=
      Subtype.ext (hhGen j hj)
    show ((α' (hV j) : Pv) : Equiv.Perm (Fin N)) =
      ((α' ⟨(hGen j : Equiv.Perm (Fin N)), (mem_onM_iff.1 (hGen j).2).1⟩ : Pv) :
        Equiv.Perm (Fin N))
    rw [h1]
  rcases hF.surv q hq L hL hcond with ⟨i, hi7, hinner⟩ | hfilt
  swap
  ·
    exfalso
    apply hfilt
    let Wv : Pv := (wF.map fun l => if l < 3 then hV l else kpV (l - 3)).prod
    have hWcoe : ((Wv : Pv) : Equiv.Perm (Fin N)) =
        evalFP (fun j => E.hP.getD j 1) E.kpP wF := by
      rw [coe_list_prod_Pv]
      unfold evalFP
      refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
      by_cases hl : l < 3
      · simp only [hl, ↓reduceIte]
        try rfl
      · simp only [hl, ↓reduceIte]
        try rfl
    have hWimg : ((α' Wv : Pv) : Equiv.Perm (Fin N)) =
        evalFP (fun j => L * E.liftImgP q j * L⁻¹) E.kpP wF := by
      have h1 : α' Wv = (wF.map fun l => α' (if l < 3 then hV l else kpV (l - 3))).prod := by
        simp only [Wv]
        rw [map_list_prod, List.map_map]
        rfl
      rw [h1, coe_list_prod_Pv (f := fun l => α' (if l < 3 then hV l else kpV (l - 3)))]
      unfold evalFP
      refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
      have hl6 := wF_le l hl
      by_cases hl3 : l < 3
      · simp only [hl3, ↓reduceIte]
        exact hα'h l hl3
      · simp only [hl3, ↓reduceIte]
        rw [hα'k (l - 3) (by omega)]
        try rfl
    have hW8 : Wv ^ 8 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hWcoe]
      exact hF.filt_orig
    have h8 : (α' Wv) ^ 8 = 1 := by rw [← map_pow, hW8, map_one]
    have := congrArg Subtype.val h8
    rw [Subgroup.coe_pow, hWimg] at this
    exact this
  ·
    have hβconj : ∀ m : onM, ((β m : onM) : Equiv.Perm (Fin N)) =
        E.xP ^ i * (m : Equiv.Perm (Fin N)) * (E.xP ^ i)⁻¹ := by
      have hf : (onM.subtype.comp β.toMonoidHom) =
          (MulAut.conj (E.xP ^ i)).toMonoidHom.comp onM.subtype := by
        refine MonoidHom.eq_of_eqOn_dense hGens_closure_top ?_
        intro g hg
        obtain ⟨j, hj, rfl⟩ := mem_hGens_iff.1 (show g ∈ hGens from hg)
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
          MulAut.conj_apply]
        rw [hgen j hj, hinner j hj, hhGen j hj]
      intro m
      have := DFunLike.congr_fun hf m
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
        MulAut.conj_apply] using this
    let γ : MulAut Pv := MulAut.conj (xV ^ i)⁻¹ * α'
    have hxcoe : ((xV ^ i : Pv) : Equiv.Perm (Fin N)) = E.xP ^ i := by
      rw [Subgroup.coe_pow]
      rfl
    have hγM : ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → γ m = m := by
      intro m hm
      have h1 : ((α' m : Pv) : Equiv.Perm (Fin N)) = E.xP ^ i * (m : Equiv.Perm (Fin N)) * (E.xP ^ i)⁻¹ := by
        have := hβconj ⟨m, hm⟩
        rw [restrAut_apply] at this
        exact this
      have h2 : α' m = xV ^ i * m * (xV ^ i)⁻¹ := by
        apply Subtype.ext
        rw [h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxcoe]
      simp only [γ, MulAut.mul_apply, MulAut.conj_apply, inv_inv, h2]
      group
    have hγk : ∀ j < 4, γ (kpV j) = kpV j := by
      intro j hj
      have hc : xV * kpV j = kpV j * xV := Subtype.ext (hF.x_comm j hj)
      have hc' : xV ^ i * kpV j = kpV j * xV ^ i := (Commute.pow_left hc i)
      simp only [γ, MulAut.mul_apply, MulAut.conj_apply, inv_inv, hα'k j hj]
      rw [mul_assoc, ← hc']
      group
    rcases pointwise_M_cases γ hγM with hγ1 | hγz
    ·
      have hα'eq : α' = MulAut.conj (xV ^ i) := by
        have : MulAut.conj (xV ^ i)⁻¹ * α' = 1 := hγ1
        rw [map_inv] at this
        exact (inv_mul_eq_one.1 this).symm
      have hαeq : α = MulAut.conj (x0V ^ i) := by
        have h1 : α = MulAut.conj bV * α' * MulAut.conj bV⁻¹ := by
          simp only [α', map_inv]
          group
        rw [h1, hα'eq, ← map_mul, ← map_mul]
        refine congrArg MulAut.conj ?_
        have : xV ^ i = bV⁻¹ * x0V ^ i * bV := by
          have := conj_pow (a := bV⁻¹) (b := x0V) (i := i)
          rw [inv_inv] at this
          simpa [xV] using this
        rw [this]
        group
      rw [hαeq, ← map_pow, ← pow_mul, mul_comm, pow_mul]
      have hx7 : x0V ^ 7 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        exact hF.x0_pow
      rw [hx7, one_pow, map_one]
    ·
      exfalso
      obtain ⟨j, hj, hnc⟩ := hF.z_ncomm
      apply hnc
      have h1 := hγk j hj
      rw [hγz, MulAut.conj_apply] at h1
      have h2 : zP * kpV j = kpV j * zP := by
        have := congrArg (fun g => g * zP) h1
        simpa [mul_assoc] using this
      exact congrArg Subtype.val h2

end CFSG.RankThree.PartOne.ONPw
