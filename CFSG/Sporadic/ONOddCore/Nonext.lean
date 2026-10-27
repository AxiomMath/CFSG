module

public import CFSG.Sporadic.ONOddCore.NonextTools
public import CFSG.Sporadic.ONOddCore.PointwiseInner

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem prep_conjArr_inv {y yi x : Array ℕ} {Y X : Equiv.Perm (Fin N)} (hy : PRep N y Y)
    (hyi : PRep N yi Y⁻¹) (hx : PRep N x X) : PRep N (conjArr yi y x) (Y⁻¹ * X * Y) := by
  have := prep_conjArr hyi (by rwa [inv_inv]) hx
  rwa [inv_inv] at this

@[expose] def toP
    (m : onM) : Pv := ⟨m, onM_le m.2⟩

theorem coe_toP
    (m : onM) : ((toP m : Pv) : Equiv.Perm (Fin N)) = m := rfl

theorem exists_betaAut
    {r : ℕ} (hr : r < 16) :
    ∃ k, ∃ hk : k < 12, ∃ he : flatLifts.getD r default ∈ (recK k).lifts,
      ⇑(liftAut hk he) = betaFun r := by
  obtain ⟨k, hk, he⟩ := flatLifts_mem hr
  exact ⟨k, hk, he, liftAut_eq_liftFun hk he⟩

theorem betaFun_inner
    {r : ℕ} (hr : r ∈ innerIdx) (m : onM) :
    betaFun r m = bElem r * m * (bElem r)⁻¹ := by
  obtain ⟨hy, hyr⟩ := innerRec_index hr
  have hr16 : r < 16 := by
    simp only [innerIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  obtain ⟨k, hk, he, hβ⟩ := exists_betaAut hr16
  have hok := nonext_facts.2.2.2.2 _ hy
  simp only [innerOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨hw, hinv⟩, hgen⟩ := hok
  rw [hyr] at hgen
  have hb := prep_posArr_h (lettersOK_iff.1 hw)
  have hbi := prep_inv_pinvCand hb hinv
  have hext : (liftAut hk he).toMonoidHom = (MulAut.conj (bElem r)).toMonoidHom := by
    apply hom_ext_hGens
    intro i hi
    apply Subtype.ext
    have h1 := eq_of_peq (prep_conjArr hb hbi (prep_hA hi)) (prep_lift_gen hk he hi)
      (hgen i hi)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact h1.symm
  rw [← hβ]
  have := DFunLike.congr_fun hext m
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem fix_D_of_gens
    (φ : MulAut onM) (h : ∀ i (hi : i < 4), φ (ceM hi) = ceM hi) :
    ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → φ d = d := by
  intro d hd
  let F : Subgroup (Equiv.Perm (Fin N)) :=
    (MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id onM)).map onM.subtype
  have hDF : onD ≤ F := by
    rw [onD, onD0, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (show g ∈ onDgens from hg)
    have hi4 : i < 4 := by rwa [onDgens_length] at hi
    refine Subgroup.mem_map.2 ⟨ceM hi4, h i hi4, ?_⟩
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl
  obtain ⟨d', hd', hdd⟩ := Subgroup.mem_map.1 (hDF hd)
  have hd'd : d' = d := Subtype.ext hdd
  subst hd'd
  exact hd'

@[expose] def vConj
    (ε : Bool) (m : onM) : onM := if ε then vM * m * vM⁻¹ else m

theorem cmc_ceM
    {i : ℕ} (hi : i < 4) : cmc (ceM hi) = toP (eM hi) := by
  apply Subtype.ext
  show onc * (onc⁻¹ * onDgens[i]'(by rw [onDgens_length]; exact hi) * onc) * onc⁻¹ =
    onDgens[i]'(by rw [onDgens_length]; exact hi)
  group

theorem posArr_six_zero {A B : Array (Array ℕ)} {GA GB : List (Equiv.Perm (Fin N))}
    (hA : A.size = 3) (hB : B.size = 3) (hGA : GA.length = 3) (hGB : GB.length = 3)
    (h1 : ∀ i < 3, PRep N A[i]! (GA.getD i 1)) (h2 : ∀ i < 3, PRep N B[i]! (GB.getD i 1))
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) (h : evalPos (GA ++ GB) w = 1) :
    (posArr nPts (A ++ B) w)[0]! = 0 := by
  have hp := prep_posArr_six hA hB hGA hGB h1 h2 hw
  rw [h] at hp
  rw [hp.apply (by norm_num)]
  rfl

theorem not_extend
    {r : ℕ} (hr : r ∈ exclIdx) (α : MulAut Pv)
    (hα : ∀ m : onM, ((α (toP m) : Pv) : Equiv.Perm (Fin N)) = (betaFun r m : Equiv.Perm (Fin N))) :
    False := by
  obtain ⟨hx, hxr⟩ := exclRec_index hr
  have hr16 : r < 16 := by
    simp only [exclIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  have hok := nonext_facts.2.2.2.1 _ hx
  simp only [exclOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwd, hwu⟩, hs⟩, hdinv⟩, huinv⟩, hvinv⟩, ht⟩, hD⟩, hrel⟩ := hok
  rw [hxr] at ht hD hrel
  rw [flatLifts_length] at hs
  obtain ⟨k, hk, he, hβ⟩ := exists_betaAut hr16
  obtain ⟨k', hk', he', -⟩ := exists_betaAut hs
  set β := liftAut hk he
  set β' := liftAut hk' he'
  set x := exclRec r
  have hd := prep_posArr_h (lettersOK_iff.1 hwd)
  have hdi := prep_inv_pinvCand hd hdinv
  have hu := prep_posArr_h (lettersOK_iff.1 hwu)
  have hui := prep_inv_pinvCand hu huinv
  have hbv := prep_lift_word hk' he' aux_facts.2.2.1
  rw [evalPos_vWord] at hbv
  have hbvi := prep_inv_pinvCand hbv hvinv
  set d : onM := evalPos hGens x.normWord
  set u : onM := evalPos hGens x.conjWord
  set δ : MulAut Pv := MulAut.conj (toP d)⁻¹ * α with hδdef
  have hδM : ∀ m : onM, ((δ (toP m) : Pv) : Equiv.Perm (Fin N)) =
      (d : Equiv.Perm (Fin N))⁻¹ * (β m : Equiv.Perm (Fin N)) * d := by
    intro m
    rw [hδdef, MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hα m, ← hβ]
    rfl
  have hδt : δ tPv = tPv := by
    have h1 := eq_of_peq (prep_conjArr hd hdi prep_t) (prep_lift_word hk he aux_facts.1) ht
    rw [evalPos_tWord] at h1
    apply Subtype.ext
    have h2 := hδM tM
    rw [← h1] at h2
    rw [show tPv = toP tM from rfl, h2]
    show (d : Equiv.Perm (Fin N))⁻¹ * (d * ont * (d : Equiv.Perm (Fin N))⁻¹) * d = ont
    group
  set η := transportAut δ hδt with hηdef
  set ηr : MulAut onM := MulAut.conj u * β' with hηrdef
  have hgen : ∀ i (hi : i < 4), (ηr⁻¹ * η) (ceM hi) = ceM hi := by
    intro i hi
    rw [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    have h1 := eq_of_peq
      (prep_conjArr hu hui (prep_lift_word hk' he' (aux_facts.2.2.2.2 i hi).2.1))
      (prep_conjArr_inv prep_onc prep_onc_inv
        (prep_conjArr_inv hd hdi (prep_lift_word hk he (aux_facts.2.2.2.2 i hi).1))) (hD i hi)
    rw [evalPos_dcWord, evalPos_dWord] at h1
    rw [hηdef, transportAut_apply, cmc_ceM, hδM, hηrdef, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact h1.symm
  have hcases : ηr⁻¹ * η = 1 ∨ ηr⁻¹ * η = MulAut.conj vM := by
    have hmem : ηr⁻¹ * η ∈
        {β : MulAut onM | ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = d} :=
      fix_D_of_gens _ hgen
    rw [pointwise_eq] at hmem
    simpa using hmem
  have hsplitη : η = ηr * (ηr⁻¹ * η) := by group
  obtain ⟨ε, hε⟩ : ∃ ε : Bool, ∀ m, η m = ηr (vConj ε m) := by
    rcases hcases with h | h
    · refine ⟨false, fun m => ?_⟩
      rw [hsplitη, h, mul_one]
      rfl
    · refine ⟨true, fun m => ?_⟩
      rw [hsplitη, h]
      rfl
  have hδh : ∀ i < 3, PRep N ((liftArrs (wordArrs Data.MWords) (flatLifts.getD r default)).map
      (conjArr (pinvCand nPts (posArr nPts (wordArrs Data.MWords) x.normWord))
        (posArr nPts (wordArrs Data.MWords) x.normWord)))[i]!
      ((δ (toP (hGen i)) : Pv) : Equiv.Perm (Fin N)) := by
    intro i hi
    rw [getElem!_map_arr (by rw [liftArrs_size hk he]; exact hi), hδM]
    exact prep_conjArr_inv hd hdi (prep_lift_gen hk he hi)
  have hδch : ∀ i < 3, PRep N ((liftArrs (wordArrs Data.MWords)
      (flatLifts.getD x.second default)).map fun a =>
        cConj (conjArr (posArr nPts (wordArrs Data.MWords) x.conjWord)
          (pinvCand nPts (posArr nPts (wordArrs Data.MWords) x.conjWord))
          (if ε then conjArr (posArr nPts (liftArrs (wordArrs Data.MWords)
            (flatLifts.getD x.second default)) nonextWords.vWord)
            (pinvCand nPts (posArr nPts (liftArrs (wordArrs Data.MWords)
              (flatLifts.getD x.second default)) nonextWords.vWord)) a else a)))[i]!
      ((δ (cmc (hGen i)) : Pv) : Equiv.Perm (Fin N)) := by
    intro i hi
    rw [getElem!_map_arr (by rw [liftArrs_size hk' he']; exact hi), ← cmc_transportFun δ hδt]
    show PRep N _ (onc * (η (hGen i) : Equiv.Perm (Fin N)) * onc⁻¹)
    refine prep_cConj ?_
    rw [hε, hηrdef, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine prep_conjArr hu hui ?_
    cases ε
    · rw [ite_eq_right Bool.false_ne_true]
      exact prep_lift_gen hk' he' hi
    · rw [ite_eq_left rfl]
      show PRep N _ ((β' (vM * hGen i * vM⁻¹) : onM) : Equiv.Perm (Fin N))
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact prep_conjArr hbv hbvi (prep_lift_gen hk' he' hi)
  have hrel1 : evalPos [toP (hGen 0), toP (hGen 1), toP (hGen 2), cmc (hGen 0), cmc (hGen 1),
      cmc (hGen 2)] nonextCert.relationWord = 1 := by
    apply Subtype.ext
    rw [← Pv.subtype_apply, map_evalPos]
    exact evalPos_relation
  have hrel2 := map_evalPos δ.toMonoidHom [toP (hGen 0), toP (hGen 1), toP (hGen 2),
    cmc (hGen 0), cmc (hGen 1), cmc (hGen 2)] nonextCert.relationWord
  rw [hrel1, map_one] at hrel2
  apply hrel ε (by cases ε <;> simp)
  rw [deltaImgs]
  refine posArr_six_zero (by rw [Array.size_map, liftArrs_size hk he])
    (by rw [Array.size_map, liftArrs_size hk' he']) rfl rfl
    (GA := [((δ (toP (hGen 0)) : Pv) : Equiv.Perm (Fin N)), (δ (toP (hGen 1)) : Pv),
      (δ (toP (hGen 2)) : Pv)])
    (GB := [((δ (cmc (hGen 0)) : Pv) : Equiv.Perm (Fin N)), (δ (cmc (hGen 1)) : Pv),
      (δ (cmc (hGen 2)) : Pv)])
    (fun i hi => by interval_cases i <;> exact hδh _ (by norm_num))
    (fun i hi => by interval_cases i <;> exact hδch _ (by norm_num))
    (lettersOK_iff.1 nonext_facts.2.1) ?_
  have e := congrArg Pv.subtype hrel2.symm
  rw [map_one, map_evalPos] at e
  exact e

theorem ctuc_on_eight_normalized_local_lifts_do_not_extend :
    (∀ r ∈ innerIdx, ∀ m : onM, betaFun r m = bElem r * m * (bElem r)⁻¹) ∧
      ∀ r ∈ exclIdx, ∀ α : MulAut Pv,
        (onM.subgroupOf Pv).map α.toMonoidHom = onM.subgroupOf Pv →
          ¬ ∀ m : onM, ((α ⟨m, onM_le m.2⟩ : Pv) : Equiv.Perm (Fin N)) =
            (betaFun r m : Equiv.Perm (Fin N)) :=
  ⟨fun _ hr m => betaFun_inner hr m, fun _ hr α _ h => not_extend hr α h⟩

end CFSG.Sporadic.ONOddCore
