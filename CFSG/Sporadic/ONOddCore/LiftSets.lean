module

public import CFSG.Sporadic.ONOddCore.LiftGraph
public import CFSG.Sporadic.ONOddCore.LiftCount

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native

theorem closure_liftPair_map
    {e : LiftEntry} :
    (Subgroup.closure (liftPair e '' {j | j < 3})).map (Pv.prod Pv).subtype =
      Subgroup.closure ((fun j => ((hGen j : Equiv.Perm (Fin N)), (liftImg e j :
        Equiv.Perm (Fin N)))) '' {j | j < 3}) := by
  rw [MonoidHom.map_closure, ← Set.image_comp]
  rfl

theorem fst_image_lift
    (e : LiftEntry) :
    Prod.fst '' ((fun j => ((hGen j : Equiv.Perm (Fin N)), (liftImg e j :
      Equiv.Perm (Fin N)))) '' {j | j < 3}) = {g | g ∈ onMgens} := by
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_onMgens_iff]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩

theorem exists_liftHom
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    ∃ φ : onM →* onM, ∀ i < 3, φ (hGen i) = liftImg e i :=
  exists_liftHom_res hk he

@[expose] def liftHom
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    onM →* onM :=
  Classical.choose (exists_liftHom hk he)

theorem liftHom_gen
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) {i : ℕ}
    (hi : i < 3) : liftHom hk he (hGen i) = liftImg e i :=
  Classical.choose_spec (exists_liftHom hk he) i hi

theorem hGens_map_liftHom
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    hGens.map (liftHom hk he) = liftImgs e := by
  obtain ⟨hl, -, -⟩ := lift_form hk he
  obtain ⟨w0, w1, w2, hw⟩ := List.length_eq_three.1 hl
  have h0 := liftHom_gen hk he (i := 0) (by norm_num)
  have h1 := liftHom_gen hk he (i := 1) (by norm_num)
  have h2 := liftHom_gen hk he (i := 2) (by norm_num)
  simp only [liftImg, hw, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
  rw [liftImgs, hw]
  show [liftHom hk he (hGen 0), liftHom hk he (hGen 1), liftHom hk he (hGen 2)] =
    [evalPos hGens w0, evalPos hGens w1, evalPos hGens w2]
  rw [h0, h1, h2]

theorem liftHom_eq_liftFun
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    ⇑(liftHom hk he) = liftFun e := by
  funext x
  rw [liftFun, ← hGens_map_liftHom hk he, substFun_eq_of_hom hGens hGens_closure_top]

theorem liftHom_q
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    liftHom hk he qM = qM ^ e.power := by
  have hq : liftHom hk he qM = evalPos (liftImgs e) liftData.qWord := by
    rw [qM_eq, map_evalPos, hGens_map_liftHom hk he]
  rw [hq]
  exact resYM_qWord hk he

theorem getElem!_eq_getD {A : Array (Array ℕ)} {j : ℕ} (hj : j < A.size) :
    A[j]! = A.getD j #[] := by
  rw [getElem!_pos A j hj, Array.getD_eq_getD_getElem?, getElem?_pos A j hj, Option.getD_some]

theorem candOK_lift
    {k : ℕ} (hk : k < 12) {a : ℕ} (ha : a < 64) {i : ℕ}
    (hc : (liftData.cands.getD k []).getD a default = .lift i) :
    i < (recK k).lifts.length ∧ ∀ j < 3, liftImg ((recK k).lifts.getD i default) j =
      candElem k a j := by
  have hok := (candCheck_facts hk).2.2.2.2 a ha
  rw [hc] at hok
  simp only [candOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hi, hall⟩ := hok
  have he : (recK k).lifts.getD i default ∈ (recK k).lifts := getD_mem hi _
  refine ⟨hi, fun j hj => Subtype.ext ?_⟩
  have h := allBelowN_spec hall hj
  obtain ⟨hl, hw, -⟩ := lift_form hk he
  have hjl : j < ((recK k).lifts.getD i default).words.length := by rw [hl]; exact hj
  have hrep := prep_posArr_h (hw _ (getD_mem hjl []))
  have hc2 := candImgs_getD hk a hj
  have e1 : (candImgs ((liftData.lw.getD k []).map (posArr nPts (wordArrs Data.MWords))).toArray
      a)[j]! = (candImgs ((liftData.lw.getD k []).map
        (posArr nPts (wordArrs Data.MWords))).toArray a).getD j #[] :=
    getElem!_eq_getD (by simp [candImgs]; omega)
  rw [e1] at h
  exact eq_of_peq hrep hc2.1 h

theorem exists_cand_of_lift
    {k : ℕ} (hk : k < 12) {i : ℕ} (hi : i < (recK k).lifts.length) :
    ∃ a < 64, (liftData.cands.getD k []).getD a default = .lift i := by
  obtain ⟨hcount, hnodup⟩ := cand_count_cert
  have hlen : (liftIdxs (liftData.cands.getD k [])).length = (recK k).lifts.length := by
    have h1 := congrArg (fun l => l.getD k 0) hcount
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range] at h1
    rw [h1, recK_lifts_length hk]
  have hnd : (liftIdxs (liftData.cands.getD k [])).Nodup := by
    have := List.all_eq_true.1 hnodup k (List.mem_range.2 hk)
    simpa using this
  have hcl : (liftData.cands.getD k []).length = 64 := (candCheck_facts hk).2.2.2.1
  have hlt : ∀ j ∈ liftIdxs (liftData.cands.getD k []), j < (recK k).lifts.length := by
    intro j hj
    obtain ⟨c, hc, hcj⟩ := List.mem_filterMap.1 hj
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hc
    cases hca : (liftData.cands.getD k [])[a] with
    | rel w w' => rw [hca] at hcj; exact absurd hcj (by simp [candLift])
    | lift j' =>
      rw [hca] at hcj
      simp only [candLift, Option.some.injEq] at hcj
      subst hcj
      have hcd : (liftData.cands.getD k []).getD a default = .lift j' := by
        rw [List.getD_eq_getElem _ _ ha, hca]
      exact (candOK_lift hk (by omega) hcd).1
  have hmem : i ∈ liftIdxs (liftData.cands.getD k []) := by
    by_contra hni
    have hsub : (liftIdxs (liftData.cands.getD k [])).toFinset ⊆
        (Finset.range (recK k).lifts.length).erase i := by
      intro j hj
      rw [List.mem_toFinset] at hj
      rw [Finset.mem_erase, Finset.mem_range]
      exact ⟨fun h => hni (h ▸ hj), hlt j hj⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_erase_of_mem (Finset.mem_range.2 hi),
      Finset.card_range] at this
    omega
  obtain ⟨c, hc, hci⟩ := List.mem_filterMap.1 hmem
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hc
  refine ⟨a, by omega, ?_⟩
  rw [List.getD_eq_getElem _ _ ha]
  cases hca : (liftData.cands.getD k [])[a] with
  | rel w w' => rw [hca] at hci; exact absurd hci (by simp [candLift])
  | lift j' =>
    rw [hca] at hci
    simp only [candLift, Option.some.injEq] at hci
    rw [hci]

end CFSG.Sporadic.ONOddCore
