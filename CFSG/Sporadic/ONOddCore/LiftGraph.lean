module

public import CFSG.Sporadic.ONOddCore.LiftHoms
public import CFSG.Sporadic.ONOddCore.LiftHomCheck

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] def pairEmbOf (n : ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + n)) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin n) (Fin n))

theorem pairEmbOf_injective (n : ℕ) : Function.Injective (pairEmbOf n) :=
  (finSumFinEquiv.permCongrHom).injective.comp Equiv.Perm.sumCongrHom_injective

theorem pairEmbOf_apply {n : ℕ} (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) (x : Fin (n + n)) :
    pairEmbOf n g x = finSumFinEquiv (Sum.map g.1 g.2 (finSumFinEquiv.symm x)) := rfl

theorem prep_dbl_of {n : ℕ} {A B : Array ℕ} {a b : Equiv.Perm (Fin n)} (hA : PRep n A a)
    (hB : PRep n B b) (hs : A.size = n) (hs' : B.size = n) :
    PRep (n + n) (dbl n A B) (pairEmbOf n (a, b)) := by
  intro x
  rw [pairEmbOf_apply]
  rcases Nat.lt_or_ge x.val n with h | h
  · have e : (finSumFinEquiv (m := n) (n := n)).symm x = Sum.inl ⟨x.val, h⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
    rw [e]
    simp only [Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]
    unfold dbl
    rw [getElem!_pos _ x.val (by simp only [Array.size_append, Array.size_map, hs, hs']; omega),
      Array.getElem_append_left (by omega), ← getElem!_pos A x.val (by omega)]
    exact hA ⟨x.val, h⟩
  · have hx : x.val - n < n := by omega
    have e : (finSumFinEquiv (m := n) (n := n)).symm x = Sum.inr ⟨x.val - n, hx⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
      omega
    rw [e]
    simp only [Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]
    unfold dbl
    rw [getElem!_pos _ x.val (by simp only [Array.size_append, Array.size_map, hs, hs']; omega),
      Array.getElem_append_right (by omega)]
    simp only [Array.getElem_map, hs]
    rw [← getElem!_pos B (x.val - n) (by omega), hB ⟨x.val - n, hx⟩]
    omega

section Res


theorem res_facts : resY.size = 480 ∧ (∀ k < 479, resY[k]! < resY[k + 1]!) ∧ resY[479]! < N ∧
    (∀ j < 3, (resArrs[j]!).size = 480 ∧ ∀ k < 480, (resArrs[j]!)[k]! < 480 ∧
      resY[(resArrs[j]!)[k]!]! = ((wordArrs Data.MWords)[j]!)[resY[k]!]!) ∧
    CFSG.Sporadic.HNOddCore.chainCheck 480 resArrs resW resBase resSizes = true := by
  have h := lift_res_cert
  simp only [liftResOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun k hk => by simpa using allBelowN_spec h2 hk, h3, fun j hj => ?_, h5⟩
  have := allBelowN_spec h4 hj
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  refine ⟨this.1, fun k hk => ?_⟩
  have := allBelowN_spec this.2 hk
  simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using this

theorem resY_lt {k l : ℕ} (hkl : k < l) (hl : l < 480) : resY[k]! < resY[l]! := by
  induction l with
  | zero => omega
  | succ l ih =>
    have h := res_facts.2.1 l (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkl with h' | h'
    · exact lt_trans (ih h' (by omega)) h
    · rw [h']
      exact h

theorem resY_lt_N {k : ℕ} (hk : k < 480) : resY[k]! < N := by
  rcases Nat.lt_or_ge k 479 with h | h
  · exact lt_trans (resY_lt h (by norm_num)) res_facts.2.2.1
  · rw [show k = 479 by omega]
    exact res_facts.2.2.1

@[expose] def resPt (k : Fin 480) : Fin N := ⟨resY[(k : ℕ)]!, resY_lt_N k.2⟩

theorem resPt_injective : Function.Injective resPt := by
  intro k l h
  have e : resY[(k : ℕ)]! = resY[(l : ℕ)]! := congrArg Fin.val h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h' | h'
  · exact absurd e (Nat.ne_of_lt (resY_lt h' l.2))
  · exact absurd e (Nat.ne_of_gt (resY_lt h' k.2))

@[expose] def resStab : Subgroup (Equiv.Perm (Fin N)) where
  carrier := {g | ∀ k : Fin 480, ∃ l : Fin 480, g (resPt k) = resPt l}
  one_mem' := fun k => ⟨k, rfl⟩
  mul_mem' := by
    intro g h hg hh k
    obtain ⟨l, hl⟩ := hh k
    obtain ⟨m, hm⟩ := hg l
    exact ⟨m, by rw [Equiv.Perm.mul_apply, hl, hm]⟩
  inv_mem' := by
    intro g hg k
    let f : Fin 480 → Fin 480 := fun k => Classical.choose (hg k)
    have hf : ∀ k, g (resPt k) = resPt (f k) := fun k => Classical.choose_spec (hg k)
    have hinj : Function.Injective f := by
      intro a b hab
      apply resPt_injective
      apply g.injective
      rw [hf, hf, hab]
    obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.1 hinj) k
    refine ⟨m, ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, hf, hm]

theorem hGen_apply_resPt {j : ℕ} (hj : j < 3) (k : Fin 480) :
    (hGen j : Equiv.Perm (Fin N)) (resPt k) =
      resPt ⟨(resArrs[j]!)[(k : ℕ)]!, ((res_facts.2.2.2.1 j hj).2 k k.2).1⟩ := by
  apply Fin.ext
  have e := ((res_facts.2.2.2.1 j hj).2 k k.2).2
  have hp := (prep_hA hj).apply (resY_lt_N k.2)
  change ((hGen j : Equiv.Perm (Fin N)) (resPt k) : ℕ) = resY[(resArrs[j]!)[(k : ℕ)]!]!
  rw [e, hp]
  rfl

theorem onM_le_resStab : onM ≤ resStab := by
  rw [onM, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_onMgens_iff.1 hg
  exact fun k => ⟨_, hGen_apply_resPt hj k⟩

@[expose] def resFunM (g : onM) (k : Fin 480) : Fin 480 :=
  Classical.choose (onM_le_resStab g.2 k)

theorem resPt_resFunM (g : onM) (k : Fin 480) :
    resPt (resFunM g k) = (g : Equiv.Perm (Fin N)) (resPt k) :=
  (Classical.choose_spec (onM_le_resStab g.2 k)).symm

theorem resFunM_one (k : Fin 480) : resFunM 1 k = k :=
  resPt_injective (by rw [resPt_resFunM]; rfl)

theorem resFunM_mul (g h : onM) (k : Fin 480) :
    resFunM (g * h) k = resFunM g (resFunM h k) :=
  resPt_injective (by rw [resPt_resFunM, resPt_resFunM, resPt_resFunM]; rfl)

@[expose] def resYM : onM →* Equiv.Perm (Fin 480) where
  toFun g :=
    { toFun := resFunM g
      invFun := resFunM g⁻¹
      left_inv := fun k => by rw [← resFunM_mul, inv_mul_cancel, resFunM_one]
      right_inv := fun k => by rw [← resFunM_mul, mul_inv_cancel, resFunM_one] }
  map_one' := Equiv.ext fun k => resFunM_one k
  map_mul' g h := Equiv.ext fun k => resFunM_mul g h k

theorem resPt_resYM (g : onM) (k : Fin 480) :
    resPt (resYM g k) = (g : Equiv.Perm (Fin N)) (resPt k) := resPt_resFunM g k

theorem prep_resArrs {j : ℕ} (hj : j < 3) : PRep 480 resArrs[j]! (resYM (hGen j)) := by
  intro k
  have e := resPt_injective ((resPt_resYM (hGen j) k).trans (hGen_apply_resPt hj k))
  rw [e]

theorem resArrs_size : resArrs.size = 3 := rfl

theorem resArrs_get_size {j : ℕ} (hj : j < 3) : resArrs[j]!.size = 480 :=
  (res_facts.2.2.2.1 j hj).1

theorem prep_res_posArr {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    PRep 480 (posArr 480 resArrs w) (resYM (evalPos hGens w)) := by
  rw [map_evalPos]
  refine prep_posArr (fun l h1 h2 => ?_) w (fun l hl => ⟨(hw l hl).1, by
    rw [List.length_map, hGens_length]; exact (hw l hl).2⟩)
  rw [List.length_map, hGens_length] at h2
  have hl3 : l - 1 < 3 := by omega
  have e1 : resArrs.getD (l - 1) (pid 480) = resArrs[l - 1]! := by
    rw [Array.getD_eq_getD_getElem?, getElem!_pos _ _ (by rw [resArrs_size]; exact hl3),
      getElem?_pos _ _ (by rw [resArrs_size]; exact hl3), Option.getD_some]
  have e2 : (hGens.map resYM).getD (l - 1) 1 = resYM (hGen (l - 1)) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hGens_length]; exact hl3),
      List.getElem_map, hGen, List.getD_eq_getElem _ _ (by rw [hGens_length]; exact hl3)]
  rw [e1, e2]
  exact prep_resArrs hl3

theorem resYM_range : resYM.range = Subgroup.closure (Set.range fun k : Fin resArrs.size =>
    resYM (hGen k)) := by
  rw [MonoidHom.range_eq_map, ← hGens_closure_top, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, mem_hGens_iff]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨⟨i, by rw [resArrs_size]; exact hi⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨hGen k, ⟨k, by rw [← resArrs_size]; exact k.2, rfl⟩, rfl⟩

theorem card_resYM_range : Nat.card resYM.range = 161280 := by
  have hc := CFSG.Sporadic.HNOddCore.card_arrGen_of_chainCheck (by norm_num) (by decide)
    res_facts.2.2.2.2
  rw [CFSG.Sporadic.HNOddCore.arrGen_eq (σ := fun k => resYM (hGen k))
    (fun k hk => prep_resArrs (by rw [← resArrs_size]; exact hk))] at hc
  rw [resYM_range, hc]
  rfl

theorem resYM_injective : Function.Injective resYM := by
  have hs : Function.Surjective resYM.rangeRestrict := MonoidHom.rangeRestrict_surjective _
  have hb := hs.bijective_of_nat_card_le (by rw [card_onM, card_resYM_range])
  exact MonoidHom.rangeRestrict_injective_iff.1 hb.1

theorem lift_graph_facts {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    CFSG.Sporadic.HNOddCore.chainCheck 960 (resPair e) resW resBase2 resSizes = true ∧
      peq 480 (posArr 480 (resLift e) liftData.qWord) (resQPow e.power) = true := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 lift_graph_cert _ (recK_mem hk)) e he
  simpa only [liftGraphOK, Bool.and_eq_true] using h

theorem prep_resLift {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) {i : ℕ}
    (hi : i < 3) : PRep 480 (resLift e)[i]! (resYM (liftImg e i)) ∧ (resLift e)[i]!.size = 480 := by
  obtain ⟨hl, hw, -⟩ := lift_form hk he
  have hil : i < e.words.length := by rw [hl]; exact hi
  have e1 : (resLift e)[i]! = posArr 480 resArrs (e.words.getD i []) := by
    rw [resLift, getElem!_pos _ _ (by simpa using hil), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hil]
  rw [e1]
  exact ⟨prep_res_posArr (hw _ (by rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil)),
    posArr_size_gen _ _ _⟩

@[expose] def resPairHom : onM × onM →* Equiv.Perm (Fin (480 + 480)) :=
  (pairEmbOf 480).comp (resYM.prodMap resYM)

theorem resPairHom_injective : Function.Injective resPairHom :=
  (pairEmbOf_injective 480).comp (Prod.map_injective.2 ⟨resYM_injective, resYM_injective⟩)

theorem prep_resPair {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) {j : ℕ}
    (hj : j < (resPair e).size) :
    PRep 960 (resPair e)[j]! (resPairHom (hGen j, liftImg e j)) := by
  have hj3 : j < 3 := hj
  have h := prep_dbl_of (prep_resArrs hj3) (prep_resLift hk he hj3).1 (resArrs_get_size hj3)
    (prep_resLift hk he hj3).2
  have e1 : (resPair e)[j]! = dbl 480 resArrs[j]! (resLift e)[j]! := by
    interval_cases j <;> rfl
  rw [e1]
  exact h

theorem card_lift_pairs {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    Nat.card (Subgroup.closure ((fun j => (hGen j, liftImg e j)) '' {j | j < 3})) = 161280 := by
  have hc := CFSG.Sporadic.HNOddCore.card_arrGen_of_chainCheck (by norm_num) (by decide)
    (lift_graph_facts hk he).1
  rw [CFSG.Sporadic.HNOddCore.arrGen_eq (σ := fun j => resPairHom (hGen j, liftImg e j))
    (fun j hj => prep_resPair hk he hj)] at hc
  rw [← Subgroup.card_map_of_injective resPairHom_injective, MonoidHom.map_closure]
  have hS : resPairHom '' ((fun j => (hGen j, liftImg e j)) '' {j | j < 3}) =
      Set.range fun j : Fin (resPair e).size => resPairHom (hGen j, liftImg e j) := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, j.2, rfl⟩, rfl⟩
  rw [hS]
  exact hc.trans rfl

theorem exists_liftHom_res {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    ∃ φ : onM →* onM, ∀ i < 3, φ (hGen i) = liftImg e i := by
  set S := (fun j => (hGen j, liftImg e j)) '' {j | j < 3}
  have hcl : Subgroup.closure (Prod.fst '' S) = ⊤ := by
    rw [← hGens_closure_top]
    congr 1
    ext g
    simp only [S, Set.mem_image, Set.mem_ofPred_eq, mem_hGens_iff]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  have hcard : Nat.card (Subgroup.closure S) ≤ Nat.card (Subgroup.closure (Prod.fst '' S)) := by
    rw [card_lift_pairs hk he, hcl, Subgroup.card_top, card_onM]
  obtain ⟨φ₀, hφ₀⟩ := exists_hom_of_graph S hcard
  let e₁ : onM ≃* Subgroup.closure (Prod.fst '' S) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcl.symm)
  refine ⟨φ₀.comp e₁.toMonoidHom, fun i hi => ?_⟩
  exact hφ₀ _ ⟨i, hi, rfl⟩

theorem prep_resQ : PRep 480 resQ (resYM qM) := by
  rw [qM_eq]
  exact prep_res_posArr cand_facts.2.1

theorem prep_resQPow :
    ∀ p : ℕ, PRep 480 (resQPow p) (resYM (qM ^ p))
  | 0 => by
    rw [pow_zero, map_one]
    exact prep_pid
  | p + 1 => by
    rw [pow_succ', map_mul]
    exact prep_pcomp prep_resQ (prep_resQPow p)

theorem resYM_qWord {k : ℕ} (hk : k < 12) {e : LiftEntry}
    (he : e ∈ (recK k).lifts) :
    evalPos (liftImgs e) liftData.qWord = qM ^ e.power := by
  apply resYM_injective
  obtain ⟨hl, -, -⟩ := lift_form hk he
  have hw := cand_facts.2.1
  have hrep := prep_posArr (n := 480) (gs := resLift e) (G := (liftImgs e).map resYM)
    (fun l h1 h2 => by
      rw [List.length_map, liftImgs, List.length_map, hl] at h2
      have hl3 : l - 1 < 3 := by omega
      have hs : (resLift e).size = 3 := by simp [resLift, hl]
      have e1 : (resLift e).getD (l - 1) (pid 480) = (resLift e)[l - 1]! := by
        rw [Array.getD_eq_getD_getElem?, getElem!_pos _ _ (by rw [hs]; exact hl3),
          getElem?_pos _ _ (by rw [hs]; exact hl3), Option.getD_some]
      have e2' : (liftImgs e).getD (l - 1) 1 = liftImg e (l - 1) := by
        rw [liftImgs, List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact hl3),
          List.getElem_map, liftImg, List.getD_eq_getElem _ _ (by rw [hl]; exact hl3)]
      have e2 : ((liftImgs e).map resYM).getD (l - 1) 1 = resYM (liftImg e (l - 1)) := by
        rw [← e2', List.getD_eq_getElem _ _ (by
          rw [List.length_map, liftImgs, List.length_map, hl]; exact hl3), List.getElem_map,
          List.getD_eq_getElem _ _ (by rw [liftImgs, List.length_map, hl]; exact hl3)]
      rw [e1, e2]
      exact (prep_resLift hk he hl3).1) _ (fun l hl' => ⟨(hw l hl').1, by
        rw [List.length_map, liftImgs, List.length_map, hl]; exact (hw l hl').2⟩)
  rw [← map_evalPos] at hrep
  exact eq_of_peq hrep (prep_resQPow _) (lift_graph_facts hk he).2

end Res

end CFSG.Sporadic.ONOddCore
