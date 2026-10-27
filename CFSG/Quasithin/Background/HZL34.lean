module

public import CFSG.Quasithin.Background.HZL34Gen
public import CFSG.Quasithin.Background.HL3NineW9
public import CFSG.Quasithin.Background.HZCoc24
public import Certificates.Certificate7236

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H13.Ch9.L34M
open scoped commutatorElement

@[expose] def glOf (M M' : Matrix (Fin 3) (Fin 3) F4) (h : M * M' = 1 ∧ M' * M = 1) :
    GL (Fin 3) F4 :=
  ⟨M, M', h.1, h.2⟩

@[expose] def xG : GL (Fin 3) F4 := glOf xM xMi x_inv

@[expose] def yG : GL (Fin 3) F4 := glOf yM yMi y_inv

theorem rho9_mem_img9 {g : GL (Fin 3) F4} (h : (g : Matrix (Fin 3) (Fin 3) F4).det = 1) :
    rho9 g ∈ img9 :=
  ⟨⟨g, h⟩, congrArg rho9 (Units.ext rfl)⟩

theorem rho9_toW_cols (g : GL (Fin 3) F4) {c : List ℕ}
    (hc : cols (g : Matrix (Fin 3) (Fin 3) F4) = c) {m : ℕ} (hm : m < 512) :
    rho9 g (toW 9 m) = toW 9 (actM c m) := by
  subst hc
  exact (rho9_toW9 g ⟨m, hm⟩).trans (congrArg (toW 9) (actM_cols _ ⟨m, hm⟩).symm)

theorem actM_cols_lt (M : Matrix (Fin 3) (Fin 3) F4) {m : ℕ} (hm : m < 512) :
    actM (cols M) m < 512 := by
  rw [show m = ((⟨m, hm⟩ : Fin 512) : ℕ) from rfl, actM_cols]
  exact (act M ⟨m, hm⟩).isLt

theorem rho9_eq_of_cols {g g' : GL (Fin 3) F4}
    (h : cols (g : Matrix (Fin 3) (Fin 3) F4) = cols (g' : Matrix (Fin 3) (Fin 3) F4)) :
    rho9 g = rho9 g' := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 w
  have hm' : m < 512 := lt_of_lt_of_eq hm (by norm_num)
  rw [rho9_toW_cols g rfl hm', rho9_toW_cols g' rfl hm', h]

theorem cols_eq_of_rho9_eq {g g' : GL (Fin 3) F4} (h : rho9 g = rho9 g') :
    cols (g : Matrix (Fin 3) (Fin 3) F4) = cols (g' : Matrix (Fin 3) (Fin 3) F4) := by
  unfold cols matOf
  refine List.map_congr_left fun j hj => ?_
  have hj9 : 2 ^ j < 512 := by
    have := List.mem_range.1 hj
    calc 2 ^ j < 2 ^ 9 := Nat.pow_lt_pow_right (by norm_num) this
      _ = 512 := by norm_num
  have e : rho9 g (toW 9 (2 ^ j)) = rho9 g' (toW 9 (2 ^ j)) := by rw [h]
  rw [rho9_toW_cols g rfl hj9, rho9_toW_cols g' rfl hj9] at e
  have e2 := toW_inj (lt_of_lt_of_eq (actM_cols_lt _ hj9) (by norm_num))
    (lt_of_lt_of_eq (actM_cols_lt _ hj9) (by norm_num)) e
  have k : ∀ M : Matrix (Fin 3) (Fin 3) F4, actN M (2 ^ j) = actM (cols M) (2 ^ j) := fun M =>
    (actN_val M ⟨2 ^ j, hj9⟩).trans (actM_cols M ⟨2 ^ j, hj9⟩).symm
  rw [k, k]
  exact e2

@[expose] def wGL (gs : List (GL (Fin 3) F4)) : List ℕ → GL (Fin 3) F4
  | [] => 1
  | i :: w => gs.getD i 1 * wGL gs w

theorem coe_wGL (gs : List (GL (Fin 3) F4)) : ∀ w,
    ((wGL gs w : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      wM (gs.map Units.val) w
  | [] => rfl
  | i :: w => by
    have h1 : (gs.map Units.val).getD i 1 =
        ((gs.getD i 1 : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
      rw [← Units.val_one, List.getD_map]
    rw [wGL, wM, Units.val_mul, coe_wGL gs w, h1]

theorem rho9_wGL_mem {L : Subgroup (MulAut W9)} {gs : List (GL (Fin 3) F4)}
    (h : ∀ g ∈ gs, rho9 g ∈ L) : ∀ w, rho9 (wGL gs w) ∈ L
  | [] => by
    rw [wGL, map_one]
    exact L.one_mem
  | i :: w => by
    rw [wGL, map_mul]
    refine L.mul_mem ?_ (rho9_wGL_mem h w)
    by_cases hi : i < gs.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega), map_one]
      exact L.one_mem

@[expose] noncomputable def L34 : Subgroup (MulAut W9) := Subgroup.closure {rho9 xG, rho9 yG}

theorem x_mem_L34 : rho9 xG ∈ L34 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem y_mem_L34 : rho9 yG ∈ L34 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem L34_le_img9 : L34 ≤ img9 := by
  rw [L34, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact rho9_mem_img9 det_xM
  · exact rho9_mem_img9 det_yM

theorem mem_L34_of_cols {g : GL (Fin 3) F4} {w : List ℕ}
    (h : cols (g : Matrix (Fin 3) (Fin 3) F4) = cols (wM [xM, yM] w)) : rho9 g ∈ L34 := by
  have e : rho9 g = rho9 (wGL [xG, yG] w) := rho9_eq_of_cols (by rw [h, coe_wGL]; rfl)
  rw [e]
  refine rho9_wGL_mem (fun g hg => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact x_mem_L34
  · exact y_mem_L34

@[expose] def iota : MulAut W9 →* Equiv.Perm (Fin 512) where
  toFun φ := (toW9.trans φ.toEquiv).trans toW9.symm
  map_one' := by
    ext m
    simp
  map_mul' φ ψ := by
    ext m
    simp

theorem iota_apply (φ : MulAut W9) (m : Fin 512) : iota φ m = toW9.symm (φ (toW9 m)) := rfl

theorem iota_injective : Function.Injective iota := by
  intro φ ψ h
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, rfl⟩ := toW9.surjective w
  have := congrArg (fun p : Equiv.Perm (Fin 512) => toW9 (p m)) h
  simpa [iota_apply] using this

theorem iota_rho9 (g : GL (Fin 3) F4) (m : Fin 512) :
    iota (rho9 g) m = act (g : Matrix (Fin 3) (Fin 3) F4) m := by
  rw [iota_apply, rho9_toW9, Equiv.symm_apply_apply]

@[expose] noncomputable def G34 : Subgroup (Equiv.Perm (Fin 512)) :=
  Subgroup.closure {iota (rho9 xG), iota (rho9 yG)}

theorem iota_x_mem : iota (rho9 xG) ∈ G34 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem iota_y_mem : iota (rho9 yG) ∈ G34 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem map_iota_L34 : L34.map iota = G34 := by
  rw [L34, MonoidHom.map_closure, Set.image_pair]
  rfl

section Order

open CFSG.Sporadic.Th CFSG.Sporadic.Mathieu

theorem rep_x : CFSG.Sporadic.Th.Rep 512 Native.l34Data.tA
    (⟨iota (rho9 xG), iota_x_mem⟩ : G34) := by
  have h : (List.range 512).all (fun i => CFSG.Sporadic.Th.Native.ap Native.l34Data.tA i ==
      actM colsX i) = true := by decide +kernel
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]
  calc actM colsX i = actM (cols xM) i := by rw [cols_x]
    _ = ((act xM ⟨i, hi⟩ : Fin 512) : ℕ) := actM_cols xM ⟨i, hi⟩
    _ = ((iota (rho9 xG) ⟨i, hi⟩ : Fin 512) : ℕ) := by rw [iota_rho9]; rfl

theorem rep_y : CFSG.Sporadic.Th.Rep 512 Native.l34Data.tB
    (⟨iota (rho9 yG), iota_y_mem⟩ : G34) := by
  have h : (List.range 512).all (fun i => CFSG.Sporadic.Th.Native.ap Native.l34Data.tB i ==
      actM colsY i) = true := by decide +kernel
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]
  calc actM colsY i = actM (cols yM) i := by rw [cols_y]
    _ = ((act yM ⟨i, hi⟩ : Fin 512) : ℕ) := actM_cols yM ⟨i, hi⟩
    _ = ((iota (rho9 yG) ⟨i, hi⟩ : Fin 512) : ℕ) := by rw [iota_rho9]; rfl

theorem card_G34 : Nat.card G34 = 960 := by
  have H : Hyp G34 Native.l34Data ⟨iota (rho9 xG), iota_x_mem⟩ ⟨iota (rho9 yG), iota_y_mem⟩ :=
    ⟨by norm_num, closure_pair_eq_top rfl _ _, rep_x, rep_y,
      Certificates.certificate7236⟩
  rw [card_eq H]
  rfl

end Order

theorem card_L34 : Nat.card L34 = 960 := by
  rw [← card_G34, ← map_iota_L34, Subgroup.card_map_of_injective iota_injective]

@[expose] def c0G : GL (Fin 3) F4 := ⁅xG, yG⁆

@[expose] def c2G : GL (Fin 3) F4 := ⁅xG, yG * yG⁆

theorem coe_c0G : (c0G : Matrix (Fin 3) (Fin 3) F4) = c0M := by
  show ((xG * yG * xG⁻¹ * yG⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = _
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  rfl

theorem coe_c2G : (c2G : Matrix (Fin 3) (Fin 3) F4) = c2M := by
  show ((xG * (yG * yG) * xG⁻¹ * (yG * yG)⁻¹ : GL (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4) = _
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, _root_.mul_inv_rev,
    Units.val_mul]
  rfl

theorem coe_c02 : ([c0G, c2G].map Units.val) = [c0M, c2M] := by
  rw [List.map_cons, List.map_cons, List.map_nil, coe_c0G, coe_c2G]

theorem commutator_L34 : ⁅L34, L34⁆ = L34 := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact L34.mul_mem (L34.mul_mem (L34.mul_mem ha hb) (L34.inv_mem ha)) (L34.inv_mem hb)) ?_
  have hc : ∀ g ∈ [c0G, c2G], rho9 g ∈ ⁅L34, L34⁆ := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [c0G, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator x_mem_L34 y_mem_L34
    · rw [c2G, map_commutatorElement, map_mul]
      exact Subgroup.commutator_mem_commutator x_mem_L34 (L34.mul_mem y_mem_L34 y_mem_L34)
  show Subgroup.closure ({rho9 xG, rho9 yG} : Set (MulAut W9)) ≤ ⁅L34, L34⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have hx : cols ((wGL [c0G, c2G] xWord : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        colsX := (congrArg cols (coe_wGL [c0G, c2G] xWord)).trans
          ((congrArg (fun l => cols (wM l xWord)) coe_c02).trans perfect_words.1)
    have e : rho9 xG = rho9 (wGL [c0G, c2G] xWord) := rho9_eq_of_cols (cols_x.trans hx.symm)
    rw [e]
    exact rho9_wGL_mem hc xWord
  · have hy : cols ((wGL [c0G, c2G] yWord : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        colsY := (congrArg cols (coe_wGL [c0G, c2G] yWord)).trans
          ((congrArg (fun l => cols (wM l yWord)) coe_c02).trans perfect_words.2)
    have e : rho9 yG = rho9 (wGL [c0G, c2G] yWord) := rho9_eq_of_cols (cols_y.trans hy.symm)
    rw [e]
    exact rho9_wGL_mem hc yWord

abbrev z0 : W9 := toW 9 1

@[expose] def oG (i : Fin 3) : GL (Fin 3) F4 := glOf (oMs.getD i 1) (oMis.getD i 1) (o_inv i i.2)

theorem det_oG (i : Fin 3) : ((oG i : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  fin_cases i
  · exact det_oM0
  · exact det_oM1
  · exact det_oM2

theorem orbTree_mem : ∀ e ∈ orbTree, ∃ h ∈ img9, h z0 = toW 9 e.1 := by
  have hP : ∀ g m, (m < 512 ∧ ∃ h ∈ img9, h z0 = toW 9 m) →
      orbAct g m < 512 ∧ ∃ h ∈ img9, h z0 = toW 9 (orbAct g m) := by
    rintro g m ⟨hm, h, hh, hhz⟩
    have hg : g % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hc := cols_o (g % 3) hg
    refine ⟨?_, rho9 (oG ⟨g % 3, hg⟩) * h, img9.mul_mem (rho9_mem_img9 (det_oG _)) hh, ?_⟩
    · show actM (colsO.getD (g % 3) []) m < 512
      rw [← hc]
      exact actM_cols_lt _ hm
    · rw [MulAut.mul_apply, hhz, rho9_toW_cols (oG ⟨g % 3, hg⟩) hc hm]
      rfl
  have hs : ∀ m, (1 <<< 1 : ℕ).testBit m = true → m < 512 ∧ ∃ h ∈ img9, h z0 = toW 9 m := by
    intro m hm
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hm
    rw [← of_decide_eq_true hm]
    exact ⟨by norm_num, 1, img9.one_mem, rfl⟩
  intro e he
  exact ((treeB_spec orbAct _ hP orbTree _ hs orbTree_ok).1 e he).2

theorem le_card_orbit : 21 ≤ (MulAction.orbit ↥img9 z0).ncard := by
  classical
  obtain ⟨-, hnd, hnot⟩ := treeB_spec orbAct (fun _ => True) (fun _ _ _ => trivial) orbTree _
    (fun _ _ => trivial) orbTree_ok
  set l : List ℕ := 1 :: orbTree.map Prod.fst with hl
  have hlnd : l.Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, hnd⟩
    obtain ⟨e, he, he1⟩ := List.mem_map.1 h
    have := hnot e he
    rw [he1, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    exact Bool.noConfusion this
  have hlt : ∀ m ∈ l, m < 2 ^ 9 := by
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · norm_num
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      exact orbTree_lt e he
  have hsub : ((l.map (toW 9)).toFinset : Set W9) ⊆ MulAction.orbit ↥img9 z0 := by
    intro v hv
    simp only [List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    rcases List.mem_cons.1 hm with rfl | hm
    · exact MulAction.mem_orbit_self _
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      obtain ⟨h, hh, hhz⟩ := orbTree_mem e he
      exact ⟨⟨h, hh⟩, hhz⟩
  have hinj : (l.map (toW 9)).Nodup := by
    refine hlnd.map_on fun a ha b hb hab => toW_inj (hlt a ha) (hlt b hb) hab
  have hlen : (l.map (toW 9)).length = 21 := by
    rw [List.length_map, hl, List.length_cons, List.length_map, orbTree_length]
  calc 21 = ((l.map (toW 9)).toFinset : Set W9).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, hlen]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_stab_le : Nat.card ↥(img9 ⊓ centSub (Subgroup.zpowers z0)) ≤ 960 := by
  have e : ↥(img9 ⊓ centSub (Subgroup.zpowers z0)) ≃ ↥(MulAction.stabilizer ↥img9 z0) :=
    { toFun := fun y => ⟨⟨y, y.2.1⟩, Coc24.mem_centSub_zpowers.1 y.2.2⟩
      invFun := fun y => ⟨y.1, y.1.2, Coc24.mem_centSub_zpowers.2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥img9 z0)
  rw [MulAction.index_stabilizer, card_img9, ← Nat.card_congr e] at h1
  have h2 := le_card_orbit
  by_contra hc
  push Not at hc
  have : 961 * 21 ≤ Nat.card ↥(img9 ⊓ centSub (Subgroup.zpowers z0)) *
      (MulAction.orbit ↥img9 z0).ncard := Nat.mul_le_mul hc h2
  omega

theorem L34_le_centSub : L34 ≤ centSub (Subgroup.zpowers z0) := by
  refine (Subgroup.closure_le (centSub (Subgroup.zpowers z0))).2 ?_
  rintro _ (rfl | rfl)
  · exact Coc24.mem_centSub_zpowers.2 ((rho9_toW_cols xG cols_x (by norm_num)).trans
      (congrArg (toW 9) xy_fix.1))
  · exact Coc24.mem_centSub_zpowers.2 ((rho9_toW_cols yG cols_y (by norm_num)).trans
      (congrArg (toW 9) xy_fix.2))

theorem L34_le_stab : L34 ≤ img9 ⊓ centSub (Subgroup.zpowers z0) :=
  le_inf L34_le_img9 L34_le_centSub

theorem perfectCore_stab :
    perfectCore (img9 ⊓ centSub (Subgroup.zpowers z0)) = L34 := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  have hEq : L34 = img9 ⊓ centSub (Subgroup.zpowers z0) :=
    Subgroup.eq_of_le_of_card_ge L34_le_stab (by rw [card_L34]; exact card_stab_le)
  rw [← hEq, perfectCore_eq_self_of_perfect commutator_L34]

theorem uM_mul_self (t : ℕ) : uM t * uM t = 1 := by
  show um (fc t) (fc (t / 4)) 0 * um (fc t) (fc (t / 4)) 0 = 1
  rw [um_mul, add_self_F4, mul_zero, add_zero, add_self_F4, add_self_F4]
  exact um_zero

@[expose] def uG (t : ℕ) : GL (Fin 3) F4 := ⟨uM t, uM t, uM_mul_self t, uM_mul_self t⟩

@[expose] def U1 : Subgroup (GL (Fin 3) F4) where
  carrier := {g | ∃ t < 16, g = uG t}
  mul_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨t ^^^ s, Nat.xor_lt_two_pow (n := 4) ht hs, Units.ext (uM_mul t ht s hs)⟩
  one_mem' := ⟨0, by norm_num, Units.ext uM_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, Units.ext rfl⟩

@[expose] noncomputable def Rbar : Subgroup (MulAut W9) := U1.map rho9

theorem uG_mem_U1 {t : ℕ} (ht : t < 16) : uG t ∈ U1 := ⟨t, ht, rfl⟩

theorem rho9_uG_mem_Rbar {t : ℕ} (ht : t < 16) : rho9 (uG t) ∈ Rbar :=
  ⟨uG t, uG_mem_U1 ht, rfl⟩

theorem mem_Rbar {φ : MulAut W9} : φ ∈ Rbar ↔ ∃ t < 16, rho9 (uG t) = φ := by
  constructor
  · rintro ⟨g, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact rho9_uG_mem_Rbar ht

theorem cols_uG {t : ℕ} (ht : t < 16) :
    cols ((uG t : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = colsU.getD t [] :=
  cols_u t ht

theorem rho9_uG_injective {t s : ℕ} (ht : t < 16) (hs : s < 16)
    (h : rho9 (uG t) = rho9 (uG s)) : t = s := by
  have e := cols_eq_of_rho9_eq h
  rw [cols_uG ht, cols_uG hs] at e
  have hnd := colsU_nodup
  have h1 : ((List.range 16).map fun t => colsU.getD t []).get ⟨t, by simpa using ht⟩ =
      ((List.range 16).map fun t => colsU.getD t []).get ⟨s, by simpa using hs⟩ := by
    simpa using e
  have := (List.Nodup.get_inj_iff hnd).1 h1
  simpa using this

theorem card_Rbar : Nat.card Rbar = 16 := by
  have hf : Function.Injective (fun t : Fin 16 => (⟨rho9 (uG t), rho9_uG_mem_Rbar t.2⟩ : Rbar)) :=
    fun t s h => Fin.ext (rho9_uG_injective t.2 s.2 (congrArg Subtype.val h))
  have hs : Function.Surjective
      (fun t : Fin 16 => (⟨rho9 (uG t), rho9_uG_mem_Rbar t.2⟩ : Rbar)) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hφ
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem Rbar_le_L34 : Rbar ≤ L34 := by
  intro φ hφ
  obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hφ
  exact mem_L34_of_cols ((cols_uG ht).trans (uWord_ok t ht).symm)

theorem isPGroup_Rbar : IsPGroup 2 Rbar := fun g => ⟨1, by
  obtain ⟨t, ht, hg⟩ := mem_Rbar.1 g.2
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, ← hg, pow_two, ← map_mul,
    show uG t * uG t = 1 from Units.ext (uM_mul_self t), map_one, Subgroup.coe_one]⟩

theorem conj_uG_x {t : ℕ} (ht : t < 16) :
    rho9 xG * rho9 (uG t) * (rho9 xG)⁻¹ = rho9 (uG (actM mxCols t)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg rho9 (Units.ext (u_conj t ht).1)

theorem conj_uG_y {t : ℕ} (ht : t < 16) :
    rho9 yG * rho9 (uG t) * (rho9 yG)⁻¹ = rho9 (uG (actM myCols t)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg rho9 (Units.ext (u_conj t ht).2)

theorem L34_le_normalizer_Rbar : L34 ≤ Subgroup.normalizer (Rbar : Set (MulAut W9)) := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  rw [L34, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> refine Subgroup.mem_normalizer_fintype fun k hk => ?_ <;>
    obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hk
  · rw [conj_uG_x ht]
    exact rho9_uG_mem_Rbar (actM_u_lt t ht).1
  · rw [conj_uG_y ht]
    exact rho9_uG_mem_Rbar (actM_u_lt t ht).2

theorem Rbar_le_pCoreOf : Rbar ≤ pCoreOf 2 L34 := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Rbar_le_L34 L34_le_normalizer_Rbar
    isPGroup_Rbar

@[expose] def sG (p : ℕ) : GL (Fin 3) F4 := uGL (fc p) (fc (p / 4)) (fc (p / 16))

theorem fc_decode (a b c : F4) :
    fc ((a.code : ℕ) + 4 * (b.code : ℕ) + 16 * (c.code : ℕ)) = a ∧
    fc (((a.code : ℕ) + 4 * (b.code : ℕ) + 16 * (c.code : ℕ)) / 4) = b ∧
    fc (((a.code : ℕ) + 4 * (b.code : ℕ) + 16 * (c.code : ℕ)) / 16) = c := by
  obtain ⟨⟨a, ha⟩⟩ := a
  obtain ⟨⟨b, hb⟩⟩ := b
  obtain ⟨⟨c, hc⟩⟩ := c
  refine ⟨f4_eq_of_code ?_, f4_eq_of_code ?_, f4_eq_of_code ?_⟩
  · show (a + 4 * b + 16 * c) % 4 = a
    omega
  · show (a + 4 * b + 16 * c) / 4 % 4 = b
    omega
  · show (a + 4 * b + 16 * c) / 16 % 4 = c
    omega

@[expose] noncomputable def S1 : Subgroup (MulAut W9) := U.map rho9

theorem mem_S1 {φ : MulAut W9} : φ ∈ S1 ↔ ∃ p < 64, rho9 (sG p) = φ := by
  constructor
  · rintro ⟨g, ⟨a, b, c, rfl⟩, rfl⟩
    refine ⟨(a.code : ℕ) + 4 * (b.code : ℕ) + 16 * (c.code : ℕ), by omega, ?_⟩
    obtain ⟨h1, h2, h3⟩ := fc_decode a b c
    rw [sG, h1, h2, h3]
  · rintro ⟨p, -, rfl⟩
    exact ⟨sG p, ⟨_, _, _, rfl⟩, rfl⟩

theorem cols_sG {p : ℕ} (hp : p < 64) :
    cols ((sG p : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = colsS1.getD p [] :=
  cols_s p hp

theorem rho9_sG_injective {p q : ℕ} (hp : p < 64) (hq : q < 64)
    (h : rho9 (sG p) = rho9 (sG q)) : p = q := by
  have e := cols_eq_of_rho9_eq h
  rw [cols_sG hp, cols_sG hq] at e
  have h1 : ((List.range 64).map fun p => colsS1.getD p []).get ⟨p, by simpa using hp⟩ =
      ((List.range 64).map fun p => colsS1.getD p []).get ⟨q, by simpa using hq⟩ := by
    simpa using e
  have := (List.Nodup.get_inj_iff s_nodup).1 h1
  simpa using this

theorem card_S1 : Nat.card S1 = 64 := by
  have hf : Function.Injective (fun p : Fin 64 =>
      (⟨rho9 (sG p), mem_S1.2 ⟨p, p.2, rfl⟩⟩ : S1)) :=
    fun p q h => Fin.ext (rho9_sG_injective p.2 q.2 (congrArg Subtype.val h))
  have hs : Function.Surjective (fun p : Fin 64 =>
      (⟨rho9 (sG p), mem_S1.2 ⟨p, p.2, rfl⟩⟩ : S1)) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨p, hp, rfl⟩ := mem_S1.1 hφ
    exact ⟨⟨p, hp⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem S1_le_L34 : S1 ≤ L34 := by
  intro φ hφ
  obtain ⟨p, hp, rfl⟩ := mem_S1.1 hφ
  exact mem_L34_of_cols ((cols_sG hp).trans (sWord_ok p hp).symm)

theorem factorization_960 : (960 : ℕ).factorization 2 = 6 := by
  rw [show (960 : ℕ) = 2 ^ 6 * 15 by norm_num, Nat.factorization_mul (by positivity) (by norm_num),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem pCoreOf_L34_le : pCoreOf 2 L34 ≤ Rbar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  set N := CFSG.Open.pCore 2 ↥L34 with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hT : Nat.card (S1.subgroupOf L34) = 2 ^ (Nat.card ↥L34).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S1_le_L34).toEquiv, card_S1, card_L34,
      factorization_960]
    norm_num
  let T : Sylow 2 ↥L34 := Sylow.ofCard (S1.subgroupOf L34) hT
  have hNT : N ≤ (T : Subgroup ↥L34) := hNp.le_sylow_of_normal T
  have hS1 : ∀ n ∈ N, (n : MulAut W9) ∈ S1 := fun n hn => Subgroup.mem_subgroupOf.1 (hNT hn)
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨p, hp, hpn⟩ := mem_S1.1 (hS1 n hn)
  by_cases hp16 : p < 16
  · refine mem_Rbar.2 ⟨p, hp16, (?_ : rho9 (uG p) = rho9 (sG p)).trans hpn⟩
    refine congrArg rho9 (Units.ext ?_)
    show um (fc p) (fc (p / 4)) 0 = um (fc p) (fc (p / 4)) (fc (p / 16))
    rw [Nat.div_eq_of_lt (by omega : p < 16)]
    rfl
  · exfalso
    set yL : ↥L34 := ⟨rho9 yG, y_mem_L34⟩
    have hy : yL⁻¹ * n * yL⁻¹⁻¹ ∈ N := hNn.conj_mem n hn yL⁻¹
    obtain ⟨q, hq, hqn⟩ := mem_S1.1 (hS1 _ hy)
    have e : rho9 (sG q) = rho9 (yG⁻¹ * sG p * yG) := by
      rw [hqn, map_mul, map_mul, map_inv, hpn]
      simp [yL]
    have e2 := cols_eq_of_rho9_eq e
    rw [cols_sG hq] at e2
    apply s_conj p hp (by omega)
    rw [show cols (yMi * sM p * yM) = colsS1.getD q [] from e2.symm]
    have hlen : q < colsS1.length := by
      have : colsS1.length = 64 := rfl
      omega
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen

theorem pCoreOf_L34 : pCoreOf 2 L34 = Rbar :=
  le_antisymm pCoreOf_L34_le Rbar_le_pCoreOf

end CFSG.Quasithin.H.L34Z
