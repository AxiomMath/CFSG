module

public import CFSG.Quasithin.Background.HZCode22
public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Background.HZCoc24B

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Mathieu.H16Pf
open scoped commutatorElement

@[expose] noncomputable def imgC (Γ : Subgroup (Equiv.Perm (Fin 24))) : Subgroup (MulAut W10) :=
  (Γ.subgroupOf mog22).map (rhoC10 mog22 mog22_le_mog22plus)

theorem range_rhoC10_eq_imgC : (rhoC10 mog22 mog22_le_mog22plus).range = imgC mog22 := by
  rw [imgC, Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem rhoC10_mem_imgC (σ : ↥mog22) : rhoC10 mog22 mog22_le_mog22plus σ ∈ imgC mog22 :=
  ⟨σ, Subgroup.mem_subgroupOf.2 σ.2, rfl⟩

abbrev z0 : W10 := toW 10 1

@[expose] def gA : Equiv.Perm (Fin 24) := permOfArr 24 gaArr gaInv g_ok.1

@[expose] def gB : Equiv.Perm (Fin 24) := permOfArr 24 gbArr gbInv g_ok.2.1

theorem hasArr_gA : HasArr gA gaArr := hasArr_permOfArr _

theorem hasArr_gB : HasArr gB gbArr := hasArr_permOfArr _

theorem gA_mem : gA ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ g_ok.2.2.1) hasArr_gA g_ok.2.2.2.2.1
    g_ok.2.2.2.2.2.1

theorem gB_mem : gB ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ g_ok.2.2.2.1) hasArr_gB g_ok.2.2.2.2.2.2.1
    g_ok.2.2.2.2.2.2.2

theorem orbTree_mem : ∀ e ∈ orbTree, ∃ h ∈ imgC mog22, h z0 = toW 10 e.1 := by
  have hP : ∀ g m, (∃ h ∈ imgC mog22, h z0 = toW 10 m) →
      ∃ h ∈ imgC mog22, h z0 = toW 10 (orbAct g m) := by
    rintro g m ⟨h, hh, hhz⟩
    by_cases hg : g = 0
    · refine ⟨rhoC10 mog22 mog22_le_mog22plus ⟨gA, gA_mem⟩ * h,
        (imgC mog22).mul_mem (rhoC10_mem_imgC _) hh, ?_⟩
      rw [MulAut.mul_apply, hhz, rhoC10_toW mog22 mog22_le_mog22plus ⟨gA, gA_mem⟩ hasArr_gA m,
        orbAct, ite_eq_left hg]
    · refine ⟨rhoC10 mog22 mog22_le_mog22plus ⟨gB, gB_mem⟩ * h,
        (imgC mog22).mul_mem (rhoC10_mem_imgC _) hh, ?_⟩
      rw [MulAut.mul_apply, hhz, rhoC10_toW mog22 mog22_le_mog22plus ⟨gB, gB_mem⟩ hasArr_gB m,
        orbAct, ite_eq_right hg]
  have hs : ∀ m, (1 <<< 1 : ℕ).testBit m = true → ∃ h ∈ imgC mog22, h z0 = toW 10 m := by
    intro m hm
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hm
    rw [← of_decide_eq_true hm]
    exact ⟨1, (imgC mog22).one_mem, rfl⟩
  exact (treeB_spec orbAct _ hP orbTree _ hs orbTree_ok).1

theorem le_card_orbit : 77 ≤ (MulAction.orbit ↥(imgC mog22) z0).ncard := by
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
  have hlt : ∀ m ∈ l, m < 2 ^ 10 := by
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · norm_num
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      exact orbTree_lt e he
  have hsub : ((l.map (toW 10)).toFinset : Set W10) ⊆ MulAction.orbit ↥(imgC mog22) z0 := by
    intro v hv
    simp only [List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    rcases List.mem_cons.1 hm with rfl | hm
    · exact MulAction.mem_orbit_self _
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      obtain ⟨h, hh, hhz⟩ := orbTree_mem e he
      exact ⟨⟨h, hh⟩, hhz⟩
  have hinj : (l.map (toW 10)).Nodup := by
    refine hlnd.map_on fun a ha b hb hab => toW_inj (hlt a ha) (hlt b hb) hab
  have hlen : (l.map (toW 10)).length = 77 := by
    rw [List.length_map, hl, List.length_cons, List.length_map, orbTree_length]
  calc 77 = ((l.map (toW 10)).toFinset : Set W10).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, hlen]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_imgC_mog22 :
    Nat.card ↥(imgC mog22) = 443520 := by
  rw [imgC, Subgroup.card_map_of_injective ModelType.rhoC10_mog22_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_rfl).toEquiv, card_mog22]

theorem card_stab_le :
    Nat.card ↥(imgC mog22 ⊓ centSub (Subgroup.zpowers z0)) ≤ 5760 := by
  have e : ↥(imgC mog22 ⊓ centSub (Subgroup.zpowers z0)) ≃
      ↥(MulAction.stabilizer ↥(imgC mog22) z0) :=
    { toFun := fun y => ⟨⟨y, y.2.1⟩, Coc24.mem_centSub_zpowers.1 y.2.2⟩
      invFun := fun y => ⟨y.1, y.1.2, Coc24.mem_centSub_zpowers.2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(imgC mog22) z0)
  rw [MulAction.index_stabilizer, card_imgC_mog22, ← Nat.card_congr e] at h1
  have h2 := le_card_orbit
  by_contra hc
  push Not at hc
  have : 5761 * 77 ≤ Nat.card ↥(imgC mog22 ⊓ centSub (Subgroup.zpowers z0)) *
      (MulAction.orbit ↥(imgC mog22) z0).ncard := Nat.mul_le_mul hc h2
  omega

theorem imgC_L22_le_centSub : imgC L22 ≤ centSub (Subgroup.zpowers z0) := by
  have hQ : L22 ≤ ((centSub (Subgroup.zpowers z0)).comap
      (rhoC10 mog22 mog22_le_mog22plus)).map mog22.subtype := by
    rw [L22, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨⟨lX, lX_mem⟩, Coc24.mem_centSub_zpowers.2 ?_, rfl⟩
      exact (rhoC10_toW mog22 mog22_le_mog22plus ⟨lX, lX_mem⟩ hasArr_lX 1).trans
        (congrArg (toW 10) l_fix.1)
    · refine ⟨⟨lY, lY_mem⟩, Coc24.mem_centSub_zpowers.2 ?_, rfl⟩
      exact (rhoC10_toW mog22 mog22_le_mog22plus ⟨lY, lY_mem⟩ hasArr_lY 1).trans
        (congrArg (toW 10) l_fix.2)
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hτσ⟩ := hQ (Subgroup.mem_subgroupOf.1 hσ)
  rw [show σ = τ from Subtype.ext hτσ.symm]
  exact hτ

theorem imgC_L22_le_stab : imgC L22 ≤ imgC mog22 ⊓ centSub (Subgroup.zpowers z0) :=
  le_inf (Subgroup.map_mono fun σ _ => Subgroup.mem_subgroupOf.2 σ.2) imgC_L22_le_centSub

theorem card_imgC_L22 :
    Nat.card ↥(imgC L22) = 5760 := by
  rw [imgC, Subgroup.card_map_of_injective ModelType.rhoC10_mog22_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe L22_le).toEquiv, card_L22]

theorem commutator_imgC_L22 : ⁅imgC L22, imgC L22⁆ = imgC L22 := by
  have h : ⁅L22.subgroupOf mog22, L22.subgroupOf mog22⁆ = L22.subgroupOf mog22 := by
    apply Subgroup.map_injective mog22.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le L22_le, commutator_L22]
  rw [imgC, ← Subgroup.map_commutator, h]

theorem perfectCore_stab :
    perfectCore (imgC mog22 ⊓ centSub (Subgroup.zpowers z0)) = imgC L22 := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  have hEq : imgC L22 = imgC mog22 ⊓ centSub (Subgroup.zpowers z0) :=
    Subgroup.eq_of_le_of_card_ge imgC_L22_le_stab (by rw [card_imgC_L22]; exact card_stab_le)
  rw [← hEq, perfectCore_eq_self_of_perfect commutator_imgC_L22]

theorem pCoreOf_imgC_L22 :
    pCoreOf 2 (imgC L22) = imgC fixO := by
  rw [imgC, pCoreOf_map_of_injective 2 _ ModelType.rhoC10_mog22_injective,
    Coc24.pCoreOf_subgroupOf L22_le, pCoreOf_L22]
  rfl

theorem card_imgC_fixO :
    Nat.card ↥(imgC fixO) = 2 ^ 4 := by
  rw [imgC, Subgroup.card_map_of_injective ModelType.rhoC10_mog22_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_mog22).toEquiv, card_fixO]
  norm_num

@[expose] def koP (t : ℕ) : Equiv.Perm (Fin 24) := if h : t < 16 then koPerm ⟨t, h⟩ else 1

theorem hasArr_koP {t : ℕ} (ht : t < 16) : HasArr (koP t) (koArr t) := by
  simp only [koP, ht, ↓reduceDIte]
  exact hasArr_koPerm ⟨t, ht⟩

theorem hasArr_koP_inv {t : ℕ} (ht : t < 16) : HasArr (koP t)⁻¹ (koArr t) := by
  simp only [koP, ht, ↓reduceDIte]
  exact hasArr_permOfArr_inv _

theorem koP_mem_fixO (t : ℕ) : koP t ∈ fixO := by
  unfold koP
  split_ifs with h
  · exact (mem_fixO_iff _).2 ⟨_, rfl⟩
  · exact fixO.one_mem

theorem koPerm_mem_fixO (t : Fin 16) : koPerm t ∈ fixO := (mem_fixO_iff _).2 ⟨t, rfl⟩

theorem koRho_mem_imgC_fixO (t : Fin 16) : koRho t ∈ imgC fixO :=
  ⟨⟨koPerm t, koPerm_mem_mog22 t⟩, Subgroup.mem_subgroupOf.2 (koPerm_mem_fixO t), rfl⟩

theorem mem_imgC_fixO {φ : MulAut W10} : φ ∈ imgC fixO ↔ ∃ t, koRho t = φ := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hσ)
    refine ⟨t, ?_⟩
    show rhoC10 mog22 mog22_le_mog22plus ⟨koPerm t, koPerm_mem_mog22 t⟩ = _
    exact congrArg (rhoC10 mog22 mog22_le_mog22plus) (Subtype.ext ht.symm)
  · rintro ⟨t, rfl⟩
    exact koRho_mem_imgC_fixO t

abbrev W0 : Subgroup W10 := maskSub 10 w0Basis

theorem card_W0 : Nat.card W0 = 2 ^ 5 :=
  card_maskSub w0_lt (nodup_of_nodupB _ _ w0_nodup).1

theorem z0_mem_W0 : z0 ∈ W0 := toW_mem_maskSub z0_mem_w0

theorem toW_inv (m : ℕ) : (toW 10 m)⁻¹ = toW 10 m := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := toW_xor 10 m m
  rw [Nat.xor_self, toW_zero] at h
  exact h.symm

theorem xorLin_comm (a : Array ℕ) : XorLin fun m => actC10 a m ^^^ m := fun x y => by
  show actC10 a (x ^^^ y) ^^^ (x ^^^ y) = actC10 a x ^^^ x ^^^ (actC10 a y ^^^ y)
  rw [xorLin_actC10 a x y]
  ac_rfl

theorem koRho_mem_moveSub (t : Fin 16) : koRho t ∈ moveSub W0 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  show koRho t (toW 10 m) * (toW 10 m)⁻¹ ∈ W0
  have e : koRho t (toW 10 m) * (toW 10 m)⁻¹ = toW 10 (actC10 (koArr t) m ^^^ m) := by
    rw [koRho_toW, toW_inv, toW_xor]
  rw [e]
  exact toW_mem_maskSub (mem_combos_of_xorLin (xorLin_comm (koArr t))
    (fun j hj => ko_comm_mem_w0 t t.2 j hj) m hm)

theorem imgC_fixO_le_moveSub : imgC fixO ≤ moveSub W0 := fun φ hφ => by
  obtain ⟨t, rfl⟩ := mem_imgC_fixO.1 hφ
  exact koRho_mem_moveSub t

theorem comm_mem_commV (t : ℕ) (ht : t < 16) (j : ℕ) :
    toW 10 (actC10 (koArr t) (2 ^ j) ^^^ 2 ^ j) ∈ commV (imgC fixO) := by
  have h := mem_commV (koRho_mem_imgC_fixO ⟨t, ht⟩) (toW 10 (2 ^ j))
  have e1 : toW 10 (actC10 (koArr t) (2 ^ j) ^^^ 2 ^ j) =
      koRho ⟨t, ht⟩ (toW 10 (2 ^ j)) * (toW 10 (2 ^ j))⁻¹ := by
    rw [koRho_toW, toW_inv, toW_xor]
  rw [e1]
  exact h

theorem commV_imgC_fixO : commV (imgC fixO) = W0 := by
  refine le_antisymm (commV_le_iff.2 imgC_fixO_le_moveSub) ?_
  rintro _ ⟨m, hm, rfl⟩
  refine mem_of_combos (fun m => toW 10 m ∈ commV (imgC fixO)) ?_ ?_ w0Basis ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    rw [w0Basis_eq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      exact comm_mem_commV _ (by norm_num) _

@[expose] def kcL : List (Equiv.Perm (Fin 24)) :=
  (List.range 8).map fun i => if i < 4 then ⁅koP (2 ^ i), lX⁆ else ⁅koP (2 ^ (i - 4)), lY⁆

theorem hasArr_kcL : ∀ i, HasArr (kcL.getD i 1) (((List.range 8).map kcArr).getD i idArr) := by
  intro i
  by_cases hi : i < 8
  · rw [kcL, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
    unfold kcArr
    by_cases h4 : i < 4
    · have ht : 2 ^ i < 16 := by interval_cases i <;> norm_num
      simp only [h4, ↓reduceIte]
      rw [commutatorElement_def, mul_assoc (koP (2 ^ i) * lX)]
      exact hasArr_mul (hasArr_mul (hasArr_koP ht) hasArr_lX)
        (hasArr_mul (hasArr_koP_inv ht) hasArr_lXinv)
    · have ht : 2 ^ (i - 4) < 16 := by
        have : i - 4 < 4 := by omega
        interval_cases (i - 4) <;> norm_num
      simp only [h4, ↓reduceIte]
      rw [commutatorElement_def, mul_assoc (koP (2 ^ (i - 4)) * lY)]
      exact hasArr_mul (hasArr_mul (hasArr_koP ht) hasArr_lY)
        (hasArr_mul (hasArr_koP_inv ht) hasArr_lYinv)
  · rw [kcL, List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by simpa using hi)]
    exact hasArr_one

theorem commutator_fixO_L22 : ⁅fixO, L22⁆ = fixO := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro k hk l hl
    have h1 : l * k⁻¹ * l⁻¹ ∈ fixO :=
      (Subgroup.mem_normalizer_iff.1 (L22_le_normalizer_fixO hl) k⁻¹).1 (fixO.inv_mem hk)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact fixO.mul_mem hk (by simpa [mul_assoc] using h1)
  · intro σ hσ
    obtain ⟨t, rfl⟩ := (mem_fixO_iff σ).1 hσ
    have h := hasArr_wPerm hasArr_kcL (koComm t)
    rw [koComm_ok t t.2] at h
    rw [perm_eq_of_hasArr (hasArr_koPerm t) h]
    refine wPerm_mem (fun p hp => ?_) _
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    by_cases h4 : k < 4
    · simp only [h4, ↓reduceIte]
      exact Subgroup.commutator_mem_commutator (koP_mem_fixO _) lX_mem_L22
    · simp only [h4, ↓reduceIte]
      exact Subgroup.commutator_mem_commutator (koP_mem_fixO _) lY_mem_L22

theorem commutator_imgC_fixO_L22 : ⁅imgC fixO, imgC L22⁆ = imgC fixO := by
  have h : ⁅fixO.subgroupOf mog22, L22.subgroupOf mog22⁆ = fixO.subgroupOf mog22 := by
    apply Subgroup.map_injective mog22.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le L22_le,
      Subgroup.map_subgroupOf_eq_of_le fixO_le_mog22, commutator_fixO_L22]
  rw [imgC, imgC, ← Subgroup.map_commutator, h]

theorem koRho_mul (c d : Fin 16) :
    koRho c * koRho d = koRho ⟨c.val ^^^ d.val, Nat.xor_lt_two_pow (n := 4) c.2 d.2⟩ := by
  rw [koRho, koRho, ← map_mul]
  refine congrArg _ (Subtype.ext ?_)
  show koPerm c * koPerm d = koPerm _
  rw [koPerm_mul]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 4) c.2 d.2))

theorem rho_lX_mem : rhoC10 mog22 mog22_le_mog22plus ⟨lX, lX_mem⟩ ∈ imgC L22 :=
  ⟨⟨lX, lX_mem⟩, Subgroup.mem_subgroupOf.2 lX_mem_L22, rfl⟩

theorem rho_lY_mem : rhoC10 mog22 mog22_le_mog22plus ⟨lY, lY_mem⟩ ∈ imgC L22 :=
  ⟨⟨lY, lY_mem⟩, Subgroup.mem_subgroupOf.2 lY_mem_L22, rfl⟩

theorem koAct_lt (g : ℕ) {d : ℕ} (hd : d < 16) : koAct g d < 16 := by
  unfold koAct
  split_ifs
  · exact (actM_ko_lt d hd).1
  · exact (actM_ko_lt d hd).2

theorem conj_koPerm_x (c : Fin 16) :
    lX * koPerm c * lX⁻¹ = koPerm ⟨actM mxCols c, (actM_ko_lt c c.2).1⟩ := by
  have h : HasArr (lX * koPerm c * lX⁻¹) (cArr lxArr (cArr (koArr c) lxInv)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_lX (hasArr_mul (hasArr_koPerm c) hasArr_lXinv)
  rw [(ko_conj c c.2).1] at h
  exact perm_eq_of_hasArr h (hasArr_koPerm _)

theorem conj_koPerm_y (c : Fin 16) :
    lY * koPerm c * lY⁻¹ = koPerm ⟨actM myCols c, (actM_ko_lt c c.2).2⟩ := by
  have h : HasArr (lY * koPerm c * lY⁻¹) (cArr lyArr (cArr (koArr c) lyInv)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_lY (hasArr_mul (hasArr_koPerm c) hasArr_lYinv)
  rw [(ko_conj c c.2).2] at h
  exact perm_eq_of_hasArr h (hasArr_koPerm _)

theorem rho_conj_koRho (g : ℕ) (c : Fin 16) :
    ∃ x ∈ imgC L22, x * koRho c * x⁻¹ = koRho ⟨koAct g c, koAct_lt g c.2⟩ := by
  by_cases hg : g = 0
  · refine ⟨_, rho_lX_mem, ?_⟩
    rw [koRho, koRho, ← map_inv, ← map_mul, ← map_mul]
    refine congrArg _ (Subtype.ext ?_)
    show lX * koPerm c * lX⁻¹ = _
    rw [conj_koPerm_x]
    congr 1
    exact Fin.ext (by simp [koAct, hg])
  · refine ⟨_, rho_lY_mem, ?_⟩
    rw [koRho, koRho, ← map_inv, ← map_mul, ← map_mul]
    refine congrArg _ (Subtype.ext ?_)
    show lY * koPerm c * lY⁻¹ = _
    rw [conj_koPerm_y]
    congr 1
    exact Fin.ext (by simp [koAct, hg])

theorem koRho_zero : koRho 0 = 1 := by
  rw [koRho]
  have h0 : (⟨koPerm 0, koPerm_mem_mog22 0⟩ : ↥mog22) = 1 := Subtype.ext koPerm_zero
  rw [h0, map_one]

theorem eq_of_le_imgC_fixO {N : Subgroup (MulAut W10)} (hN : N ≤ imgC fixO) (h1 : N ≠ ⊥)
    (hP : imgC L22 ≤ Subgroup.normalizer (N : Set (MulAut W10))) : N = imgC fixO := by
  obtain ⟨⟨φ, hφ⟩, hφ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h1
  have hφ1 : φ ≠ 1 := fun h => hφ1' (Subtype.ext h)
  obtain ⟨c, hc⟩ := mem_imgC_fixO.1 (hN hφ)
  let P : ℕ → Prop := fun d => ∃ hd : d < 16, koRho ⟨d, hd⟩ ∈ N
  have P0 : P 0 := ⟨by norm_num, by
    rw [show (⟨0, by norm_num⟩ : Fin 16) = 0 from rfl, koRho_zero]
    exact N.one_mem⟩
  have Pxor : ∀ a b, P a → P b → P (a ^^^ b) := by
    rintro a b ⟨ha, hNa⟩ ⟨hb, hNb⟩
    refine ⟨Nat.xor_lt_two_pow (n := 4) ha hb, ?_⟩
    have := N.mul_mem hNa hNb
    rwa [koRho_mul] at this
  have Pact : ∀ g d, P d → P (koAct g d) := by
    rintro g d ⟨hd, hNd⟩
    obtain ⟨x, hx, hxe⟩ := rho_conj_koRho g ⟨d, hd⟩
    refine ⟨koAct_lt g hd, ?_⟩
    rw [← hxe]
    exact (Subgroup.mem_normalizer_iff.1 (hP hx) _).1 hNd
  have hc0 : c.val ≠ 0 := by
    intro h
    apply hφ1
    rw [← hc, show c = 0 from Fin.ext h, koRho_zero]
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (irrK_cover c c.2 hc0)
  have hall : ∀ d ∈ derivB koAct [e.1] e.2, P d := by
    refine mem_of_derivB koAct P Pact P0 e.2 [e.1] fun d hd => ?_
    rw [List.mem_singleton] at hd
    rw [hd, he1]
    exact ⟨c.2, hc ▸ hφ⟩
  refine le_antisymm hN fun ψ hψ => ?_
  obtain ⟨d, rfl⟩ := mem_imgC_fixO.1 hψ
  obtain ⟨_, h⟩ := mem_of_combos P P0 Pxor _ hall d (irrK_ok e he d d.2)
  exact h

theorem rho_lAct (g m : ℕ) : ∃ x ∈ imgC L22, x (toW 10 m) = toW 10 (lAct g m) := by
  by_cases hg : g = 0
  · refine ⟨_, rho_lX_mem, ?_⟩
    rw [rhoC10_toW mog22 mog22_le_mog22plus ⟨lX, lX_mem⟩ hasArr_lX m, lAct, ite_eq_left hg]
  · refine ⟨_, rho_lY_mem, ?_⟩
    rw [rhoC10_toW mog22 mog22_le_mog22plus ⟨lY, lY_mem⟩ hasArr_lY m, lAct, ite_eq_right hg]

theorem eq_W0_of_lt {Y : Subgroup W10} (h1 : Subgroup.zpowers z0 < Y) (h2 : Y ≤ W0)
    (h3 : imgC L22 ≤ stabSub Y) : Y = W0 := by
  obtain ⟨y, hyY, hyz⟩ := IsConcreteLE.exists_of_lt h1
  obtain ⟨m, hm, rfl⟩ := h2 hyY
  have hm0 : m ≠ 0 := fun h => hyz (by rw [h, toW_zero]; exact Subgroup.one_mem _)
  have hm1 : m ≠ 1 := fun h => hyz (by rw [h]; exact Subgroup.mem_zpowers _)
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (irrW_cover m hm hm0 hm1)
  let P : ℕ → Prop := fun k => k < 2 ^ 10 ∧ toW 10 k ∈ Y
  have Pact : ∀ g k, P k → P (lAct g k) := by
    rintro g k ⟨-, hk⟩
    refine ⟨by unfold lAct; exact actC10_lt _ _, ?_⟩
    obtain ⟨x, hx, hxe⟩ := rho_lAct g k
    rw [← hxe]
    exact ((h3 hx) _).2 hk
  have P0 : P 0 := ⟨by norm_num, by rw [toW_zero]; exact Y.one_mem⟩
  have hstart : ∀ k ∈ [e.1, 1], P k := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · rw [he1]
      exact ⟨combos_lt w0_lt _ hm, hyY⟩
    · exact ⟨by norm_num, h1.le (Subgroup.mem_zpowers _)⟩
  have hall := mem_of_derivB lAct P Pact P0 e.2 _ hstart
  have hcard := (MaskCoords.std 10).pow_le_card Y (derivB lAct [e.1, 1] e.2)
    (nodup_of_nodupB _ _ (irrW_ok e he).1).1 (fun a ha => (hall a ha).1)
    (fun a ha => (hall a ha).2)
  rw [(irrW_ok e he).2] at hcard
  exact Subgroup.eq_of_le_of_card_ge h2 (by rw [card_W0]; exact hcard)

theorem fix_imgC_fixO (w : W10) (hw : w ∈ fixV (imgC fixO)) : w = 1 ∨ w = z0 :=
  (fix_koRho w).1 ⟨hw _ (koRho_mem_imgC_fixO 1), hw _ (koRho_mem_imgC_fixO 2),
    hw _ (koRho_mem_imgC_fixO 4), hw _ (koRho_mem_imgC_fixO 8)⟩

theorem W0_inf_fixV : W0 ⊓ fixV (imgC fixO) = Subgroup.zpowers z0 := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨-, hv⟩
    rcases fix_imgC_fixO v hv with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨z0_mem_W0, fun φ hφ => ?_⟩
    obtain ⟨t, rfl⟩ := mem_imgC_fixO.1 hφ
    exact (koRho_toW t 1).trans (congrArg (toW 10) (ko_fix t t.2))

theorem commV_imgC_L22 : commV (imgC L22) = ⊤ := by
  have hl : ∀ a ∈ cvData.map (fun e => lAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2),
      (MaskCoords.std 10).vm a ∈ commV (imgC L22) := by
    intro a ha
    obtain ⟨⟨g, j⟩, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, hx, hxe⟩ := rho_lAct g (2 ^ j)
    have h := mem_commV hx (toW 10 (2 ^ j))
    show toW 10 (lAct g (2 ^ j) ^^^ 2 ^ j) ∈ commV (imgC L22)
    have e1 : toW 10 (lAct g (2 ^ j) ^^^ 2 ^ j) = x (toW 10 (2 ^ j)) * (toW 10 (2 ^ j))⁻¹ := by
      rw [hxe, toW_inv, toW_xor]
    rw [e1]
    exact h
  have hlt : ∀ a ∈ cvData.map (fun e => lAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2), a < 2 ^ 10 := by
    intro a ha
    obtain ⟨⟨g, j⟩, hgj, rfl⟩ := List.mem_map.1 ha
    have hcv : ∀ e ∈ cvData, e.2 < 10 := by decide
    have hj : j < 10 := hcv _ hgj
    exact Nat.xor_lt_two_pow (by unfold lAct; exact actC10_lt _ _)
      (Nat.pow_lt_pow_right (by norm_num) hj)
  have hcard := (MaskCoords.std 10).pow_le_card _ _ (nodup_of_nodupB _ _ cv_ok.1).1 hlt hl
  rw [List.length_map, cv_ok.2] at hcard
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [Nat.card_eq_fintype_card, card_Wn]
  exact hcard

theorem parZ_std :
    parZ (imgC mog22) z0 = imgC L22 :=
  perfectCore_stab

theorem radZ_std :
    radZ (imgC mog22) z0 = imgC fixO := by
  show pCoreOf 2 (parZ (imgC mog22) z0) = _
  rw [parZ_std]
  exact pCoreOf_imgC_L22

theorem vZ_std :
    vZ (imgC mog22) z0 = W0 := by
  show commV (radZ (imgC mog22) z0) = _
  rw [radZ_std]
  exact commV_imgC_fixO

theorem hzConcl_std :
    HZConcl (imgC mog22) z0 4 := by
  unfold HZConcl
  rw [vZ_std, radZ_std, parZ_std]
  exact ⟨card_W0, card_imgC_fixO, commutator_imgC_fixO_L22,
    fun N h1 h2 h3 => eq_of_le_imgC_fixO h1 h2 h3, fun Y h1 h2 h3 => eq_W0_of_lt h1 h2 h3,
    W0_inf_fixV, commV_imgC_L22⟩

theorem isPGroup_imgC_fixO : IsPGroup 2 ↥(imgC fixO) :=
  (isPGroup_fixO.of_equiv (Subgroup.subgroupOfEquivOfLe fixO_le_mog22).symm).map _

theorem imgC_fixO_le : imgC fixO ≤ imgC mog22 :=
  Subgroup.map_mono fun σ _ => Subgroup.mem_subgroupOf.2 σ.2

theorem exists_equiv_z0 {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : ∃ e : V ≃* W10, H.map (congrHom e) = imgC mog22 ∧ e z = z0 := by
  obtain ⟨e₀, he₀⟩ := code22_std h
  have he₀' : H.map (congrHom e₀) = imgC mog22 := he₀.trans range_rhoC10_eq_imgC
  have hcH : Nat.card ↥(imgC mog22) = Nat.card ↥H := by
    rw [← he₀']
    exact card_map_congrHom e₀ H
  have hS' : Nat.card ↥(S.map (congrHom e₀)) =
      2 ^ (Nat.card ↥(imgC mog22)).factorization 2 := by
    rw [hcH, ← hS]
    exact card_map_congrHom e₀ S
  have hSH' : S.map (congrHom e₀) ≤ imgC mog22 := by
    rw [← he₀']
    exact Subgroup.map_mono hSH
  have hz' : e₀ z ∈ fixV (S.map (congrHom e₀)) := by
    rintro _ ⟨y, hy, rfl⟩
    show e₀ (y (e₀.symm (e₀ z))) = e₀ z
    rw [MulEquiv.symm_apply_apply, hzS y hy]
  have hz1' : e₀ z ≠ 1 := fun h' => hz1 (e₀.injective (h'.trans (map_one e₀).symm))
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_of_fixV hSH' hS' imgC_fixO_le isPGroup_imgC_fixO
    fix_imgC_fixO hz' hz1'
  exact exists_equiv_std e₀ he₀' hg hgz

theorem hzConcl_of_code22
    {V : Type} [CommGroup V]
    [Finite V] {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : HZConcl H z 4 := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  have key : ∀ (A : Subgroup (MulAut W10)) (w : W10), A = imgC mog22 → w = z0 →
      HZConcl A w 4 := by
    rintro A w rfl rfl
    exact hzConcl_std
  exact HZConcl.of_map e (key _ _ he hez)

end CFSG.Quasithin.H.Code22
