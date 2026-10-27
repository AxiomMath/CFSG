module

public import CFSG.Quasithin.H13.AS91Sec5ToddDefs
public import CFSG.Quasithin.H13.AS91Sec3Delta
public import CFSG.Quasithin.H13.AS91Sec3Dual
public import Certificates.Certificate89019

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem sum_smul_finset_perm (σ : S24) (O : Finset (Fin 24)) (x : Fin 24 → ZMod 2) :
    ∑ i ∈ σ • O, x (σ⁻¹ i) = ∑ j ∈ O, x j := by
  rw [Finset.smul_finset_def, Finset.sum_image (fun a _ b _ h => MulAction.injective σ h)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Equiv.Perm.smul_def]

private theorem sum_eq_dot_eY (c : Fin 24 → ZMod 2) (Y : Finset (Fin 24)) :
    ∑ i ∈ Y, c i = c ⬝ᵥ Multiplicative.toAdd (eY Y) := by
  classical
  simp only [dotProduct, toAdd_eY, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

private theorem toAdd_lift (v : W11) :
    Multiplicative.toAdd (cocodeCoords.lift v) = liftE (Multiplicative.toAdd v) := rfl

private theorem rho11_apply (σ : ↥AutPerm) (w : W11) :
    rho11 AutPerm le_rfl σ w = cocodeCoords.κ (G6.permAct 24 σ (cocodeCoords.lift w)) := rfl

theorem octFun_smul {σ : S24} (hσ : σ ∈ M24g) {O : Finset (Fin 24)} (hO : IsOctad O) (w : W11) :
    octFun (σ • O) (rho11 AutPerm le_rfl ⟨σ, hσ⟩ w) = octFun O w := by
  have hσ' : σ ∈ AutPerm := hσ
  obtain ⟨m, hm⟩ : ∃ m, m = G6.permAct 24 σ (cocodeCoords.lift w) := ⟨_, rfl⟩
  have hmE : m ∈ G6.coreMod 24 := hm ▸ (preserves_cocode hσ').1 _ (cocodeCoords.lift_mem w)
  have hc := cocodeCoords.mul_lift_inv_mem hmE
  have hrho : rho11 AutPerm le_rfl ⟨σ, hσ⟩ w = cocodeCoords.κ m := by
    rw [rho11_apply, hm]
  have hcC : Multiplicative.toAdd (m * (cocodeCoords.lift (cocodeCoords.κ m))⁻¹) ∈ C :=
    (mem_golayC_iff' _).1 hc
  have hOσ : IsOctad (σ • O) := (isOctad_smul_iff hσ).2 hO
  have hdot : ∑ i ∈ σ • O, Multiplicative.toAdd
      (m * (cocodeCoords.lift (cocodeCoords.κ m))⁻¹) i = 0 := by
    rw [sum_eq_dot_eY]
    exact dotProduct_eq_zero hcC ((mem_golayC_iff' _).1 hOσ.2)
  have h1 : ∀ i, liftE (Multiplicative.toAdd (cocodeCoords.κ m)) i =
      Multiplicative.toAdd m i - Multiplicative.toAdd
        (m * (cocodeCoords.lift (cocodeCoords.κ m))⁻¹) i := by
    intro i
    have e : Multiplicative.toAdd (m * (cocodeCoords.lift (cocodeCoords.κ m))⁻¹) i =
        Multiplicative.toAdd m i - liftE (Multiplicative.toAdd (cocodeCoords.κ m)) i := by
      simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
      rfl
    rw [e]
    exact (sub_sub_cancel _ _).symm
  have h2 : ∀ i, Multiplicative.toAdd m i = Multiplicative.toAdd (cocodeCoords.lift w) (σ⁻¹ i) := by
    intro i
    rw [hm, G6.permAct_apply]
  rw [hrho, octFun_def, octFun_def]
  calc ∑ i ∈ σ • O, liftE (Multiplicative.toAdd (cocodeCoords.κ m)) i
      = ∑ i ∈ σ • O, (Multiplicative.toAdd m i - Multiplicative.toAdd
          (m * (cocodeCoords.lift (cocodeCoords.κ m))⁻¹) i) :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ i ∈ σ • O, Multiplicative.toAdd m i - ∑ i ∈ σ • O, Multiplicative.toAdd
          (m * (cocodeCoords.lift (cocodeCoords.κ m))⁻¹) i := Finset.sum_sub_distrib _ _
    _ = ∑ i ∈ σ • O, Multiplicative.toAdd m i - 0 := by rw [hdot]
    _ = ∑ i ∈ σ • O, Multiplicative.toAdd m i := sub_zero _
    _ = ∑ i ∈ σ • O, Multiplicative.toAdd (cocodeCoords.lift w) (σ⁻¹ i) :=
        Finset.sum_congr rfl fun i _ => h2 i
    _ = ∑ j ∈ O, Multiplicative.toAdd (cocodeCoords.lift w) j := sum_smul_finset_perm σ O _
    _ = ∑ j ∈ O, liftE (Multiplicative.toAdd w) j :=
        Finset.sum_congr rfl fun j _ => by rw [toAdd_lift]

theorem mem_annOf_smul {σ : S24} (hσ : σ ∈ M24g) {S : Finset (Finset (Fin 24))}
    (hS : ∀ O ∈ S, IsOctad O) (w : W11) :
    rho11 AutPerm le_rfl ⟨σ, hσ⟩ w ∈ annOf (σ • S) ↔ w ∈ annOf S := by
  rw [mem_annOf, mem_annOf]
  constructor
  · intro h O hO
    rw [← octFun_smul hσ (hS O hO) w]
    exact h _ (Finset.smul_mem_smul_finset hO)
  · intro h O' hO'
    obtain ⟨O, hO, rfl⟩ := Finset.mem_smul_finset.1 hO'
    rw [octFun_smul hσ (hS O hO) w]
    exact h O hO

private theorem annOf_smul {σ : S24} (hσ : σ ∈ M24g) {S : Finset (Finset (Fin 24))}
    (hS : ∀ O ∈ S, IsOctad O) :
    annOf (σ • S) = (annOf S).map (rho11 AutPerm le_rfl ⟨σ, hσ⟩).toMonoidHom := by
  ext W
  rw [Subgroup.mem_map]
  constructor
  · intro hW
    refine ⟨(rho11 AutPerm le_rfl ⟨σ, hσ⟩).symm W, ?_, by simp⟩
    rw [← mem_annOf_smul hσ hS]
    simpa using hW
  · rintro ⟨w, hw, rfl⟩
    exact (mem_annOf_smul hσ hS w).2 hw

private theorem card_annOf_smul {σ : S24} (hσ : σ ∈ M24g) {S : Finset (Finset (Fin 24))}
    (hS : ∀ O ∈ S, IsOctad O) : Nat.card (annOf (σ • S)) = Nat.card (annOf S) := by
  rw [annOf_smul hσ hS]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

private theorem card_annOf_inf_smul {σ : S24} (hσ : σ ∈ M24g) {l k : Finset (Finset (Fin 24))}
    (hl : ∀ O ∈ l, IsOctad O) (hk : ∀ O ∈ k, IsOctad O) :
    Nat.card ↥(annOf (σ • l) ⊓ annOf (σ • k)) = Nat.card ↥(annOf l ⊓ annOf k) := by
  rw [annOf_smul hσ hl, annOf_smul hσ hk, ← Subgroup.map_inf _ _ _ (MulEquiv.injective _)]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

private theorem toddPopc_eq (k a : ℕ) : Native.toddPopc k a = popc k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [Native.toddPopc, popc, ih]

private theorem toddEven_iff (k a : ℕ) :
    Native.toddEven k a = true ↔ ((popc k a : ℕ) : ZMod 2) = 0 := by
  rw [Native.toddEven, toddPopc_eq, ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  simp

private theorem octFun_maskFin_toW (o m : ℕ) :
    octFun (maskFin o) (toW 11 m) = ((popc 24 (o &&& actM liftECols m) : ℕ) : ZMod 2) := by
  rw [octFun_def, toAdd_toW, liftE_bvec, ← bvec_dotProduct]
  simp only [dotProduct, bvec_apply, maskFin]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : o.testBit i = true <;> simp [h]

private theorem toddOct_iff (o m : ℕ) :
    Native.toddOct o m = true ↔ octFun (maskFin o) (toW 11 m) = 0 := by
  have e : Native.actM Native.liftEColsN m = actM liftECols m := actM_eq_actM _ _
  rw [octFun_maskFin_toW, Native.toddOct, toddEven_iff, e]

private theorem toddOrth_iff (u m : ℕ) :
    Native.toddOrth u m = true ↔ ((popc 11 (u &&& m) : ℕ) : ZMod 2) = 0 := toddEven_iff 11 _

private theorem img_eq_permM {a : Array ℕ} {σ : Equiv.Perm (Fin 24)} (h : RepT a σ) (x : ℕ) :
    Native.img a x = permM a x := by
  have hasarr : HasArr σ a := fun i => (h i).symm
  have hlt : permM a x < 2 ^ 24 := by
    refine actM_lt (cs := permCols a) (fun c hc => ?_) x
    simp only [permCols, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have hj' : a[j]! < 24 := by
      have h1 := h ⟨j, hj⟩
      simp only at h1
      rw [h1]
      exact (σ ⟨j, hj⟩).2
    exact Nat.pow_lt_pow_right (by norm_num) hj'
  apply bvec_inj (img_lt h x) hlt
  rw [← permWord_bvec hasarr x]
  funext i
  have key : (Native.img a x).testBit i = x.testBit ((σ⁻¹ i : Fin 24) : ℕ) := by
    rw [Bool.eq_iff_iff, testBit_img]
    constructor
    · rintro ⟨i', hi', hx, hai⟩
      have h1 := h ⟨i', hi'⟩
      simp only at h1
      have h2 : σ ⟨i', hi'⟩ = i := Fin.ext (h1.symm.trans hai)
      have h3 : (σ⁻¹ i : Fin 24) = ⟨i', hi'⟩ := by rw [← h2]; simp
      rw [h3]
      exact hx
    · intro hx
      refine ⟨((σ⁻¹ i : Fin 24) : ℕ), (σ⁻¹ i).2, hx, ?_⟩
      rw [h (σ⁻¹ i)]
      simp
  simp only [bvec_apply, permWord, Function.comp_apply, key]

private theorem toddAct_eq {a : Array ℕ} {σ : Equiv.Perm (Fin 24)} (h : RepT a σ) (m : ℕ) :
    Native.toddAct a m = act11 a m := by
  have e1 : Native.actM Native.liftEColsN m = actM liftECols m := actM_eq_actM _ _
  rw [Native.toddAct, img_eq_permM h, e1, actM_eq_actM, act11]
  rfl

private theorem rho11_of_repT (j : Fin 4) {a : Array ℕ} (h : RepT a (lPerm j)) (m : ℕ) :
    rho11 AutPerm le_rfl ⟨lPerm j, lPerm_mem j⟩ (toW 11 m) = toW 11 (Native.toddAct a m) := by
  rw [toddAct_eq h]
  exact rho11_toW AutPerm le_rfl ⟨lPerm j, lPerm_mem j⟩ (fun i => (h i).symm) m

private theorem mem_annOf_toFinset_map (os : List ℕ) (m : ℕ) :
    toW 11 m ∈ annOf ((os.map maskFin).toFinset) ↔ Native.toddOctsKer os m = true := by
  rw [mem_annOf, Native.toddOctsKer, List.all_eq_true]
  constructor
  · intro h o ho
    exact (toddOct_iff o m).2 (h _ (List.mem_toFinset.2 (List.mem_map.2 ⟨o, ho, rfl⟩)))
  · intro h O hO
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hO)
    exact (toddOct_iff o m).1 (h o ho)

private theorem card_eq_filter (U : Subgroup W11) (P : ℕ → Bool)
    (hP : ∀ m < 2048, toW 11 m ∈ U ↔ P m = true) :
    Nat.card U = ((List.range 2048).filter P).length := by
  have h := (MaskCoords.std 11).card_eq U P (fun m hm => hP m (by simpa using hm))
  simpa using h

private theorem card_annOf_toFinset_map (os : List ℕ) :
    Nat.card (annOf ((os.map maskFin).toFinset)) =
      ((List.range 2048).filter (Native.toddOctsKer os)).length :=
  card_eq_filter _ _ fun m _ => mem_annOf_toFinset_map os m

section Spec

private theorem toddCheck_true : Native.toddCheck () = true :=
  Certificates.certificate89019

private theorem toddUniqCheck_true :
    Native.toddUniqCheck () = true := by
  have h := toddCheck_true
  simp only [Native.toddCheck, Bool.and_eq_true] at h
  exact h.1.1

private theorem toddIntCheck_true :
    Native.toddIntCheck () = true := by
  have h := toddCheck_true
  simp only [Native.toddCheck, Bool.and_eq_true] at h
  exact h.1.2

private theorem toddSextCheck_true :
    Native.toddSextCheck () = true := by
  have h := toddCheck_true
  simp only [Native.toddCheck, Bool.and_eq_true] at h
  exact h.2

private theorem getElem!_toddActTab (a : Array ℕ) {w : ℕ} (hw : w < 2048) :
    ((Array.range 2048).map (Native.toddAct a))[w]! = Native.toddAct a w := by
  rw [getElem!_pos _ _ (by simpa using hw)]
  simp

private theorem toddKerT_iff {u w : ℕ} (hw : w < 2048) :
    Native.toddKerT (Native.toddActTabs ()) u w = true ↔
      Native.toddOrth u w = true ∧
        ∀ a ∈ Native.lTabs, Native.toddOrth u (Native.toddAct a w) = true := by
  unfold Native.toddKerT Native.toddActTabs
  rw [Bool.and_eq_true, List.all_eq_true]
  refine and_congr Iff.rfl ?_
  rw [List.forall_mem_map]
  refine forall₂_congr fun a _ => ?_
  rw [getElem!_toddActTab a hw]

private theorem toddUniq_spec {u : ℕ} (hu0 : 0 < u)
    (hu : u < 2048) :
    ((List.range 2048).filter (Native.toddKerT (Native.toddActTabs ()) u)).length < 512 ∨
      ∀ w < 2048, Native.toddKerT (Native.toddActTabs ()) u w = true →
        Native.toddOctsKer (Native.octsT Native.baseTrio) w = true := by
  have h := toddUniqCheck_true
  unfold Native.toddUniqCheck Native.toddUniqLoop at h
  rw [List.all_eq_true] at h
  have h1 := h u (List.mem_range.2 hu)
  rw [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · omega
  · unfold Native.toddUniqRow at h1
    rw [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · refine Or.inr fun w hw hk => ?_
      have h2 := h1 w (List.mem_range.2 hw)
      rw [Bool.or_eq_true, Bool.not_eq_true'] at h2
      rcases h2 with h2 | h2
      · rw [hk] at h2
        exact absurd h2 (by simp)
      · exact h2

private theorem mem_annOf_trioFin (k m : ℕ) :
    toW 11 m ∈ annOf (trioFin k) ↔
      Native.toddOctsKer (Native.octsT (Native.trioList ())[k]!) m = true := by
  rw [trioFin_eq_toFinset]
  exact mem_annOf_toFinset_map _ _

private theorem mem_annOf_trioFin_zero (m : ℕ) :
    toW 11 m ∈ annOf (trioFin 0) ↔
      Native.toddOctsKer (Native.octsT Native.baseTrio) m = true := by
  rw [mem_annOf_trioFin, trioList_zero]

private theorem card_inf_trioFin (k : ℕ) :
    Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin k)) =
      (((List.range 2048).filter (Native.toddOctsKer (Native.octsT Native.baseTrio))).filter
        (Native.toddOctsKer (Native.octsT (Native.trioList ())[k]!))).length := by
  rw [List.filter_filter]
  refine card_eq_filter _ _ fun m _ => ?_
  rw [Subgroup.mem_inf, mem_annOf_trioFin_zero, mem_annOf_trioFin, Bool.and_eq_true]
  exact and_comm

private theorem card_annOf_trioFin_zero :
    Nat.card (annOf (trioFin 0)) = 512 := by
  have h := toddIntCheck_true
  simp only [Native.toddIntCheck, Bool.and_eq_true, beq_iff_eq] at h
  have e : Nat.card (annOf (trioFin 0)) = ((List.range 2048).filter
      (Native.toddOctsKer (Native.octsT Native.baseTrio))).length :=
    card_eq_filter _ _ fun m _ => mem_annOf_trioFin_zero m
  rw [e]
  exact h.1

private theorem toddInt_facts :
    (Delta (trioFin 0) (trioFin 267) 1 ∧
        Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin 267)) = 256) ∧
      (Delta (trioFin 0) (trioFin 23) 2 ∧
        Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin 23)) = 128) ∧
      (Delta (trioFin 0) (trioFin 22) 3 ∧
        Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin 22)) = 128) ∧
      (Delta (trioFin 0) (trioFin 1) 4 ∧
        Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin 1)) = 128) := by
  have h := toddIntCheck_true
  simp only [Native.toddIntCheck, Native.toddIntReps, Native.toddInterCount, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨-, hm1, hc1, hm2, ht1, ht2, hc2, hz3, hc3, hz4, hc4⟩ := h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show trioFin 267 ≠ trioFin 0 ∧ ¬ Disjoint (trioFin 267) (trioFin 0)
    refine ⟨fun h => absurd (trioFin_injective (by norm_num) (by norm_num) h) (by norm_num),
      (meets_iff (by norm_num) (by norm_num)).1 hm1⟩
  · rw [card_inf_trioFin]
    exact hc1
  · show Disjoint (trioFin 23) (trioFin 0) ∧ Coplanar (trioFin 0) (trioFin 23)
    refine ⟨?_, sextFin 1293, isSextet_sextFin (by norm_num),
      (trioIn_iff (by norm_num) (by norm_num)).1 ht1,
      (trioIn_iff (by norm_num) (by norm_num)).1 ht2⟩
    by_contra hd
    have := (meets_iff (p := 0) (p' := 23) (by norm_num) (by norm_num)).2 hd
    rw [hm2] at this
    exact absurd this (by simp)
  · rw [card_inf_trioFin]
    exact hc2
  · show ((trioFin 22).filter (InZeta (trioFin 0))).card = 1
    rw [← zc_eq (by norm_num) (by norm_num)]
    exact hz3
  · rw [card_inf_trioFin]
    exact hc3
  · show ((trioFin 1).filter (InZeta (trioFin 0))).card = 0
    rw [← zc_eq (by norm_num) (by norm_num)]
    exact hz4
  · rw [card_inf_trioFin]
    exact hc4

private theorem toddSext_facts :
    Nat.card (annOf (octsOf (sextFin 0))) = 128 ∧
      ∀ q < 1771, q ≠ 0 →
        ∃ W : W11, W ∈ annOf (octsOf (sextFin 0)) ∧ W ∉ annOf (octsOf (sextFin q)) := by
  have h := toddSextCheck_true
  unfold Native.toddSextCheck Native.toddSextLoop at h
  rw [Bool.and_eq_true, beq_iff_eq, Native.allLt_iff] at h
  obtain ⟨hK, hq⟩ := h
  have hmem : ∀ q < 1771, ∀ m, toW 11 m ∈ annOf (octsOf (sextFin q)) ↔
      Native.toddOctsKer (Native.octsS (Native.sextList ())[q]!) m = true := by
    intro q hq m
    rw [octsOf_sextFin hq]
    exact mem_annOf_toFinset_map _ _
  refine ⟨?_, fun q hq1 hq0 => ?_⟩
  · rw [octsOf_sextFin (by norm_num), card_annOf_toFinset_map]
    exact hK
  · have h1 := hq q hq1
    rw [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hq0
    · rw [List.any_eq_true] at h1
      obtain ⟨w, hw, hw2⟩ := h1
      rw [List.mem_filter, List.mem_range] at hw
      refine ⟨toW 11 w, (hmem 0 (by norm_num) w).2 hw.2, fun hW => ?_⟩
      rw [hmem q hq1] at hW
      rw [hW] at hw2
      exact absurd hw2 (by simp)

end Spec

private theorem exists_functional (A : Subgroup W11) (hA : Nat.card A = 512) :
    ∃ u, 0 < u ∧ u < 2048 ∧ ∀ m < 2048, toW 11 m ∈ A → Native.toddOrth u m = true := by
  let P : Submodule (ZMod 2) (Fin 11 → ZMod 2) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ A}
      add_mem' := fun ha hb => A.mul_mem ha hb
      zero_mem' := A.one_mem
      smul_mem' := fun c v hv => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · simpa using A.one_mem
        · simpa using hv }
  have hP : ∀ v, v ∈ P ↔ Multiplicative.ofAdd v ∈ A := fun v => Iff.rfl
  have hlt : P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    have hAtop : A = ⊤ := by
      rw [eq_top_iff]
      intro w _
      have hw : Multiplicative.toAdd w ∈ P := by rw [htop]; trivial
      exact (hP _).1 hw
    have hcard : Nat.card W11 = 2 ^ 11 := by
      rw [Nat.card_eq_fintype_card]
      exact card_Wn 11
    rw [hAtop, Subgroup.card_top, hcard] at hA
    norm_num at hA
  obtain ⟨f, hf0, hPf⟩ := Submodule.exists_le_ker_of_lt_top P hlt
  obtain ⟨u, hu, huv⟩ :=
    toW_surj 11 (Multiplicative.ofAdd (fun j => f (fun k => if j = k then 1 else 0)))
  have hbu : bvec 11 u = fun j => f (fun k => if j = k then 1 else 0) :=
    congrArg Multiplicative.toAdd huv
  have hfx : ∀ x : Fin 11 → ZMod 2, f x = ∑ j, x j * bvec 11 u j := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp only [hbu, smul_eq_mul]
  have hfm : ∀ m, f (bvec 11 m) = ((popc 11 (u &&& m) : ℕ) : ZMod 2) := by
    intro m
    rw [hfx, ← bvec_dotProduct, dotProduct_comm]
    rfl
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hf0
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, -, hm⟩ := toW_surj 11 (Multiplicative.ofAdd x)
    have hx : bvec 11 m = x := congrArg Multiplicative.toAdd hm
    rw [← hx, hfm]
    simp [popc]
  refine ⟨u, Nat.pos_of_ne_zero hu0, by simpa using hu, fun m hm hmA => ?_⟩
  have hmP : bvec 11 m ∈ P := hmA
  have h0 : f (bvec 11 m) = 0 := LinearMap.mem_ker.1 (hPf hmP)
  rw [hfm] at h0
  exact (toddOrth_iff u m).2 h0

private theorem eq_annOf_base
    (A : Subgroup W11) (hA : Nat.card A = 512)
    (hinv : ∀ j : Fin 4, ∀ w ∈ A, rho11 AutPerm le_rfl ⟨lPerm j, lPerm_mem j⟩ w ∈ A) :
    A = annOf (trioFin 0) := by
  classical
  obtain ⟨u, hu0, hu, huA⟩ := exists_functional A hA
  have hker : ∀ m < 2048, toW 11 m ∈ A →
      Native.toddKerT (Native.toddActTabs ()) u m = true := by
    intro m hm hmA
    rw [toddKerT_iff hm]
    refine ⟨huA m hm hmA, fun a ha => ?_⟩
    obtain ⟨j, hj⟩ := exists_repT_of_mem_lTabs ha
    have h1 : toW 11 (Native.toddAct a m) ∈ A := by
      rw [← rho11_of_repT j hj m]
      exact hinv j _ hmA
    refine huA _ ?_ h1
    rw [toddAct_eq hj]
    simpa using act11_lt a m
  have hcard : 512 ≤ ((List.range 2048).filter
      (Native.toddKerT (Native.toddActTabs ()) u)).length := by
    rw [← hA, card_eq_filter A (fun m => decide (m < 2048 ∧ toW 11 m ∈ A))
      (fun m hm => by simp [hm])]
    refine (List.monotone_filter_right _ ?_).length_le
    intro m hm
    simp only [decide_eq_true_eq] at hm
    exact hker m hm.1 hm.2
  have hsub : ∀ m < 2048, toW 11 m ∈ A →
      Native.toddOctsKer (Native.octsT Native.baseTrio) m = true := by
    rcases toddUniq_spec hu0 hu with hlt | hall
    · exact absurd hcard (not_le.2 hlt)
    · exact fun m hm hmA => hall m hm (hker m hm hmA)
  have hle : A ≤ annOf (trioFin 0) := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
    rw [mem_annOf_trioFin_zero]
    exact hsub m (by simpa using hm) hw
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_annOf_trioFin_zero, hA])

private theorem card_inf_of_rep
    {p r : ℕ} (hp : p < 3795) (hr : r < 3795) {i : Fin 5} (h : Delta (trioFin 0) (trioFin p) i)
    (hr' : Delta (trioFin 0) (trioFin r) i) :
    Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin p)) =
      Nat.card ↥(annOf (trioFin 0) ⊓ annOf (trioFin r)) := by
  obtain ⟨g, hg, hg0, hgp⟩ := delta_base_orbit hp hr h hr'
  have := card_annOf_inf_smul hg (isTrio_trioFin (by norm_num : 0 < 3795)).2.1
    (isTrio_trioFin hp).2.1
  rw [hg0, hgp] at this
  exact this.symm

private theorem card_annOf_inf_delta
    {l k : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hk : IsTrio k) (i : Fin 5) (h : Delta l k i) :
    Nat.card ↥(annOf l ⊓ annOf k) = ![512, 256, 128, 128, 128] i := by
  have key := delta_trio_pair_of_base
    (Q := fun l k => ∀ i : Fin 5, IsTrio l → IsTrio k → Delta l k i →
      Nat.card ↥(annOf l ⊓ annOf k) = ![512, 256, 128, 128, 128] i) ?_ ?_ hl hk
  · exact key i hl hk h
  · intro g hg l k hlk i hl hk h
    have hl' := (isTrio_smul_iff hg).1 hl
    have hk' := (isTrio_smul_iff hg).1 hk
    rw [card_annOf_inf_smul hg hl'.2.1 hk'.2.1]
    exact hlk i hl' hk' ((delta_smul_iff hg i).1 h)
  · intro p hp i _ _ h
    obtain ⟨⟨h1, c1⟩, ⟨h2, c2⟩, ⟨h3, c3⟩, ⟨h4, c4⟩⟩ := toddInt_facts
    match i, h with
    | 0, h =>
      have e : trioFin p = trioFin 0 := h
      rw [e, inf_idem]
      exact card_annOf_trioFin_zero
    | 1, h =>
      rw [card_inf_of_rep hp (by norm_num : 267 < 3795) h h1]
      exact c1
    | 2, h =>
      rw [card_inf_of_rep hp (by norm_num : 23 < 3795) h h2]
      exact c2
    | 3, h =>
      rw [card_inf_of_rep hp (by norm_num : 22 < 3795) h h3]
      exact c3
    | 4, h =>
      rw [card_inf_of_rep hp (by norm_num : 1 < 3795) h h4]
      exact c4

theorem card_annOf_inf_one
    {l k : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hk : IsTrio k) (h : Delta l k 1) : Nat.card ↥(annOf l ⊓ annOf k) = 256 :=
  card_annOf_inf_delta hl hk 1 h

theorem card_annOf_inf_two
    {l k : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hk : IsTrio k) (h : Delta l k 2 ∨ Delta l k 3 ∨ Delta l k 4) :
    Nat.card ↥(annOf l ⊓ annOf k) = 128 := by
  rcases h with h | h | h
  · exact card_annOf_inf_delta hl hk 2 h
  · exact card_annOf_inf_delta hl hk 3 h
  · exact card_annOf_inf_delta hl hk 4 h

private theorem isOctad_of_mem_octsOf {U : Finset (Finset (Fin 24))} (hU : IsSextet U) :
    ∀ O ∈ octsOf U, IsOctad O := by
  intro O hO
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsOf.1 hO
  exact hU.2.2.2.2 a ha b hb hab

private theorem exists_trio_of_mem_octsOf {U : Finset (Finset (Fin 24))} (hU : IsSextet U)
    {O : Finset (Fin 24)} (hO : O ∈ octsOf U) : ∃ t ∈ triosOf U, O ∈ t := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsOf.1 hO
  have hcard : ((U.erase a).erase b).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab.symm, hb⟩),
      Finset.card_erase_of_mem ha, hU.1]
  obtain ⟨c, hc⟩ : ((U.erase a).erase b).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hcard' : (((U.erase a).erase b).erase c).card = 3 := by
    rw [Finset.card_erase_of_mem hc, hcard]
  obtain ⟨d, hd⟩ : (((U.erase a).erase b).erase c).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hcard'' : ((((U.erase a).erase b).erase c).erase d).card = 2 := by
    rw [Finset.card_erase_of_mem hd, hcard']
  obtain ⟨e, f, hef, hEF⟩ := Finset.card_eq_two.1 hcard''
  have he : e ∈ ((((U.erase a).erase b).erase c).erase d) := by rw [hEF]; simp
  have hf : f ∈ ((((U.erase a).erase b).erase c).erase d) := by rw [hEF]; simp
  simp only [Finset.mem_erase] at hc hd he hf
  obtain ⟨hcb, hca, hcU⟩ := hc
  obtain ⟨hdc, hdb, hda, hdU⟩ := hd
  obtain ⟨hed, hec, heb, hea, heU⟩ := he
  obtain ⟨hfd, hfc, hfb, hfa, hfU⟩ := hf
  have hdis : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → Disjoint x y := hU.2.2.1
  have hoct : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → IsOctad (x ∪ y) := hU.2.2.2.2
  have hT : IsTrio {a ∪ b, c ∪ d, e ∪ f} := by
    refine isTrio_of_three (hoct a ha b hb hab) (hoct c hcU d hdU hdc.symm)
      (hoct e heU f hfU hef) ?_ ?_ ?_ ?_
    · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨hdis a ha c hcU hca.symm, hdis a ha d hdU hda.symm⟩, Finset.disjoint_union_right.2
        ⟨hdis b hb c hcU hcb.symm, hdis b hb d hdU hdb.symm⟩⟩
    · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨hdis a ha e heU hea.symm, hdis a ha f hfU hfa.symm⟩, Finset.disjoint_union_right.2
        ⟨hdis b hb e heU heb.symm, hdis b hb f hfU hfb.symm⟩⟩
    · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨hdis c hcU e heU hec.symm, hdis c hcU f hfU hfc.symm⟩, Finset.disjoint_union_right.2
        ⟨hdis d hdU e heU hed.symm, hdis d hdU f hfU hfd.symm⟩⟩
    · refine Finset.eq_univ_iff_forall.2 fun x => ?_
      have hx : x ∈ U.biUnion id := by rw [hU.2.2.2.1]; exact Finset.mem_univ x
      obtain ⟨B, hBU, hxB⟩ := Finset.mem_biUnion.1 hx
      have hxB' : x ∈ B := hxB
      by_cases hBa : B = a
      · rw [hBa] at hxB'
        simp [hxB']
      by_cases hBb : B = b
      · rw [hBb] at hxB'
        simp [hxB']
      by_cases hBc : B = c
      · rw [hBc] at hxB'
        simp [hxB']
      by_cases hBd : B = d
      · rw [hBd] at hxB'
        simp [hxB']
      have hBE : B ∈ ((((U.erase a).erase b).erase c).erase d) := by
        simp only [Finset.mem_erase]
        exact ⟨hBd, hBc, hBb, hBa, hBU⟩
      rw [hEF] at hBE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hBE
      rcases hBE with hBe | hBf
      · rw [hBe] at hxB'
        simp [hxB']
      · rw [hBf] at hxB'
        simp [hxB']
  refine ⟨{a ∪ b, c ∪ d, e ∪ f}, mem_triosOf.2 ⟨hT, ?_⟩, by simp⟩
  intro X hX
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX
  rcases hX with rfl | rfl | rfl
  · exact mem_octsOf.2 ⟨a, ha, b, hb, hab, rfl⟩
  · exact mem_octsOf.2 ⟨c, hcU, d, hdU, hdc.symm, rfl⟩
  · exact mem_octsOf.2 ⟨e, heU, f, hfU, hef, rfl⟩

theorem card_annOf_octsOf
    {U : Finset (Finset (Fin 24))} (hU : IsSextet U) : Nat.card (annOf (octsOf U)) = 128 := by
  obtain ⟨g, hg, hgU⟩ := sextet_transitive hU
  have h := card_annOf_smul hg (isOctad_of_mem_octsOf hU)
  rw [← octsOf_smul, hgU] at h
  rw [← h]
  exact toddSext_facts.1

theorem annOf_octsOf_inj
    {U U' : Finset (Finset (Fin 24))} (hU : IsSextet U) (hU' : IsSextet U')
    (h : annOf (octsOf U) = annOf (octsOf U')) : U = U' := by
  obtain ⟨g, hg, hgU⟩ := sextet_transitive hU
  obtain ⟨q, hq, hqU'⟩ := (isSextet_iff (g • U')).1 ((isSextet_smul_iff hg).2 hU')
  have key : annOf (octsOf (g • U)) = annOf (octsOf (g • U')) := by
    rw [octsOf_smul, octsOf_smul, annOf_smul hg (isOctad_of_mem_octsOf hU),
      annOf_smul hg (isOctad_of_mem_octsOf hU'), h]
  rw [hgU, ← hqU'] at key
  have hq0 : q = 0 := by
    by_contra hne
    obtain ⟨W, hW0, hWq⟩ := toddSext_facts.2 q hq hne
    exact hWq (key ▸ hW0)
  subst hq0
  exact smul_left_cancel g (hgU.trans hqU')

theorem mem_annOf_octsOf_iff {U : Finset (Finset (Fin 24))} (hU : IsSextet U) {w : W11} :
    w ∈ annOf (octsOf U) ↔ ∀ t ∈ triosOf U, w ∈ annOf t := by
  rw [mem_annOf]
  constructor
  · intro h t ht
    rw [mem_annOf]
    intro O hO
    exact h O (Finset.subset_iff.1 (mem_triosOf.1 ht).2 hO)
  · intro h O hO
    obtain ⟨t, ht, hOt⟩ := exists_trio_of_mem_octsOf hU hO
    exact (mem_annOf.1 (h t ht)) O hOt

theorem eq_annOf_of_invariant
    {t : Finset (Finset (Fin 24))} (ht : IsTrio t)
    (A : Subgroup W11) (hA : Nat.card A = 512)
    (hinv : ∀ (σ : S24) (hσ : σ ∈ M24g), σ • t = t → ∀ w ∈ A,
      rho11 AutPerm le_rfl ⟨σ, hσ⟩ w ∈ A) :
    A = annOf t := by
  obtain ⟨g, hg, hgt⟩ := trio_transitive ht
  have hmap : A.map (rho11 AutPerm le_rfl ⟨g, hg⟩).toMonoidHom = annOf (trioFin 0) := by
    refine eq_annOf_base _ ?_ ?_
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hA]
    · intro j w hw
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
      have hc : g⁻¹ * lPerm j * g ∈ M24g :=
        M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hg) (lPerm_mem j)) hg
      have hfix : (g⁻¹ * lPerm j * g) • t = t := by
        rw [mul_smul, mul_smul, hgt, lPerm_smul_trioFin_zero, ← hgt, inv_smul_smul]
      refine Subgroup.mem_map.2 ⟨_, hinv _ hc hfix w₀ hw₀, ?_⟩
      have e : (⟨lPerm j, lPerm_mem j⟩ : ↥AutPerm) * ⟨g, hg⟩ =
          ⟨g, hg⟩ * ⟨g⁻¹ * lPerm j * g, hc⟩ := Subtype.ext (by simp [mul_assoc])
      have h1 := congrArg (fun x => (rho11 AutPerm le_rfl x) w₀) e
      simp only [map_mul, MulAut.mul_apply] at h1
      exact h1.symm
  have h2 := annOf_smul hg ht.2.1
  rw [hgt] at h2
  exact Subgroup.map_injective (MulEquiv.injective _) (hmap.trans h2)

end CFSG.Quasithin.H13.AS91.M24G
