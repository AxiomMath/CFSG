module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCount

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

open E6ThreeEnd

private abbrev Md : Type := Model piE7 piE7_pow_three

private def ofVec (v : Fin 3 → ZMod 3) : Md := SemidirectProduct.inl (.ofAdd v)

private def cM : Md := SemidirectProduct.inr (.ofAdd 1)

private def dM : Md := ofVec ![1, 1, 1]

private def outVec (v : Fin 3 → ZMod 3) : Md := ofVec v * cM

private def KSub (f : Fin 3 → ZMod 3) : Subgroup Md :=
  Subgroup.closure (ofVec '' {v : Fin 3 → ZMod 3 | ∑ i, f i * v i = 0})

private def PSub (y : Md) : Subgroup Md := Subgroup.closure ({y, dM} : Set Md)

private def fourF : Fin 4 → Fin 3 → ZMod 3 :=
  ![![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]]

private def e3 : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 0, 1, 0, 0]

private def xK : Fin 4 → Fin Tag.E6.rank → ZMod 3 :=
  ![![1, 1, 1, 0, 1, 1], ![1, 2, 1, 0, 1, 1], ![1, 1, 1, 0, 2, 2],
    ![1, 2, 1, 0, 2, 2]]

private def xOut : Fin Tag.E6.rank → ZMod 3 := ![1, 1, 1, 0, 1, 1]

private def dot (α : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  ∑ i, (α i : ZMod 3) * x i

private theorem e6_check : e6Certificate.check = true := by decide +kernel

private theorem mem_rootFinset_E6 {v : Fin Tag.E6.rank → ℤ} :
    v ∈ rootFinset .E6 ↔ IsRoot .E6 v := by
  rw [rootFinset, List.mem_toFinset, List.mem_map,
    RootCertificate.isRoot_iff e6_check]
  simp only [List.mem_range, Tag.rootCertificate]

private theorem modelHom_cM : modelHomE6 cM =
    (coxeterSystem .E6).wordProd wordE6C := by
  rw [cM]; exact modelHomE6_c

private theorem modelHom_dM : modelHomE6 dM =
    (coxeterSystem .E6).wordProd (nfWordE6 1 1 1) := by
  rw [dM, ofVec, modelHomE6_inl]
  simp only [toAdd_ofAdd]
  rfl

private theorem modelHom_outVec (v : Fin 3 → ZMod 3) :
    modelHomE6 (outVec v) = (coxeterSystem .E6).wordProd
      (nfWordE6 (v 0).val (v 1).val (v 2).val ++ wordE6C) := by
  rw [outVec, ofVec, map_mul, modelHomE6_inl, modelHom_cM,
    CoxeterSystem.wordProd_append]
  simp only [toAdd_ofAdd]

private theorem ofVec_add (u v : Fin 3 → ZMod 3) :
    ofVec (u + v) = ofVec u * ofVec v := by
  rw [ofVec, ofVec, ofVec, ofAdd_add, map_mul]

private theorem ofVec_nsmul (n : ℕ) (v : Fin 3 → ZMod 3) :
    ofVec (n • v) = ofVec v ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, ofVec]; rfl
  | succ n ih => rw [succ_nsmul, ofVec_add, ih, pow_succ]

private theorem ofVec_smul_const (a : ZMod 3) :
    ofVec (a • ![1, 1, 1]) = dM ^ a.val := by
  have h1 : a • (![1, 1, 1] : Fin 3 → ZMod 3) = a.val • ![1, 1, 1] := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h1, ofVec_nsmul, dM]

private theorem ofVec_neg (v : Fin 3 → ZMod 3) : ofVec (-v) = (ofVec v)⁻¹ := by
  rw [ofVec, ofVec, ofAdd_neg]
  exact map_inv SemidirectProduct.inl (Multiplicative.ofAdd v)

private theorem right_eq_ofAdd_val (y : Md) :
    y.right = Multiplicative.ofAdd ((y.right.toAdd).val : ZMod 3) := by
  rw [ZMod.natCast_zmod_val, ofAdd_toAdd]

private theorem eq_smul_const_of_shiftAut {w : Fin 3 → ZMod 3}
    (h : shiftAut piE7 (.ofAdd w) = .ofAdd w) :
    ∃ a : ZMod 3, w = a • ![1, 1, 1] := by
  revert w
  decide +kernel

private theorem sum_eq_zero_of_cube {v : Fin 3 → ZMod 3}
    (h : Multiplicative.ofAdd v * shiftAut piE7 (.ofAdd v) *
      (shiftAut piE7 ^ 2) (.ofAdd v) = 1) : ∑ i, v i = 0 := by
  revert v
  decide +kernel

private theorem mk_eq_outVec (w : Multiplicative (Fin 3 → ZMod 3)) :
    (⟨w, .ofAdd 1⟩ : Md) = outVec w.toAdd := by
  apply SemidirectProduct.ext
  · rw [outVec, ofVec, SemidirectProduct.mul_left]
    simp [cM, SemidirectProduct.left_inr, SemidirectProduct.right_inr]
  · rw [outVec, ofVec, SemidirectProduct.mul_right]
    simp [cM, SemidirectProduct.left_inr, SemidirectProduct.right_inr]

private theorem adAct_inv_apply (w : WeylGroup .E6) (x : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 w⁻¹ (adAct .E6 3 w x) = x := by
  rw [← adAct_mul, inv_mul_cancel, adAct_one]

private theorem fix_of_mem_closure {s : Set Md} {x : Fin Tag.E6.rank → ZMod 3}
    (h : ∀ y ∈ s, adAct .E6 3 (modelHomE6 y) x = x) :
    ∀ a ∈ Subgroup.closure s, adAct .E6 3 (modelHomE6 a) x = x := by
  intro a ha
  refine Subgroup.closure_induction (p := fun a _ => adAct .E6 3 (modelHomE6 a) x = x)
    ?_ ?_ ?_ ?_ ha
  · exact h
  · rw [map_one, adAct_one]
  · intro u v _ _ ihu ihv
    rw [map_mul, adAct_mul, ihv, ihu]
  · intro u _ ihu
    rw [map_inv]
    have h1 := adAct_inv_apply (modelHomE6 u) x
    rwa [ihu] at h1

private theorem K_fix_e3_aux (j : Fin 4) :
    ∀ v : Fin 3 → ZMod 3, (∑ i, fourF j i * v i = 0) →
      adWord .E6 3 (nfWordE6 (v 0).val (v 1).val (v 2).val) e3 = e3 := by
  fin_cases j <;> decide +kernel

private theorem K_fix_x_aux (j : Fin 4) :
    ∀ v : Fin 3 → ZMod 3, (∑ i, fourF j i * v i = 0) →
      adWord .E6 3 (nfWordE6 (v 0).val (v 1).val (v 2).val) (xK j) = xK j := by
  fin_cases j <;> decide +kernel

private theorem K_fix_e3 (j : Fin 4) :
    ∀ a ∈ KSub (fourF j), adAct .E6 3 (modelHomE6 a) e3 = e3 := by
  refine fix_of_mem_closure ?_
  intro y hy
  unfold KSub at hy
  obtain ⟨v, hv, rfl⟩ := hy
  rw [ofVec, modelHomE6_inl, ← adWord_eq_adAct]
  exact K_fix_e3_aux j v hv

private theorem K_fix_x (j : Fin 4) :
    ∀ a ∈ KSub (fourF j), adAct .E6 3 (modelHomE6 a) (xK j) = xK j := by
  refine fix_of_mem_closure ?_
  intro y hy
  unfold KSub at hy
  obtain ⟨v, hv, rfl⟩ := hy
  rw [ofVec, modelHomE6_inl, ← adWord_eq_adAct]
  exact K_fix_x_aux j v hv

private theorem root_cover_K :
    ∀ α ∈ rootFinset .E6, ∀ j : Fin 4,
      dot α e3 ≠ 0 ∨ dot α (xK j) ≠ 0 := by
  decide +kernel

private theorem K_root_property (j : Fin 4) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) :
    ∃ x, (∀ a ∈ KSub (fourF j), adAct .E6 3 (modelHomE6 a) x = x) ∧ dot α x ≠ 0 := by
  have hmem : α ∈ rootFinset .E6 := mem_rootFinset_E6.mpr hα
  rcases root_cover_K α hmem j with h3 | hx
  · exact ⟨e3, K_fix_e3 j, h3⟩
  · exact ⟨xK j, K_fix_x j, hx⟩

private theorem out_fix_e3_aux :
    ∀ v : Fin 3 → ZMod 3, (∑ i, v i = 0) →
      adWord .E6 3 (nfWordE6 (v 0).val (v 1).val (v 2).val ++ wordE6C) e3 = e3 := by
  decide +kernel

private theorem out_fix_x_aux :
    ∀ v : Fin 3 → ZMod 3, (∑ i, v i = 0) →
      adWord .E6 3 (nfWordE6 (v 0).val (v 1).val (v 2).val ++ wordE6C) xOut = xOut := by
  decide +kernel

private theorem out_fix_e3 {v : Fin 3 → ZMod 3} (hv : ∑ i, v i = 0) :
    adAct .E6 3 (modelHomE6 (outVec v)) e3 = e3 := by
  rw [modelHom_outVec, ← adWord_eq_adAct]
  exact out_fix_e3_aux v hv

private theorem out_fix_x {v : Fin 3 → ZMod 3} (hv : ∑ i, v i = 0) :
    adAct .E6 3 (modelHomE6 (outVec v)) xOut = xOut := by
  rw [modelHom_outVec, ← adWord_eq_adAct]
  exact out_fix_x_aux v hv

private theorem dM_fix_e3 : adAct .E6 3 (modelHomE6 dM) e3 = e3 := by
  rw [modelHom_dM, ← adWord_eq_adAct]
  decide +kernel

private theorem dM_fix_x : adAct .E6 3 (modelHomE6 dM) xOut = xOut := by
  rw [modelHom_dM, ← adWord_eq_adAct]
  decide +kernel

private theorem root_cover_out :
    ∀ α ∈ rootFinset .E6, dot α e3 ≠ 0 ∨ dot α xOut ≠ 0 := by
  decide +kernel

private theorem out_root_property {v : Fin 3 → ZMod 3} (hv : ∑ i, v i = 0)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) :
    ∃ x, (∀ a ∈ PSub (outVec v), adAct .E6 3 (modelHomE6 a) x = x) ∧ dot α x ≠ 0 := by
  have hmem : α ∈ rootFinset .E6 := mem_rootFinset_E6.mpr hα
  have hfixe : ∀ a ∈ PSub (outVec v), adAct .E6 3 (modelHomE6 a) e3 = e3 := by
    refine fix_of_mem_closure (s := {outVec v, dM}) ?_
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact out_fix_e3 hv
    · exact dM_fix_e3
  have hfixx : ∀ a ∈ PSub (outVec v), adAct .E6 3 (modelHomE6 a) xOut = xOut := by
    refine fix_of_mem_closure (s := {outVec v, dM}) ?_
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact out_fix_x hv
    · exact dM_fix_x
  rcases root_cover_out α hmem with h3 | hx
  · exact ⟨e3, hfixe, h3⟩
  · exact ⟨xOut, hfixx, hx⟩

private theorem outVec_right (v : Fin 3 → ZMod 3) : (outVec v).right = .ofAdd 1 := by
  rw [outVec, ofVec, SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul, cM,
    SemidirectProduct.right_inr]

private theorem mem_PSub_out_zero {B : Subgroup Md}
    (hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y)
    {v : Fin 3 → ZMod 3} (hy : outVec v ∈ B) {b : Md} (hb : b ∈ B) (hr : b.right = 1) :
    b ∈ PSub (outVec v) := by
  set w : Fin 3 → ZMod 3 := b.left.toAdd
  have hbw : b = ofVec w := by
    rw [eq_inl_of_right_eq_one hr, ofVec, ofAdd_toAdd]
  have hcomm : b * outVec v = outVec v * b := hBc b hb (outVec v) hy
  rw [hbw] at hcomm
  have hs : shiftAut piE7 (.ofAdd w) = .ofAdd w := by
    refine shiftAut_eq_of_comm (π := piE7) (hπ := piE7_pow_three)
      (v := Multiplicative.ofAdd v) (w := Multiplicative.ofAdd w) ?_
    have hpair : outVec v = (⟨Multiplicative.ofAdd v, .ofAdd 1⟩ : Md) := by
      simpa using (mk_eq_outVec (Multiplicative.ofAdd v)).symm
    rw [hpair] at hcomm
    simpa [ofVec] using hcomm
  obtain ⟨a, ha⟩ := eq_smul_const_of_shiftAut hs
  have hbd : b = dM ^ a.val := by
    rw [hbw, ha, ofVec_smul_const]
  rw [hbd]
  have hgen : dM ∈ PSub (outVec v) := by
    unfold PSub
    exact Subgroup.subset_closure (by simp)
  exact Subgroup.pow_mem (PSub (outVec v)) hgen a.val

private theorem mem_PSub_out_one {B : Subgroup Md}
    (hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y)
    {v : Fin 3 → ZMod 3} (hy : outVec v ∈ B) {b : Md} (hb : b ∈ B)
    (hr : b.right = .ofAdd 1) : b ∈ PSub (outVec v) := by
  have hbw : b = outVec b.left.toAdd := by
    rw [show b = (⟨b.left, .ofAdd 1⟩ : Md) from SemidirectProduct.ext rfl hr]
    exact mk_eq_outVec b.left
  have hmem : b * (outVec v)⁻¹ ∈ B := mul_mem hb (inv_mem hy)
  have hright : (b * (outVec v)⁻¹).right = 1 := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hr, outVec_right,
      mul_inv_cancel]
  have hzero := mem_PSub_out_zero hBc hy hmem hright
  have hyP : outVec v ∈ PSub (outVec v) := by
    unfold PSub
    exact Subgroup.subset_closure (by simp)
  have hb_eq : b = (b * (outVec v)⁻¹) * outVec v := by group
  rw [hb_eq]
  exact mul_mem hzero hyP

private theorem mem_PSub_out {B : Subgroup Md}
    (hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y) (hB3 : ∀ y ∈ B, y ^ 3 = 1)
    {v : Fin 3 → ZMod 3} (hy : outVec v ∈ B) {b : Md} (hb : b ∈ B) :
    b ∈ PSub (outVec v) := by
  have hbr := right_eq_ofAdd_val b
  have hval := ZMod.val_lt b.right.toAdd
  have hm : (b.right.toAdd).val = 0 ∨ (b.right.toAdd).val = 1 ∨
      (b.right.toAdd).val = 2 := by omega
  rcases hm with h0 | h1 | h2
  · have hr : b.right = 1 := by rw [hbr, h0]; rfl
    exact mem_PSub_out_zero hBc hy hb hr
  · have hr : b.right = .ofAdd 1 := by rw [hbr, h1]; rfl
    exact mem_PSub_out_one hBc hy hb hr
  · have hb2 : b ^ 2 ∈ B := Subgroup.pow_mem B hb 2
    have hr2 : (b ^ 2).right = .ofAdd 1 := by
      rw [pow_two, SemidirectProduct.mul_right, hbr, h2, ← ofAdd_add]
      rfl
    have h2mem := mem_PSub_out_one hBc hy hb2 hr2
    have hb4 : (b ^ 2) ^ 2 = b := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ, hB3 b hb, one_mul]
    rw [← hb4]
    exact Subgroup.pow_mem (PSub (outVec v)) h2mem 2

private theorem exists_ker_four {v : Fin 3 → ZMod 3} (hv : v ≠ 0)
    (hs : ∀ i, v ≠ Pi.single i 1 ∧ v ≠ -Pi.single i 1) :
    ∃ j : Fin 4, ∑ i, fourF j i * v i = 0 := by
  revert v
  decide +kernel

private theorem exists_ker_four_of_nonzero {f : Fin 3 → ZMod 3}
    (hf : ∀ i, f i ≠ 0) :
    ∃ j : Fin 4, ∀ v : Fin 3 → ZMod 3, (∑ i, f i * v i = 0) →
      ∑ i, fourF j i * v i = 0 := by
  revert f
  decide +kernel

private theorem covering_outside (B : Subgroup Md) (hB3 : ∀ y ∈ B, y ^ 3 = 1)
    (hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y)
    (hI : ∃ y ∈ B, y.right ≠ 1) :
    ∃ v : Fin 3 → ZMod 3, (∑ i, v i = 0) ∧ B ≤ PSub (outVec v) := by
  obtain ⟨y, hyB, hyr⟩ := hI
  obtain ⟨y₁, hy₁B, hy₁r⟩ := exists_right_eq_ofAdd_one hyB hyr
  set v : Fin 3 → ZMod 3 := y₁.left.toAdd with hv
  have hy₁eq : y₁ = outVec v := by
    rw [show y₁ = (⟨y₁.left, .ofAdd 1⟩ : Md) from SemidirectProduct.ext rfl hy₁r]
    exact mk_eq_outVec y₁.left
  have hcube : (outVec v) ^ 3 = 1 := by
    rw [← hy₁eq]
    exact hB3 y₁ hy₁B
  have hleft : Multiplicative.ofAdd v * shiftAut piE7 (.ofAdd v) *
      (shiftAut piE7 ^ 2) (.ofAdd v) = 1 := by
    have h := congrArg SemidirectProduct.left hcube
    rw [SemidirectProduct.one_left] at h
    have hpair : outVec v = (⟨Multiplicative.ofAdd v, .ofAdd 1⟩ : Md) := by
      simpa using (mk_eq_outVec (Multiplicative.ofAdd v)).symm
    rw [hpair, left_cube] at h
    exact h
  refine ⟨v, sum_eq_zero_of_cube hleft, ?_⟩
  intro b hb
  exact mem_PSub_out hBc hB3 (by rwa [hy₁eq] at hy₁B) hb

private theorem covering_le_N_zero (B : Subgroup Md) (hcard : Nat.card B = 1) :
    ∃ j : Fin 4, B ≤ KSub (fourF j) := by
  refine ⟨0, ?_⟩
  rw [Subgroup.eq_bot_of_card_eq B hcard]
  exact bot_le

private theorem covering_le_N_one (B : Subgroup Md) (hB3 : ∀ y ∈ B, y ^ 3 = 1)
    (hI : ∀ y ∈ B, y.right = 1) (hgB : ∀ i, ofVec (Pi.single i 1) ∉ B)
    (hcard : Nat.card B = 3) : ∃ j : Fin 4, B ≤ KSub (fourF j) := by
  haveI := finite_model (π := piE7) (hπ := piE7_pow_three)
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨y, hyB⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
  have hyne : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have horder : orderOf y = 3 := orderOf_eq_prime (hB3 y hyB) hyne
  have hBz : B = Subgroup.zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyB) ?_).symm
    simp [Nat.card_zpowers, horder, hcard]
  have hyr : y.right = 1 := hI y hyB
  set v : Fin 3 → ZMod 3 := y.left.toAdd with hv
  have hyeq : y = ofVec v := by
    rw [eq_inl_of_right_eq_one hyr, ofVec, ofAdd_toAdd]
  have hv0 : v ≠ 0 := by
    intro h0
    apply hyne
    rw [hyeq, h0]
    rfl
  have hsing : ∀ i, v ≠ Pi.single i 1 ∧ v ≠ -Pi.single i 1 := by
    intro i
    constructor
    · intro h
      apply hgB i
      rwa [hyeq, h] at hyB
    · intro h
      apply hgB i
      have hmem : ofVec (-Pi.single i 1) ∈ B := by rwa [hyeq, h] at hyB
      rw [ofVec_neg] at hmem
      simpa using inv_mem hmem
  obtain ⟨j, hj⟩ := exists_ker_four hv0 hsing
  refine ⟨j, ?_⟩
  rw [hBz, hyeq]
  exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨v, hj, rfl⟩)

private theorem covering_le_N_two (B : Subgroup Md) (hI : ∀ y ∈ B, y.right = 1)
    (hgB : ∀ i, ofVec (Pi.single i 1) ∉ B) (hcard : Nat.card B = 9) :
    ∃ j : Fin 4, B ≤ KSub (fourF j) := by
  have hcardX : Nat.card (expSub B) = 9 := by rw [card_expSub hI, hcard]
  have hle : 3 ^ (3 - 1) ≤ Nat.card (expSub B) := by rw [hcardX]; norm_num
  obtain ⟨f, hf⟩ := exists_forall_mem_iff_dot (expSub B) hle
  have hfne : ∀ i, f i ≠ 0 := by
    intro i hi
    apply hgB i
    have hsum : ∑ j, f j * (Pi.single i 1 : Fin 3 → ZMod 3) j = f i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hm : Pi.single i 1 ∈ expSub B := by
      rw [hf, hsum, hi]
    exact by simpa [ofVec] using (mem_expSub.mp hm)
  obtain ⟨j, hj⟩ := exists_ker_four_of_nonzero hfne
  refine ⟨j, ?_⟩
  intro y hy
  have hyr : y.right = 1 := hI y hy
  have hyeq : y = ofVec y.left.toAdd :=
    (eq_inl_of_right_eq_one hyr).trans (by rw [ofVec, ofAdd_toAdd])
  rw [hyeq]
  refine Subgroup.subset_closure ⟨y.left.toAdd, ?_, rfl⟩
  apply hj
  have hm : y.left.toAdd ∈ expSub B := by
    rw [mem_expSub]
    rwa [hyeq] at hy
  exact (hf _).mp hm

private theorem covering_le_N_three (B : Subgroup Md)
    (hBN : B ≤ (SemidirectProduct.inl :
      Multiplicative (Fin 3 → ZMod 3) →* Md).range)
    (hgB : ∀ i, ofVec (Pi.single i 1) ∉ B) (hcard : Nat.card B = 27) : False := by
  haveI := finite_model (π := piE7) (hπ := piE7_pow_three)
  have hBeq : B = (SemidirectProduct.inl :
      Multiplicative (Fin 3 → ZMod 3) →* Md).range := by
    refine Subgroup.eq_of_le_of_card_ge hBN ?_
    rw [card_range_inl, hcard]
    norm_num
  exact hgB 0 (by rw [hBeq]; exact ⟨_, rfl⟩)

private theorem covering_le_N (B : Subgroup Md) (hB3 : ∀ y ∈ B, y ^ 3 = 1)
    (hI : ∀ y ∈ B, y.right = 1) (hgB : ∀ i, ofVec (Pi.single i 1) ∉ B) :
    ∃ j : Fin 4, B ≤ KSub (fourF j) := by
  classical
  haveI := finite_model (π := piE7) (hπ := piE7_pow_three)
  have hBN : B ≤ (SemidirectProduct.inl :
      Multiplicative (Fin 3 → ZMod 3) →* Md).range := by
    intro y hy
    exact ⟨y.left, (eq_inl_of_right_eq_one (hI y hy)).symm⟩
  have hdvd : Nat.card B ∣ 3 ^ 3 := by
    have h := Subgroup.card_dvd_of_le hBN
    rwa [card_range_inl] at h
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl | rfl
  · exact covering_le_N_zero B (by rw [hk']; norm_num)
  · exact covering_le_N_one B hB3 hI hgB (by rw [hk']; norm_num)
  · exact covering_le_N_two B hI hgB (by rw [hk']; norm_num)
  · exact False.elim (covering_le_N_three B hBN hgB (by rw [hk']; norm_num))

private theorem covering (B : Subgroup Md) (hB3 : ∀ y ∈ B, y ^ 3 = 1)
    (hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y)
    (hgB : ∀ i, ofVec (Pi.single i 1) ∉ B) :
    (∃ j : Fin 4, B ≤ KSub (fourF j)) ∨
      ∃ v : Fin 3 → ZMod 3, (∑ i, v i = 0) ∧ B ≤ PSub (outVec v) := by
  by_cases hI : ∃ y ∈ B, y.right ≠ 1
  · exact Or.inr (covering_outside B hB3 hBc hI)
  · push Not at hI
    exact Or.inl (covering_le_N B hB3 hI hgB)

theorem exists_fix_dot_ne_zero (A : Subgroup (WeylGroup .E6)) (hAS : A ≤ modelHomE6.range)
    (hA : IsElemAbelian 3 A) (hg : ∀ i, gE6 i ∉ A) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) :
    ∃ x : Fin Tag.E6.rank → ZMod 3, (∀ a ∈ A, adAct .E6 3 a x = x) ∧
      ∑ i, (α i : ZMod 3) * x i ≠ 0 := by
  classical
  set B : Subgroup Md := A.comap modelHomE6 with hB
  have hmap : B.map modelHomE6 = A := Subgroup.map_comap_eq_self hAS
  have hB3 : ∀ y ∈ B, y ^ 3 = 1 := by
    intro y hy
    apply modelHomE6_injective
    rw [map_pow, map_one]
    exact hA.2 (modelHomE6 y) hy
  have hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y := by
    intro y hy z hz
    apply modelHomE6_injective
    rw [map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hA hy hz
  have hgB : ∀ i, ofVec (Pi.single i 1) ∉ B := by
    intro i hi
    rw [hB] at hi
    change modelHomE6 (ofVec (Pi.single i 1)) ∈ A at hi
    apply hg i
    rw [show modelHomE6 (ofVec (Pi.single i 1)) = gE6 i from by
      rw [ofVec]; exact modelHomE6_inl_single i] at hi
    exact hi
  rcases covering B hB3 hBc hgB with ⟨j, hBle⟩ | ⟨v, hvsum, hBle⟩
  · obtain ⟨x, hxfix, hxdot⟩ := K_root_property j hα
    refine ⟨x, ?_, hxdot⟩
    intro a ha
    rw [← hmap] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [← hba]
    exact hxfix b (hBle hb)
  · obtain ⟨x, hxfix, hxdot⟩ := out_root_property hvsum hα
    refine ⟨x, ?_, hxdot⟩
    intro a ha
    rw [← hmap] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [← hba]
    exact hxfix b (hBle hb)

end CFSG.StandardType.E6NonToralThree
