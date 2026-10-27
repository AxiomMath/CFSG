module

public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public import CFSG.Monster.Visible.Kernel
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public import CFSG.Monster.Existence.Census.RigidInputs
public import Certificates.Certificate6023
public import Certificates.Certificate6007

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.AxisCount Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

theorem ofList_single_getD (k k' : ℕ) (hk : k < 196884) :
    (Native.DVec.ofList [(k, 1)]).D.getD k' 0 = if k' = k then 1 else 0 := by
  simp only [Native.DVec.ofList, Native.DVec.ofListE, List.foldl_cons, List.foldl_nil, hk,
    ite_true]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : k = k'
  · subst h
    simp [hk]
  · simp [h, Ne.symm h, Array.getElem?_replicate]
    split_ifs <;> rfl

theorem interp_ofList_single (k : ℕ) (hk : k < 196884) :
    interp (Native.DVec.ofList [(k, 1)]) = fbasis k := by
  rw [interp_eq_sum]
  have hcf : ∀ k', cf (Native.DVec.ofList [(k, 1)]) k' = if k' = k then 1 else 0 := by
    intro k'
    unfold cf
    have h := ofList_single_getD k k' hk
    have he : (Native.DVec.ofList [(k, 1)]).e = 0 := rfl
    rw [he, h]
    split_ifs <;> simp
  simp only [tm, hcf]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h


@[expose] noncomputable def wvec (η : Bool) (c : ℕ) (j : Fin 24) : SpaceB :=
  inW (tensor (Evec η c) (Pi.single j 1))

theorem rowIdx_lt (η : Bool) (c : ℕ) : Native.rowIdx η c < 4096 := by
  unfold Native.rowIdx
  have := Nat.mod_lt (Native.pi0N c / 2) (show 2048 > 0 by norm_num)
  split_ifs <;> omega

theorem fbasis_rowIdx (η : Bool) (c : ℕ) (j : Fin 24) :
    fbasis (98580 + 24 * Native.rowIdx η c + j) = wvec η c j := by
  rw [fbasis_W _ _ j.2, wvecB, spinOfRow_rowIdx, finOf_fin]
  rfl

theorem interp_wvec (η : Bool) (c : ℕ) (j : Fin 24) :
    interp (Native.DVec.ofList [(98580 + 24 * Native.rowIdx η c + j, 1)]) = wvec η c j := by
  have hr := rowIdx_lt η c
  have hj := j.2
  rw [interp_ofList_single _ (by omega), fbasis_rowIdx]

theorem entries_of_fix (p : Pvis) (η : Bool) (c : ℕ) (j : Fin 24)
    (h : thetaEquiv p (wvec η c j) = wvec η c j) (a : SpinIdx) (b : Fin 24) :
    (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (boolZ η, π₀ (toC c)) a * mat p.1.2 j b =
      (if a = (boolZ η, π₀ (toC c)) then 1 else 0) * (if b = j then 1 else 0) := by
  have h1 := congrArg (fun x : SpaceB => x.2.2 a b)
    ((theta_tensor p (Evec η c) (Pi.single j 1)).symm.trans ((thetaEquiv_apply p _).symm.trans h))
  have e1 : Evec η c = Pi.single (boolZ η, π₀ (toC c)) 1 := rfl
  simp only [wvec, tensor, vecMulVec_apply, e1, single_one_vecMul, Matrix.row_apply,
    Pi.single_apply] at h1
  exact h1


theorem fixRowA_of_fixRow {y : Model.Pauli} {η : Bool} {c : ℕ} (h : fixRow y η c = true) :
    fixRowA y.2.1 c = true := by
  simp only [fixRow, fixRowA, Native.ePauliN, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h ⊢
  exact h.2

theorem rigid_A_native :
    (List.range 4096).all (fun a => !(rigidRows.all fun x => fixRowA a x.2) || a == 0 || a == 63) =
      true :=
  Certificates.certificate6023.1

theorem rigid_pauli_native :
    ([0, 63].all fun a => [false, true].all fun s => (List.range 4096).all fun d =>
      !(rigidRows.all fun x => fixRow (s, a, d) x.1 x.2) || (!s && a == 0 && d == 0)) = true :=
  Certificates.certificate6023.2


theorem Evec_eq_single (η : Bool) (c : ℕ) : Evec η c = Pi.single (boolZ η, π₀ (toC c)) 1 := rfl

theorem fixRow_of_row_fixed (y : Model.Pauli) (η : Bool) (c : ℕ)
    (h : ∀ a : SpinIdx, ((pauliQ y : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)
      (boolZ η, π₀ (toC c)) a = if a = (boolZ η, π₀ (toC c)) then 1 else 0) :
    fixRow y η c = true := by
  have h1 := Evec_vecMul_qmatR y η c
  rw [← qmatR_toSC_eq y] at h1
  have e1 : Evec η c ᵥ* ((pauliQ y : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Evec η c := by
    rw [Evec_eq_single, single_one_vecMul]
    funext a
    simp only [Matrix.row_apply, h a, Pi.single_apply]
  rw [e1] at h1
  have h2 := congrFun h1 (boolZ (Model.ePauliN y η c).2.1, π₀ (toC (Model.ePauliN y η c).2.2))
  simp only [Evec_eq_single, Pi.smul_apply, Pi.single_apply, smul_eq_mul, ite_true, mul_one] at h2
  simp only [fixRow, native_ePauliN, native_pi0N]
  generalize Model.ePauliN y η c = t at h2 ⊢
  by_cases hj : (boolZ t.2.1, π₀ (toC t.2.2)) = (boolZ η, π₀ (toC c))
  · rw [ite_eq_left hj] at h2
    have hs : t.1 = false := by
      by_cases ht : t.1 = true
      · exfalso
        rw [sgn_boolZ, ht] at h2
        norm_num [Model.sgnI] at h2
      · simpa using ht
    obtain ⟨hη, hc⟩ := Prod.mk.inj hj
    have hη' : t.2.1 = η := boolZ_injective hη
    have hc' : Model.pi0N t.2.2 % 4096 = Model.pi0N c % 4096 := by
      have h3 := congrArg (fun x : C₀ => ((x : C) : Fin 24 → ZMod 2)) hc
      simp only [coe_π₀_toC] at h3
      have h4 : toC (Model.pi0N t.2.2 % 4096) = toC (Model.pi0N c % 4096) := by
        rw [toC_mod_4096, toC_mod_4096]
        exact Subtype.ext h3
      exact toC_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h4
    simp [hs, hη', hc']
  · rw [ite_eq_right hj] at h2
    exfalso
    rw [sgn_boolZ] at h2
    by_cases ht : t.1 = true <;> simp [ht, Model.sgnI] at h2


open CFSG.Monster.B.TwoA.Census in
theorem eq_one_of_rows_fixed (q : Q)
    (hrows : ∀ x ∈ rigidRows, ∀ a : SpinIdx,
      ((q : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) (boolZ x.1, π₀ (toC x.2)) a =
        if a = (boolZ x.1, π₀ (toC x.2)) then 1 else 0) : q = 1 := by
  obtain ⟨s, hs, A, hA, D, hD, rfl⟩ := exists_qP q
  have hfix : ∀ x ∈ rigidRows, fixRow (s % 2 == 1, A, D) x.1 x.2 = true := fun x hx =>
    fixRow_of_row_fixed _ _ _ (hrows x hx)
  have h1 := List.all_eq_true.1 rigid_A_native A (List.mem_range.2 hA)
  have hA0 : A = 0 ∨ A = 63 := by
    have h2 : (rigidRows.all fun x => fixRowA A x.2) = true :=
      List.all_eq_true.2 fun x hx => fixRowA_of_fixRow (hfix x hx)
    rw [h2] at h1
    simpa using h1
  have h3 : (s % 2 = 0 ∧ A = 0 ∧ D = 0) := by
    have h4 := List.all_eq_true.1 rigid_pauli_native A (by simpa using hA0)
    have h5 := List.all_eq_true.1 h4 (s % 2 == 1) (by cases h : (s % 2 == 1) <;> simp)
    have h6 := List.all_eq_true.1 h5 D (List.mem_range.2 hD)
    have h7 : (rigidRows.all fun x => fixRow (s % 2 == 1, A, D) x.1 x.2) = true :=
      List.all_eq_true.2 hfix
    rw [h7] at h6
    simpa [and_assoc] using h6
  obtain ⟨h11, h9, h10⟩ := h3
  subst h9 h10
  have : qP s 0 0 = qP 0 0 0 := by
    rw [qP, qP, h11]
  rw [this]
  exact pauliQ_false_zero


theorem eq_one_of_snd_eq_one (p : Pvis) (h2 : p.1.2 = 1)
    (hrows : ∀ x ∈ rigidRows, ∀ a : SpinIdx,
      (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (boolZ x.1, π₀ (toC x.2)) a =
        if a = (boolZ x.1, π₀ (toC x.2)) then 1 else 0) : p = 1 := by
  have hq := mem_Q_of_snd_eq_one p h2
  have h := eq_one_of_rows_fixed ⟨p.1.1, hq⟩ hrows
  refine Subtype.ext (Prod.ext ?_ h2)
  exact congrArg Subtype.val h

theorem mul_negPair_fst (p : Pvis) :
    (((p * negPair : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
      -(p.1.1 : Matrix SpinIdx SpinIdx ℚ) := by
  rw [Subgroup.coe_mul, Prod.fst_mul, Units.val_mul, coe_negPair, coe_zU, zmat, Matrix.mul_neg,
    Matrix.mul_one]

theorem mul_negPair_snd (p : Pvis) :
    (((p * negPair : Pvis) : GL SpinIdx ℚ × latticeO).2 : latticeO) = p.1.2 * negOneO := by
  rw [Subgroup.coe_mul, Prod.snd_mul, coe_negPair]

theorem eq_one_of_fix_wvec {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis)
    (h1 : ∀ j : Fin 24, g (wvec false 0 j) = wvec false 0 j)
    (h2 : ∀ x ∈ rigidRows, g (wvec x.1 x.2 0) = wvec x.1 x.2 0) : g = 1 := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  set s := (p.1.1 : Matrix SpinIdx SpinIdx ℚ) with hs
  set L := mat p.1.2 with hL
  set i₀ : SpinIdx := (boolZ false, π₀ (toC 0)) with hi₀
  have hE : ∀ (j : Fin 24) (a : SpinIdx) (b : Fin 24),
      s i₀ a * L j b = (if a = i₀ then 1 else 0) * (if b = j then 1 else 0) :=
    fun j a b => entries_of_fix p false 0 j (h1 j) a b
  have hd : ∀ j, s i₀ i₀ * L j j = 1 := fun j => by simpa using hE j i₀ j
  have hs0 : s i₀ i₀ ≠ 0 := left_ne_zero_of_mul_eq_one (hd 0)
  have hLoff : ∀ j b, b ≠ j → L j b = 0 := fun j b hb => by
    have := hE j i₀ b
    rw [ite_eq_left rfl, ite_eq_right hb, mul_zero] at this
    simpa [hs0] using this
  have hLdiag : ∀ j, L j j = L 0 0 := fun j =>
    mul_left_cancel₀ hs0 ((hd j).trans (hd 0).symm)
  set μ := L 0 0 with hμ
  have hLμ : L = μ • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
    ext j b
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hjb : j = b
    · subst hjb
      rw [ite_eq_left rfl, mul_one, hLdiag]
    · rw [ite_eq_right hjb, mul_zero, hLoff j b (Ne.symm hjb)]
  have hμμ : μ * μ = 1 := by
    have h := congrFun (congrFun (mat_mul_transpose p.1.2) 0) 0
    rw [← hL, hLμ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul] at h
    simpa using h
  have hμ0 : μ ≠ 0 := left_ne_zero_of_mul_eq_one hμμ
  have hrow : ∀ x ∈ rigidRows, ∀ a : SpinIdx,
      s (boolZ x.1, π₀ (toC x.2)) a = μ * (if a = (boolZ x.1, π₀ (toC x.2)) then 1 else 0) := by
    intro x hx a
    have this : s (boolZ x.1, π₀ (toC x.2)) a * L 0 0 =
        (if a = (boolZ x.1, π₀ (toC x.2)) then 1 else 0) * (if (0 : Fin 24) = 0 then 1 else 0) :=
      entries_of_fix p x.1 x.2 0 (h2 x hx) a 0
    rw [ite_eq_left rfl, mul_one] at this
    have h3 : L 0 0 = μ := rfl
    rw [h3] at this
    calc s (boolZ x.1, π₀ (toC x.2)) a = s (boolZ x.1, π₀ (toC x.2)) a * (μ * μ) := by
          rw [hμμ, mul_one]
      _ = μ * (s (boolZ x.1, π₀ (toC x.2)) a * μ) := by ring
      _ = _ := by rw [this]
  have hrow0 : (false, 0) ∈ rigidRows := by simp [rigidRows]
  rcases mul_self_eq_one_iff.1 hμμ with hμ1 | hμ1
  ·
    have hL1 : p.1.2 = 1 := mat_injective (by rw [← hL, hLμ, hμ1, one_smul, mat_one])
    have hp1 : p = 1 := eq_one_of_snd_eq_one p hL1 fun x hx a => by
      show s (boolZ x.1, π₀ (toC x.2)) a = _
      rw [hrow x hx a, hμ1, one_mul]
    rw [hp1, thetaEquiv_one]
  ·
    have hL1 : p.1.2 = negOneO := mat_injective (by
      rw [← hL, hLμ, hμ1, neg_one_smul, mat_negOneO])
    have hp1 : p * negPair = 1 := by
      refine eq_one_of_snd_eq_one _ ?_ fun x hx a => ?_
      · rw [mul_negPair_snd, hL1, negOneO_mul_self]
      · show (((p * negPair : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ)
          (boolZ x.1, π₀ (toC x.2)) a = _
        rw [mul_negPair_fst, Matrix.neg_apply]
        show -s (boolZ x.1, π₀ (toC x.2)) a = _
        rw [hrow x hx a, hμ1]
        ring
    rw [← thetaEquiv_mul_negPair p, hp1, thetaEquiv_one]


@[expose] def rigidKeys : List (Bool × ℕ × Fin 24) :=
  (List.finRange 24).map (fun j => (false, 0, j)) ++ rigidRows.map fun x => (x.1, x.2, 0)

@[expose] def rigidDVec (k : Bool × ℕ × Fin 24) : Native.DVec :=
  Native.DVec.ofList [(98580 + 24 * Native.rowIdx k.1 k.2.1 + k.2.2, 1)]

theorem interp_rigidDVec
    (k : Bool × ℕ × Fin 24) : interp (rigidDVec k) = wvec k.1 k.2.1 k.2.2 :=
  interp_wvec _ _ _

@[expose, noinline] def checkRigid (c : Native.Ctx) (w₁ w₂ : List Native.Gen) : Bool :=
  (w₁ ++ w₂).all (fun g => g.validB) &&
    rigidKeys.all fun k =>
      (Native.evalWordC c w₁ (rigidDVec k)).eqv (Native.evalWordC c w₂ (rigidDVec k))

theorem checkRigid_sound {w₁ w₂ : List Native.Gen}
    (h : checkRigid (Native.mkCtx ()) w₁ w₂ = true) :
    ∀ k ∈ rigidKeys, wordLin w₁ (wvec k.1 k.2.1 k.2.2) = wordLin w₂ (wvec k.1 k.2.1 k.2.2) := by
  intro k hk
  unfold checkRigid at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hv, he⟩ := h
  have hw1 : ∀ g ∈ w₁, g.validB = true := fun g hg =>
    List.all_eq_true.1 hv g (List.mem_append_left _ hg)
  have hw2 : ∀ g ∈ w₂, g.validB = true := fun g hg =>
    List.all_eq_true.1 hv g (List.mem_append_right _ hg)
  have h1 := List.all_eq_true.1 he k hk
  have h2 := eqv_sound h1
  rw [evalWordC_sound w₁ hw1, evalWordC_sound w₂ hw2, interp_rigidDVec] at h2
  exact h2

theorem eq_of_fix_rigidKeys
    {a b : SpaceB ≃ₗ[ℚ] SpaceB} (ha : a ∈ Gvis) (hb : b ∈ Gvis)
    (h : ∀ k ∈ rigidKeys, a (wvec k.1 k.2.1 k.2.2) = b (wvec k.1 k.2.1 k.2.2)) : a = b := by
  have hg : b⁻¹ * a ∈ Gvis := Gvis.mul_mem (Gvis.inv_mem hb) ha
  have hfix : ∀ k ∈ rigidKeys, (b⁻¹ * a) (wvec k.1 k.2.1 k.2.2) = wvec k.1 k.2.1 k.2.2 := by
    intro k hk
    rw [LinearEquiv.mul_apply, h k hk]
    exact b.symm_apply_apply _
  have h1 : b⁻¹ * a = 1 := by
    refine eq_one_of_fix_wvec hg (fun j => hfix (false, 0, j) ?_) (fun x hx => hfix (x.1, x.2, 0) ?_)
    · unfold rigidKeys
      exact List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)
    · unfold rigidKeys
      exact List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  exact (inv_mul_eq_one.1 h1).symm

theorem wordLin_eq_of_check
    {w₁ w₂ : List Native.Gen} (hw₁ : ∀ g ∈ w₁, ¬ g = .tau)
    (hw₂ : ∀ g ∈ w₂, ¬ g = .tau) (h : checkRigid (Native.mkCtx ()) w₁ w₂ = true) :
    wordLin w₁ = wordLin w₂ :=
  eq_of_fix_rigidKeys (wordLin_mem_Gvis w₁ hw₁) (wordLin_mem_Gvis w₂ hw₂) (checkRigid_sound h)

end CFSG.Monster.Existence.Census
