module

public import CFSG.Sporadic.Schreier.Co1LocalExt
public import CFSG.Sporadic.Schreier.Co1RigidCheck
public import CFSG.Sporadic.Schreier.Co1Propagate
public import CFSG.Sporadic.Schreier.Co1Descent

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply toVecD toVecD_apply toVecD_injective
  rowsMatrix_mulRows rowsMatrix_idRows)

theorem rig_facts : Native.mul Native.qMat Native.qInv = Native.one ∧
    (∀ i < 2, Native.mul (Native.cRows i) (Native.inv (Native.cRows i)) = Native.one) ∧
    Native.mul (Native.gRows 2) (Native.inv (Native.gRows 2)) = Native.one ∧
    (∀ i < 3, Native.mul Native.xR (Native.hRows i) = Native.mul (Native.kRows i) Native.xR) ∧
    Native.mul Native.xR Native.xR = Native.one ∧
    Native.pow (Native.mul Native.xR Native.yR) 28 = Native.one ∧
    Native.aRows 1 = Native.yR ∧ Native.aRows 1 ≠ Native.one ∧ Native.wf (Native.aRows 1) = true ∧
    Native.wf Native.one = true ∧ Native.freeA.size = 8 ∧
    ∀ f < 8, (Native.freeA.getD f (0, 0)).1 < 24 ∧ (Native.freeA.getD f (0, 0)).2 < 24 := by
  have h := rig_check
  simp only [Native.rigCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, decide_eq_true_eq, and_assoc] at h
  exact h

theorem rowsMatrix_mul (X Y : Native.Rows) :
    rowsMatrix 24 (Native.mul X Y) = rowsMatrix 24 X * rowsMatrix 24 Y :=
  rowsMatrix_mulRows 24 X Y

theorem rowsMatrix_one : rowsMatrix 24 Native.one = 1 := rowsMatrix_idRows 24

theorem rowsMatrix_inj {X Y : Native.Rows} (hX : Native.wf X = true) (hY : Native.wf Y = true)
    (h : rowsMatrix 24 X = rowsMatrix 24 Y) : X = Y := by
  unfold Native.wf at hX hY
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hX hY
  obtain ⟨hXs, hXb⟩ := hX
  obtain ⟨hYs, hYb⟩ := hY
  refine Array.ext (hXs.trans hYs.symm) fun i hi hi' => ?_
  have hi24 : i < 24 := hXs ▸ hi
  refine toVecD_injective (hXb i hi) (hYb i hi') (funext fun j => ?_)
  have hij := congrFun (congrFun h ⟨i, hi24⟩) j
  rw [rowsMatrix_apply, rowsMatrix_apply, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hi', Option.getD_some, Option.getD_some] at hij
  exact hij

theorem c_rep
    (i : Fin 2) : MRep (Native.cRows i.val) (c i) :=
  (((((g_rep 2).mul (g_rep i.castSucc)).mul (g_inv_rep 2)).mul (g_inv_rep i.castSucc)).pow 2).mul
    (g_rep i.castSucc)

theorem c_inv_rep
    (i : Fin 2) : MRep (Native.inv (Native.cRows i.val)) (c i)⁻¹ :=
  (c_rep i).inv (rig_facts.2.1 i.val i.isLt)

theorem comp_listRep :
    ListRep Native.compRows (Native.compRows.map Native.inv) [c 0, c 1, r] := by
  simp only [Native.compRows, List.map_cons, List.map_nil]
  exact ⟨.cons (c_rep 0) (.cons (c_rep 1) (.cons (g_rep 2) .nil)),
    .cons (c_inv_rep 0) (.cons (c_inv_rep 1) (.cons (g_inv_rep 2) .nil))⟩

theorem locWord_rep
    (w : List ℕ × List ℕ) : MRep (Native.locRows w) (locWord w) :=
  (eProd_rep _).mul (MRep.word comp_listRep _)

theorem extH_rep
    (i : Fin 3) : MRep (Native.hRows i.val) (extH i) := locWord_rep _

theorem extK_rep
    (i : Fin 3) : MRep (Native.kRows i.val) (extK i) := locWord_rep _

theorem a_one_eq :
    a 1 = ThreeLocal.y := by
  have h := a_rep 1
  rw [show (1 : Fin 6).val = 1 from rfl, rig_facts.2.2.2.2.2.2.1] at h
  exact h.eq rep_y

theorem x_mul_extH
    (i : Fin 3) : ThreeLocal.x * extH i = extK i * ThreeLocal.x :=
  MRep.eq (rep_x.mul (extH_rep i))
    ((rig_facts.2.2.2.1 i.val i.isLt).symm ▸ (extK_rep i).mul rep_x)

noncomputable def rigQ : Mat24 := rowsMatrix 24 Native.qMat

noncomputable def rigQi : Mat24 := rowsMatrix 24 Native.qInv

theorem rigQ_mul_rigQi : rigQ * rigQi = 1 := by
  rw [rigQ, rigQi, ← rowsMatrix_mul, rig_facts.1, rowsMatrix_one]

theorem ofFn_getD {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]

noncomputable def hqM (i : Fin 3) : Mat24 := rowsMatrix 24 (Native.hqT.getD i.val Native.one)

theorem hqM_eq
    (i : Fin 3) : hqM i = rigQi * (extH i : Mat24) * rigQ := by
  rw [hqM, Native.hqT, ofFn_getD _ _ i.isLt, rowsMatrix_mul, rowsMatrix_mul, extH_rep i, rigQ,
    rigQi]

noncomputable def dqM (f : Fin 8) : Mat24 := rowsMatrix 24 (Native.dqT.getD f.val Native.one)

noncomputable def dsM (f : Fin 8) : Mat24 := rowsMatrix 24 (Native.dsT.getD f.val Native.one)

theorem dsM_eq (f : Fin 8) : dsM f = rigQ * dqM f * rigQi := by
  rw [dsM, Native.dsT, ofFn_getD _ _ f.isLt, rowsMatrix_mul, rowsMatrix_mul, rigQ, rigQi, dqM]

theorem basis_facts :
    ∀ f < 8, (∀ i < 3, Native.mul (Native.dqT.getD f Native.one)
      (Native.hqT.getD i Native.one) =
      Native.mul (Native.hqT.getD i Native.one) (Native.dqT.getD f Native.one)) ∧
    ∀ g < 8, ((Native.dqT.getD f Native.one).getD (Native.freeA.getD g (0, 0)).1 0).testBit
      (Native.freeA.getD g (0, 0)).2 = decide (f = g) := by
  have h := basis_check
  simp only [Native.basisCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  intro f hf
  refine ⟨(h f hf).1, fun g hg => ?_⟩
  rw [(h f hf).2 g hg]
  exact Bool.beq_eq_decide_eq f g

theorem dqM_comm
    (f : Fin 8) (i : Fin 3) : dqM f * hqM i = hqM i * dqM f := by
  rw [dqM, hqM, ← rowsMatrix_mul, ← rowsMatrix_mul, (basis_facts f.val f.isLt).1 i.val i.isLt]

@[expose] def freeP (f : Fin 8) : Fin 24 × Fin 24 :=
  (Fin.ofNat 24 (Native.freeA.getD f.val (0, 0)).1, Fin.ofNat 24 (Native.freeA.getD f.val (0, 0)).2)

theorem freeP_val (f : Fin 8) : ((freeP f).1.val, (freeP f).2.val) =
    Native.freeA.getD f.val (0, 0) := by
  have h := rig_facts.2.2.2.2.2.2.2.2.2.2.2 f.val f.isLt
  simp only [freeP, Fin.val_ofNat, Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h.2]

theorem dqM_free
    (f g : Fin 8) : dqM f (freeP g).1 (freeP g).2 = if f = g then 1 else 0 := by
  have h := (basis_facts f.val f.isLt).2 g.val g.isLt
  have hv := freeP_val g
  simp only [Prod.ext_iff] at hv
  rw [dqM, rowsMatrix_apply, toVecD_apply, ← Array.getD_eq_getD_getElem?, hv.1, hv.2, h]
  by_cases hfg : f = g
  · simp only [hfg, decide_true, ↓reduceIte]
  · have : f.val ≠ g.val := fun h' => hfg (Fin.ext h')
    simp only [this, hfg, decide_false, Bool.false_eq_true, ↓reduceIte]

@[expose] def rigRank (u : Fin 24 × Fin 24) : ℕ := Native.rankA.getD (24 * u.1.val + u.2.val) 0

@[expose] def rigEqs (u : Fin 24 × Fin 24) : List ℕ :=
  Native.eqsA.getD (24 * u.1.val + u.2.val) []

@[expose] def rigN (c : ℕ) (u : Fin 24 × Fin 24) : ZMod 2 :=
  if Native.coefB c u.1.val u.2.val then 1 else 0

theorem rigN_sum (u v : Fin 24 × Fin 24) :
    ((rigEqs u).map fun c => rigN c v).sum =
      if Native.combB (24 * u.1.val + u.2.val) v.1.val v.2.val then 1 else 0 := by
  have h := Propagate.xor_sum (fun c => Native.coefB c v.1.val v.2.val) (rigEqs u) false
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
  exact h

theorem rig_step (u : Fin 24 × Fin 24) (hu : 0 < rigRank u) :
    ((rigEqs u).map fun c => rigN c u).sum = 1 ∧
      ∀ v, v ≠ u → rigRank u ≤ rigRank v → ((rigEqs u).map fun c => rigN c v).sum = 0 := by
  have h := prop_check
  simp only [Native.propCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  have hn : 24 * u.1.val + u.2.val < 576 := by omega
  have hdiv : ∀ p q : Fin 24,
      (24 * p.val + q.val) / 24 = p.val ∧ (24 * p.val + q.val) % 24 = q.val :=
    fun p q => ⟨by omega, by omega⟩
  rcases h _ hn with h0 | ⟨h1, h2⟩
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp hu)
  · rw [(hdiv u.1 u.2).1, (hdiv u.1 u.2).2] at h1
    refine ⟨by simp only [rigN_sum, h1, ↓reduceIte], fun v hv hr => ?_⟩
    have hvn : 24 * v.1.val + v.2.val < 576 := by omega
    rcases h2 _ hvn with (he | hlt) | hc
    · exact absurd (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))) hv
    · exact absurd hr (not_le.mpr hlt)
    · rw [(hdiv v.1 v.2).1, (hdiv v.1 v.2).2] at hc
      rw [rigN_sum, hc]
      rfl

theorem ite_xor_eq (P Q : Prop) [Decidable P] [Decidable Q] (b₁ b₂ : Bool) :
    (if ((decide P && b₁) ^^ (decide Q && b₂)) = true then (1 : ZMod 2) else 0) =
      (if P then (if b₁ = true then 1 else 0) else 0) -
        (if Q then (if b₂ = true then 1 else 0) else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> cases b₁ <;> cases b₂ <;> simp [hP, hQ] <;> decide

theorem rigN_eq (c : ℕ) (u : Fin 24 × Fin 24) :
    rigN c u = Descent.coeff (hqM (Fin.ofNat 3 (c / 576))) (hqM (Fin.ofNat 3 (c / 576)))
      (Fin.ofNat 24 (c / 24)) (Fin.ofNat 24 c) u.1 u.2 := by
  unfold rigN Native.coefB Descent.coeff hqM
  simp only [rowsMatrix_apply, toVecD_apply, Fin.ext_iff, Fin.val_ofNat,
    ← Array.getD_eq_getD_getElem?, Bool.beq_eq_decide_eq]
  exact ite_xor_eq _ _ _ _

theorem free_facts
    (u : Fin 24 × Fin 24) (hu : rigRank u = 0) : ∃ f, freeP f = u := by
  have h := free_check
  simp only [Native.freeCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    ne_eq, List.any_eq_true, beq_iff_eq] at h
  have hn : 24 * u.1.val + u.2.val < 576 := by omega
  rcases h _ hn with h0 | ⟨f, hf, hfe⟩
  · exact absurd hu h0
  · refine ⟨⟨f, hf⟩, ?_⟩
    have hv := freeP_val ⟨f, hf⟩
    rw [hfe] at hv
    simp only [Prod.mk.injEq] at hv
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem comm_eq_sum {T : Mat24} (hT : ∀ i, T * hqM i = hqM i * T) :
    T = ∑ f, T (freeP f).1 (freeP f).2 • dqM f := by
  have hT' : ∀ i, (T - ∑ f, T (freeP f).1 (freeP f).2 • dqM f) * hqM i =
      hqM i * (T - ∑ f, T (freeP f).1 (freeP f).2 • dqM f) := by
    intro i
    have hs : ∑ f, (T (freeP f).1 (freeP f).2 • dqM f) * hqM i =
        ∑ f, hqM i * (T (freeP f).1 (freeP f).2 • dqM f) :=
      Finset.sum_congr rfl fun f _ => by rw [smul_mul_assoc, mul_smul_comm, dqM_comm]
    rw [sub_mul, mul_sub, hT i, Finset.sum_mul, Finset.mul_sum, hs]
  have h0 := Propagate.eq_zero_of_steps rigN rigRank rigEqs rig_step
    (t := fun u => (T - ∑ f, T (freeP f).1 (freeP f).2 • dqM f) u.1 u.2) (fun c => by
      simp only [rigN_eq]
      rw [Descent.intertwine_sum, hT', sub_self, Matrix.zero_apply]) (fun u hu => by
      obtain ⟨g, rfl⟩ := free_facts u hu
      show (T - ∑ f, T (freeP f).1 (freeP f).2 • dqM f) (freeP g).1 (freeP g).2 = 0
      have hs : ∑ f, (T (freeP f).1 (freeP f).2 • dqM f) (freeP g).1 (freeP g).2 =
          T (freeP g).1 (freeP g).2 := by
        rw [Finset.sum_eq_single g]
        · rw [Matrix.smul_apply, dqM_free]
          simp only [↓reduceIte, smul_eq_mul, mul_one]
        · intro f _ hfg
          rw [Matrix.smul_apply, dqM_free]
          simp only [hfg, ↓reduceIte, smul_zero]
        · intro h
          exact absurd (Finset.mem_univ g) h
      rw [Matrix.sub_apply, Matrix.sum_apply, hs, sub_self])
  rw [← sub_eq_zero]
  ext i j
  exact congrFun h0 (i, j)

theorem zeroRows_eq : rowsMatrix 24 Native.zeroRows = 0 := by
  ext i j
  rw [rowsMatrix_apply, Native.zeroRows, Array.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, Matrix.zero_apply, toVecD_apply,
    Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

theorem candRows_eq (ε : Fin 8 → ZMod 2) :
    rowsMatrix 24 (Native.candRows fun f => decide (ε f = 1)) = ∑ f, ε f • dsM f := by
  have key : ∀ (l : List (Fin 8)) (R : Native.Rows), rowsMatrix 24 (l.foldl (fun R f =>
      if decide (ε f = 1) then Native.add R (Native.dsT.getD f.val Native.one) else R) R) =
      rowsMatrix 24 R + (l.map fun f => ε f • dsM f).sum := by
    intro l
    induction l with
    | nil => intro R; rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons f l ih =>
      intro R
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
      congr 1
      rcases zmod2_cases (ε f) with h | h
      · simp only [h, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, zero_smul,
          add_zero]
      · simp only [h, decide_true, ↓reduceIte, one_smul, rowsMatrix_add, dsM]
  rw [Native.candRows, key, zeroRows_eq, zero_add, Fin.sum_univ_def]

theorem rigidity_main
    (X : GL24) (hX : ∀ i, X * extH i = extK i * X) (hX2 : X ^ 2 = 1)
    (hX28 : (X * a 1) ^ 28 = 1) : X = ThreeLocal.x := by
  have hT : ∀ i, ThreeLocal.x⁻¹ * X * extH i = extH i * (ThreeLocal.x⁻¹ * X) := by
    intro i
    have hk : extK i = ThreeLocal.x * extH i * ThreeLocal.x⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact (x_mul_extH i).symm
    rw [mul_assoc, hX i, hk]
    group
  obtain ⟨Tm, hTm⟩ : ∃ M : Mat24, M = ((ThreeLocal.x⁻¹ * X : GL24) : Mat24) := ⟨_, rfl⟩
  have hTh : ∀ i, Tm * (extH i : Mat24) = (extH i : Mat24) * Tm := fun i => by
    rw [hTm, ← Units.val_mul, hT i, Units.val_mul]
  have hT' : ∀ i, (rigQi * Tm * rigQ) * hqM i = hqM i * (rigQi * Tm * rigQ) := by
    intro i
    rw [hqM_eq]
    calc rigQi * Tm * rigQ * (rigQi * (extH i : Mat24) * rigQ)
        = rigQi * (Tm * (rigQ * rigQi) * (extH i : Mat24)) * rigQ := by
          simp only [mul_assoc]
      _ = rigQi * ((extH i : Mat24) * Tm) * rigQ := by rw [rigQ_mul_rigQi, mul_one, hTh]
      _ = rigQi * (extH i : Mat24) * (rigQ * rigQi) * Tm * rigQ := by
          rw [rigQ_mul_rigQi, mul_one]
          simp only [mul_assoc]
      _ = rigQi * (extH i : Mat24) * rigQ * (rigQi * Tm * rigQ) := by simp only [mul_assoc]
  have hsum := comm_eq_sum hT'
  have hTeq : Tm = ∑ f, (rigQi * Tm * rigQ) (freeP f).1 (freeP f).2 • dsM f := by
    have e1 : Tm = rigQ * (rigQi * Tm * rigQ) * rigQi := by
      simp only [← mul_assoc, rigQ_mul_rigQi, one_mul]
      rw [mul_assoc, rigQ_mul_rigQi, mul_one]
    calc Tm = rigQ * (rigQi * Tm * rigQ) * rigQi := e1
      _ = rigQ * (∑ f, (rigQi * Tm * rigQ) (freeP f).1 (freeP f).2 • dqM f) * rigQi := by
          rw [← hsum]
      _ = ∑ f, (rigQi * Tm * rigQ) (freeP f).1 (freeP f).2 • dsM f := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [dsM_eq, mul_smul_comm, smul_mul_assoc]
  have hRep : MRep (Native.candRows fun f => decide
      ((rigQi * Tm * rigQ) (freeP f).1 (freeP f).2 = 1)) (ThreeLocal.x⁻¹ * X) :=
    ((candRows_eq _).trans hTeq.symm).trans hTm
  have hXrep : MRep (Native.mul Native.xR (Native.candRows fun f => decide
      ((rigQi * Tm * rigQ) (freeP f).1 (freeP f).2 = 1))) X := by
    have h := rep_x.mul hRep
    rwa [mul_inv_cancel_left] at h
  have hX2rep := hXrep.mul hXrep
  rw [← pow_two, hX2] at hX2rep
  have hX28rep := (hXrep.mul rep_y).pow 28
  rw [← a_one_eq, hX28] at hX28rep
  have hok := cand_check fun f => decide ((rigQi * Tm * rigQ) (freeP f).1 (freeP f).2 = 1)
  simp only [Native.candOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at hok
  obtain ⟨⟨hw1, hw2⟩, hc⟩ := hok
  have hone := rig_facts.2.2.2.2.2.2.2.2.2.1
  rcases hc with (h | h) | h
  · exact absurd (rowsMatrix_inj hw1 hone (hX2rep.trans MRep.one.symm)) h
  · exact absurd (rowsMatrix_inj hw2 hone (hX28rep.trans MRep.one.symm)) h
  · have hT1 : ThreeLocal.x⁻¹ * X = 1 := MRep.eq (h ▸ hRep) MRep.one
    calc X = ThreeLocal.x * (ThreeLocal.x⁻¹ * X) := by rw [mul_inv_cancel_left]
      _ = ThreeLocal.x := by rw [hT1, mul_one]

theorem local_extension_matrix_rigidity :
    a 1 = ThreeLocal.y ∧ a 1 ≠ 1 ∧ ThreeLocal.x ^ 2 = 1 ∧ (ThreeLocal.x * a 1) ^ 28 = 1 ∧
    (∀ i : Fin 3, ThreeLocal.x * extH i = extK i * ThreeLocal.x) ∧
    ∀ X : GL (Fin 24) (ZMod 2), (∀ i : Fin 3, X * extH i = extK i * X) → X ^ 2 = 1 →
      (X * a 1) ^ 28 = 1 → X = ThreeLocal.x := by
  refine ⟨a_one_eq, fun h => ?_, ?_, ?_, x_mul_extH, rigidity_main⟩
  · have h1 := a_rep 1
    rw [h] at h1
    exact rig_facts.2.2.2.2.2.2.2.1 (rowsMatrix_inj rig_facts.2.2.2.2.2.2.2.2.1
      rig_facts.2.2.2.2.2.2.2.2.2.1 (h1.trans MRep.one.symm))
  · rw [pow_two]
    exact MRep.eq (rep_x.mul rep_x) (rig_facts.2.2.2.2.1 ▸ MRep.one)
  · rw [a_one_eq]
    exact MRep.eq ((rep_x.mul rep_y).pow 28) (rig_facts.2.2.2.2.2.1 ▸ MRep.one)

end CFSG.Sporadic.Co1Schreier
