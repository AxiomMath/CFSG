module

public import CFSG.Sporadic.J4.QTOutCommCheck
public import CFSG.Sporadic.J4.QTOutObs

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native Matrix

theorem get!_eq (X : Array V2) (i : ℕ) : X[i]! = X[i]?.getD V2.zero := by
  rw [getElem!_def]
  cases X[i]? <;> rfl

theorem rowsMatrix_xorMat (X Y : Array V2) :
    rowsMatrix (xorMat X Y) = rowsMatrix X + rowsMatrix Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold xorMat
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [get!_eq, get!_eq, V2.toVec_xor]
  rfl

theorem rowsMatrix_zeroMat : rowsMatrix zeroMat = 0 := by
  ext i j
  rw [rowsMatrix_apply]
  unfold zeroMat
  rw [Array.getElem?_replicate]
  split_ifs <;> simp [V2.toVec_zero]

theorem rowsMatrix_psiRows (s : ℕ) (i j : Fin 112) :
    rowsMatrix (psiRows s) i j = if s ≤ i.val ∧ j.val = i.val - s then 1 else 0 := by
  rw [rowsMatrix_apply]
  unfold psiRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [V2.toVec_ofFn]
  simp

theorem wmats_get {l : ℕ} (hl : l < 111) : wmats[l]! = wmat l := by
  simp [wmats, hl]

theorem edgeMats_get {e : ℕ} (he : e < 6) : edgeMats[e]! = edgeMat e := by
  simp [edgeMats, he]

theorem pRows_get {i : ℕ} (hi : i < 111) : pRows[i]?.getD V2.zero = bvec i := by
  simp only [pRows, List.getElem?_toArray]
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, List.getElem?_range hi]
  rfl

theorem pRows_get111 : pRows[111]?.getD V2.zero = v1Vec := by
  simp [pRows]

theorem qRows_get {i : ℕ} (hi : i < 111) (U0 U1 : V2) :
    (qRows U0 U1)[i]?.getD V2.zero = frApply (wTabs[i]!) U0 := by
  simp only [qRows, List.getElem?_toArray]
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, List.getElem?_range hi]
  rfl

theorem qRows_get111 (U0 U1 : V2) : (qRows U0 U1)[111]?.getD V2.zero = U1 := by
  simp [qRows]

theorem wTabs_get {l : ℕ} (hl : l < 111) : wTabs[l]! = frTable (wmat l) := by
  simp [wTabs, wmats, hl]

def CommRows (T : Matrix (Fin 112) (Fin 112) (ZMod 2)) (X : Array V2) : Prop :=
  T * rowsMatrix X = rowsMatrix X * T

theorem commRows_id (T : Matrix (Fin 112) (Fin 112) (ZMod 2)) : CommRows T idRows := by
  unfold CommRows
  rw [rowsMatrix_idRows, mul_one, one_mul]

theorem commRows_zero (T : Matrix (Fin 112) (Fin 112) (ZMod 2)) : CommRows T zeroMat := by
  unfold CommRows
  rw [rowsMatrix_zeroMat, mul_zero, zero_mul]

theorem commRows_mul {T : Matrix (Fin 112) (Fin 112) (ZMod 2)} {X Y : Array V2} (hX : CommRows T X)
    (hY : CommRows T Y) : CommRows T (mulRows X Y) := by
  unfold CommRows at *
  rw [rowsMatrix_mulRows, ← mul_assoc, hX, mul_assoc, hY, mul_assoc]

theorem commRows_xor {T : Matrix (Fin 112) (Fin 112) (ZMod 2)} {X Y : Array V2} (hX : CommRows T X)
    (hY : CommRows T Y) : CommRows T (xorMat X Y) := by
  unfold CommRows at *
  rw [rowsMatrix_xorMat, mul_add, add_mul, hX, hY]

theorem kEdge_lt {e : ℕ} (he : e < 6) : (kEdges.getD e (0, 0)).1 < 111 := by
  have hlen : e < kEdges.length := by rw [comm_kEdges_length]; exact he
  rw [List.getD_eq_getElem _ _ hlen]
  exact comm_edges_lt _ (List.getElem_mem hlen)

section Comm

variable {T : Matrix (Fin 112) (Fin 112) (ZMod 2)} (h0 : CommRows T mat0) (h1 : CommRows T mat1)
include h0 h1

theorem commRows_mg (g : ℕ) : CommRows T (mg g) := by
  unfold mg
  split_ifs
  · exact h0
  · exact h1

theorem commRows_path :
    ∀ (w : List ℕ) (acc : Array V2), CommRows T acc →
      CommRows T (w.foldl (fun acc g => mulRows acc (mg g)) acc)
  | [], _, ha => ha
  | g :: w, acc, ha => by
    rw [List.foldl_cons]
    exact commRows_path w _ (commRows_mul ha (commRows_mg h0 h1 g))

theorem commRows_wmat (l : ℕ) : CommRows T (wmat l) := by
  unfold wmat pathMat
  exact commRows_path h0 h1 _ _ (commRows_id T)

theorem commRows_wmats {l : ℕ} (hl : l < 111) : CommRows T (wmats[l]!) := by
  rw [wmats_get hl]
  exact commRows_wmat h0 h1 l

theorem commRows_sumW (c : V2) : CommRows T (sumW c) := by
  have key : ∀ (L : List ℕ) (acc : Array V2), CommRows T acc → (∀ l ∈ L, l < 111) →
      CommRows T
        (L.foldl (fun acc l => if c.testBit l then xorMat acc (wmats[l]!) else acc) acc) := by
    intro L
    induction L with
    | nil => intro acc ha _; exact ha
    | cons l L ih =>
      intro acc ha hL
      rw [List.foldl_cons]
      refine ih _ ?_ (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      split_ifs
      · exact commRows_xor ha (commRows_wmats h0 h1 (hL l (List.mem_cons_self ..)))
      · exact ha
  exact key _ _ (commRows_zero T) (fun l hl => List.mem_range.1 hl)

theorem commRows_edgeMat {e : ℕ} (he : e < 6) : CommRows T (edgeMat e) := by
  unfold edgeMat
  exact commRows_xor (commRows_mul (commRows_wmats h0 h1 (kEdge_lt he)) (commRows_mg h0 h1 _))
    (commRows_sumW h0 h1 _)

theorem commRows_rg (g : ℕ) : CommRows T (rg g) := commRows_sumW h0 h1 _

theorem commRows_mgp (g : ℕ) : CommRows T (mgp g) := by
  unfold mgp
  exact commRows_xor (commRows_mg h0 h1 g) (commRows_id T)

end Comm

theorem vecMul_swap {T X : Matrix (Fin 112) (Fin 112) (ZMod 2)} (h : T * X = X * T)
    (a : Fin 112 → ZMod 2) : (a ᵥ* T) ᵥ* X = (a ᵥ* X) ᵥ* T := by
  rw [Matrix.vecMul_vecMul, h, ← Matrix.vecMul_vecMul]

theorem v0_rel {e : ℕ} (he : e < 6) : v0Vec.toVec ᵥ* rowsMatrix (edgeMat e) = 0 := by
  have := V2.beq_iff.1 (comm_rel e he)
  rw [← frApply_toVec_eq_vecMul, this, V2.toVec_zero]

theorem v1_rg {g : ℕ} (hg : g < 2) :
    v1Vec.toVec ᵥ* rowsMatrix (mgp g) = v0Vec.toVec ᵥ* rowsMatrix (rg g) := by
  have h1 := congrArg V2.toVec (V2.beq_iff.1 (comm_rg g hg))
  rw [frApply_toVec_eq_vecMul, V2.toVec_xor, frApply_toVec_eq_vecMul] at h1
  rw [h1]
  unfold mgp
  rw [rowsMatrix_xorMat, rowsMatrix_idRows, Matrix.vecMul_add, Matrix.vecMul_one]

theorem u1s_rel {i : ℕ} (hi : i < 4) {g : ℕ} (hg : g < 2) :
    (u1s[i]!).toVec ᵥ* rowsMatrix (mgp g) = (bkRows[i]!).toVec ᵥ* rowsMatrix (rg g) := by
  have := V2.beq_iff.1 (comm_u1 i hi g hg)
  rw [← frApply_toVec_eq_vecMul, ← frApply_toVec_eq_vecMul, this]

theorem rowsMatrix_phiOf (mats : Array (Array V2)) (cols : List (Nat × Nat)) (i m : Fin 112) :
    rowsMatrix (phiOf mats cols) i m =
      match cols[m.val]? with
      | some (e, c) => if ((mats[e]!)[i.val]!).testBit c then 1 else 0
      | none => 0 := by
  rw [rowsMatrix_apply]
  unfold phiOf
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [V2.toVec_ofFn]
  rcases h : cols[m.val]? with _ | ⟨e, c⟩ <;> simp

theorem vecMul_phiOf {mats : Array (Array V2)} {cols : List (Nat × Nat)} (z : Fin 112 → ZMod 2)
    (hcols : ∀ c ∈ cols, c.1 < mats.size ∧ c.2 < 112)
    (hz : ∀ e < mats.size, z ᵥ* rowsMatrix (mats[e]!) = 0) :
    z ᵥ* rowsMatrix (phiOf mats cols) = 0 := by
  funext m
  show ∑ i, z i * rowsMatrix (phiOf mats cols) i m = 0
  simp only [rowsMatrix_phiOf]
  rcases h : cols[m.val]? with _ | ⟨e, c⟩
  · simp
  · obtain ⟨he, hc⟩ := hcols _ (List.mem_of_getElem? h)
    have h1 := congrFun (hz e he) ⟨c, hc⟩
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h1
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    dsimp only
    rw [rowsMatrix_apply, V2.toVec_apply, get!_eq]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  revert c
  decide

theorem vec_add_self (v : Fin 112 → ZMod 2) : v + v = 0 := by
  funext j
  exact zmod2_add_self _

def toB (c : ZMod 2) : Bool := decide (c = 1)

theorem selV_toVec (c : ZMod 2) (x : V2) : (selV (toB c) x).toVec = c • x.toVec := by
  rcases zmod2_cases c with rfl | rfl
  · simp [toB, selV, V2.toVec_zero]
  · simp [toB, selV]

theorem kappaComb_toVec (c0 c1 c2 c3 : ZMod 2) :
    (kappaComb (toB c0) (toB c1) (toB c2) (toB c3)).toVec =
      c0 • (bkRows[0]!).toVec + c1 • (bkRows[1]!).toVec + c2 • (bkRows[2]!).toVec +
        c3 • (bkRows[3]!).toVec := by
  unfold kappaComb
  rw [V2.toVec_xor, V2.toVec_xor, V2.toVec_xor, selV_toVec, selV_toVec, selV_toVec, selV_toVec]
  abel

theorem uComb_toVec (c0 c1 c2 c3 : ZMod 2) :
    (uComb (toB c0) (toB c1) (toB c2) (toB c3)).toVec =
      c0 • (u1s[0]!).toVec + c1 • (u1s[1]!).toVec + c2 • (u1s[2]!).toVec +
        c3 • (u1s[3]!).toVec := by
  unfold uComb
  rw [V2.toVec_xor, V2.toVec_xor, V2.toVec_xor, selV_toVec, selV_toVec, selV_toVec, selV_toVec]
  abel

theorem fixComb_toVec (d0 d1 : ZMod 2) :
    (fixComb (toB d0) (toB d1)).toVec = d0 • (bfRows[0]!).toVec + d1 • (bfRows[1]!).toVec := by
  unfold fixComb
  rw [V2.toVec_xor, selV_toVec, selV_toVec]

theorem fin112_lt_four : ∀ i : Fin 112, i.val < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide

theorem fin112_lt_two : ∀ i : Fin 112, i.val < 2 → i = 0 ∨ i = 1 := by decide

theorem sum_four (f : Fin 112 → ZMod 2) (h : ∀ i : Fin 112, 4 ≤ i.val → f i = 0) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  have h1 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 112)), f i = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply h
    by_contra hlt
    apply hi
    have hi4 : i.val < 4 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fin112_lt_four i hi4
  rw [← h1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem sum_two (f : Fin 112 → ZMod 2) (h : ∀ i : Fin 112, 2 ≤ i.val → f i = 0) :
    ∑ i, f i = f 0 + f 1 := by
  have h1 : ∑ i ∈ ({0, 1} : Finset (Fin 112)), f i = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply h
    by_contra hlt
    apply hi
    have hi2 : i.val < 2 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fin112_lt_two i hi2
  rw [← h1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem vecMul_four (M : Array V2) (c : Fin 112 → ZMod 2)
    (hc : ∀ i : Fin 112, 4 ≤ i.val → c i = 0) :
    c ᵥ* rowsMatrix M = c 0 • (M[0]!).toVec + c 1 • (M[1]!).toVec + c 2 • (M[2]!).toVec +
      c 3 • (M[3]!).toVec := by
  funext j
  show ∑ i, c i * rowsMatrix M i j = _
  rw [sum_four (fun i => c i * rowsMatrix M i j) (fun i hi => by rw [hc i hi, zero_mul])]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rowsMatrix_apply, get!_eq]
  rfl

theorem vecMul_two (M : Array V2) (c : Fin 112 → ZMod 2)
    (hc : ∀ i : Fin 112, 2 ≤ i.val → c i = 0) :
    c ᵥ* rowsMatrix M = c 0 • (M[0]!).toVec + c 1 • (M[1]!).toVec := by
  funext j
  show ∑ i, c i * rowsMatrix M i j = _
  rw [sum_two (fun i => c i * rowsMatrix M i j) (fun i hi => by rw [hc i hi, zero_mul])]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rowsMatrix_apply, get!_eq]
  rfl

theorem pRows_mul {T : Matrix (Fin 112) (Fin 112) (ZMod 2)} (h0 : CommRows T mat0)
    (h1 : CommRows T mat1) (U0 U1 : V2) (hU0 : v0Vec.toVec ᵥ* T = U0.toVec)
    (hU1 : v1Vec.toVec ᵥ* T = U1.toVec) : rowsMatrix pRows * T = rowsMatrix (qRows U0 U1) := by
  have hrow : ∀ (X : Array V2) (i : Fin 112),
      (rowsMatrix X * T) i = (X[i.val]?.getD V2.zero).toVec ᵥ* T := fun X i => rfl
  have key : ∀ i : Fin 112, (rowsMatrix pRows * T) i = rowsMatrix (qRows U0 U1) i := by
    intro i
    rw [hrow]
    show _ = ((qRows U0 U1)[i.val]?.getD V2.zero).toVec
    by_cases hi : i.val < 111
    · rw [pRows_get hi, qRows_get hi]
      unfold bvec
      rw [wTabs_get hi, frApply_toVec_eq_vecMul, frApply_toVec_eq_vecMul,
        ← vecMul_swap (commRows_wmat h0 h1 i.val), hU0]
    · have : i.val = 111 := by omega
      rw [this, pRows_get111, qRows_get111, hU1]
  exact Matrix.ext fun i k => congrFun (key i) k

theorem commutant_form {T : Matrix (Fin 112) (Fin 112) (ZMod 2)} (h0 : CommRows T mat0)
    (h1 : CommRows T mat1) :
    ∃ b0 b1 b2 b3 d0 d1 : Bool, T = rowsMatrix (tcomb b0 b1 b2 b3 d0 d1) := by
  obtain ⟨u0, hu0⟩ : ∃ u0, u0 = v0Vec.toVec ᵥ* T := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1, u1 = v1Vec.toVec ᵥ* T := ⟨_, rfl⟩
  have hker : u0 ᵥ* rowsMatrix (phiOf edgeMats kCols) = 0 := by
    refine vecMul_phiOf u0 (fun c hc => ?_) (fun e he => ?_)
    · have hsz : edgeMats.size = 6 := by simp [edgeMats]
      rw [hsz]
      exact ⟨(comm_cols.1 c hc).1, (comm_cols.1 c hc).2⟩
    · have he6 : e < 6 := by simpa [edgeMats] using he
      rw [edgeMats_get he6, hu0, vecMul_swap (commRows_edgeMat h0 h1 he6), v0_rel he6,
        Matrix.zero_vecMul]
  have hBinvK : rowsMatrix (invRows bkRows) * rowsMatrix bkRows = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 comm_K.2)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hΨK : ∀ i j : Fin 112, (rowsMatrix bkRows * rowsMatrix (phiOf edgeMats kCols)) i j =
      if 4 ≤ i.val ∧ j.val = i.val - 4 then 1 else 0 := by
    intro i j
    have := congrArg rowsMatrix (eqRows_iff.1 comm_K.1)
    rw [rowsMatrix_mulRows] at this
    rw [this, rowsMatrix_psiRows]
  obtain ⟨c, hcu, hc⟩ := kernel_span hBinvK hΨK u0 hker
  have hu0K : u0 = (kappaComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec := by
    rw [hcu, vecMul_four _ _ hc, kappaComb_toVec]
  have hw : ∀ e < mgps.size,
      (u1 + (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec) ᵥ*
        rowsMatrix (mgps[e]!) = 0 := by
    intro e he
    have he2 : e < 2 := by simpa [mgps] using he
    have hmg : mgps[e]! = mgp e := by
      interval_cases e <;> rfl
    rw [hmg, Matrix.add_vecMul]
    have e1 : u1 ᵥ* rowsMatrix (mgp e) = u0 ᵥ* rowsMatrix (rg e) := by
      rw [hu1, vecMul_swap (commRows_mgp h0 h1 e), v1_rg he2, ← vecMul_swap (commRows_rg h0 h1 e),
        ← hu0]
    have e2 : (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec ᵥ*
        rowsMatrix (mgp e) = u0 ᵥ* rowsMatrix (rg e) := by
      rw [uComb_toVec, hu0K, kappaComb_toVec]
      simp only [Matrix.add_vecMul, Matrix.smul_vecMul]
      rw [u1s_rel (by norm_num) he2, u1s_rel (by norm_num) he2, u1s_rel (by norm_num) he2,
        u1s_rel (by norm_num) he2]
    rw [e1, e2]
    exact vec_add_self _
  have hkerF : (u1 + (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec) ᵥ*
      rowsMatrix (phiOf mgps fCols) = 0 := by
    refine vecMul_phiOf _ (fun c' hc' => ?_) hw
    have hsz : mgps.size = 2 := by simp [mgps]
    rw [hsz]
    exact ⟨(comm_cols.2 c' hc').1, (comm_cols.2 c' hc').2⟩
  have hBinvF : rowsMatrix (invRows bfRows) * rowsMatrix bfRows = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 comm_F.2)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hΨF : ∀ i j : Fin 112, (rowsMatrix bfRows * rowsMatrix (phiOf mgps fCols)) i j =
      if 2 ≤ i.val ∧ j.val = i.val - 2 then 1 else 0 := by
    intro i j
    have := congrArg rowsMatrix (eqRows_iff.1 comm_F.1)
    rw [rowsMatrix_mulRows] at this
    rw [this, rowsMatrix_psiRows]
  obtain ⟨d, hdu, hd⟩ := kernel_span hBinvF hΨF _ hkerF
  have hu1F : u1 = (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec +
      (fixComb (toB (d 0)) (toB (d 1))).toVec := by
    rw [fixComb_toVec, ← vecMul_two _ _ hd, ← hdu]
    have := vec_add_self (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec
    calc u1 = (u1 + (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec) +
          (uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).toVec := by
          rw [add_assoc, this, add_zero]
      _ = _ := by rw [add_comm]
  refine ⟨toB (c 0), toB (c 1), toB (c 2), toB (c 3), toB (d 0), toB (d 1), ?_⟩
  have hPinv : rowsMatrix pInv * rowsMatrix pRows = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 comm_pinv.1)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hPT := pRows_mul h0 h1
    (kappaComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3)))
    ((uComb (toB (c 0)) (toB (c 1)) (toB (c 2)) (toB (c 3))).xor
      (fixComb (toB (d 0)) (toB (d 1))))
    (by rw [← hu0, hu0K]) (by rw [V2.toVec_xor, ← hu1F, ← hu1])
  calc T = rowsMatrix pInv * (rowsMatrix pRows * T) := by rw [← mul_assoc, hPinv, one_mul]
    _ = _ := by rw [hPT, ← rowsMatrix_mulRows]; rfl

theorem rowsMatrix_powFuel (fuel : ℕ) : ∀ (M : Array V2) (e : ℕ), e < 2 ^ fuel →
    rowsMatrix (powFuel M fuel e) = rowsMatrix M ^ e := by
  induction fuel with
  | zero =>
    intro M e he
    have : e = 0 := by simpa using he
    subst this
    simp [powFuel, rowsMatrix_idRows]
  | succ fuel ih =>
    intro M e he
    by_cases h0 : e = 0
    · subst h0
      simp [powFuel, rowsMatrix_idRows]
    · have hlt : e / 2 < 2 ^ fuel := by rw [pow_succ] at he; omega
      have ih' := ih (mulRows M M) (e / 2) hlt
      rw [rowsMatrix_mulRows, ← pow_two, ← pow_mul] at ih'
      unfold powFuel
      dsimp only
      split_ifs with hA
      · rw [rowsMatrix_mulRows, ih', ← pow_succ']
        congr 1
        omega
      · rw [ih']
        congr 1
        omega

theorem rowsMatrix_powBin (M : Array V2) {e : ℕ} (he : e < 2 ^ 128) :
    rowsMatrix (powBin M e) = rowsMatrix M ^ e :=
  rowsMatrix_powFuel 128 M e he

noncomputable def jgenJ (g : ℕ) : J := if g = 0 then a else if g = 1 then b else b⁻¹

noncomputable def jwordJ (w : List ℕ) : J := (w.map jgenJ).prod

section Words

variable (hM : MatFacts)
include hM

theorem Mx_jgenJ (g : ℕ) : Mx (jgenJ g) = rowsMatrix (jgen g) := by
  unfold jgenJ jgen
  split_ifs
  · exact Mx_a hM
  · exact Mx_b hM
  · exact Mx_b_inv hM

theorem Mx_jword (w : List ℕ) : Mx (jwordJ w) = rowsMatrix (jword w) := by
  have key : ∀ (w : List ℕ) (acc : Array V2),
      rowsMatrix (w.foldl (fun acc g => mulRows acc (jgen g)) acc) =
        rowsMatrix acc * Mx (jwordJ w) := by
    intro w
    induction w with
    | nil =>
      intro acc
      have : jwordJ ([] : List ℕ) = 1 := rfl
      rw [List.foldl_nil, this, map_one, mul_one]
    | cons g w ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, mul_assoc]
      unfold jwordJ
      rw [List.map_cons, List.prod_cons, map_mul, Mx_jgenJ hM]
  unfold jword
  rw [key w idRows, rowsMatrix_idRows, one_mul]

end Words

theorem commutant_trivial (hF : J4Facts) {t : J}
    (h0 : Mx t * rowsMatrix mat0 = rowsMatrix mat0 * Mx t)
    (h1 : Mx t * rowsMatrix mat1 = rowsMatrix mat1 * Mx t) : t = 1 := by
  have hM := hF.mat
  obtain ⟨b0, b1, b2, b3, d0, d1, hT⟩ := commutant_form (T := Mx t) h0 h1
  rcases comm_excl b0 b1 b2 b3 d0 d1 with h | ⟨hwf, hne⟩
  · apply Mx_injective
    rw [hT, eqRows_iff.1 h, rowsMatrix_idRows, map_one]
  · exfalso
    obtain ⟨W, hW⟩ : ∃ W, W = witWords.getD (combIdx b0 b1 b2 b3 d0 d1) [] := ⟨_, rfl⟩
    rw [← hW] at hwf hne
    have hmx : Mx (jwordJ W * t) =
        rowsMatrix (mulRows (jword W) (tcomb b0 b1 b2 b3 d0 d1)) := by
      rw [map_mul, Mx_jword hM, hT, rowsMatrix_mulRows]
    have hpow : (jwordJ W * t) ^ 86775571046077562880 = 1 := by
      rw [← card_J hF]
      exact pow_card_eq_one'
    have h2 := congrArg Mx hpow
    rw [map_pow, hmx, ← rowsMatrix_powBin _ (by norm_num), map_one, ← rowsMatrix_idRows] at h2
    obtain ⟨hs, hw⟩ := wfRows_spec hwf
    exact rowsMatrix_ne_of_eqRows_false hs idRows_size hw idRows_wf hne h2

theorem yJ_not_mem_Hj (hF : J4Facts) : yJ ∉ Hj := by
  have hM := hF.mat
  intro hy
  have hconj := yJ_conj hM
  have hysq := yJ_sq hM
  have hyinv : yJ⁻¹ = yJ := inv_eq_of_mul_eq_one_right hysq
  have h1 : yJ * eta uJ 11 cA * yJ⁻¹ ∈ Eg uJ 11 :=
    Hj_normalizes_Eg hM yJ hy _ (eta_mem_Eg 11 le_rfl cA)
  rw [hyinv, hconj] at h1
  have hw : wordProd xJ wObs ∈ Eg uJ 11 := by
    have h2 := (Eg uJ 11).mul_mem ((Eg uJ 11).inv_mem (eta_mem_Eg 11 le_rfl cB)) h1
    rwa [inv_mul_cancel_left] at h2
  obtain ⟨c, hc, hcw⟩ := (mem_Eg_iff (elem_uJ hM)).1 hw
  have hA := Acts_wordProd hM wObs obs_letters
  have hany := comm_y_out
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hany
  obtain ⟨c', hc', hne⟩ := hany
  have e1 := hA.2 c' (by simpa using hc')
  rw [hcw] at e1
  have e2 : eta uJ 11 c * eta uJ 11 c' * (eta uJ 11 c)⁻¹ = eta uJ 11 c' := by
    rw [eta_inv_self hM, eta_comm (elem_uJ hM) c c', mul_assoc, eta_sq (elem_uJ hM), mul_one]
  rw [e2] at e1
  exact hne (eta_inj hM c' (by simpa using hc') _ (actT_lt hA.1 c') e1).symm

def fixedSub (α : MulAut J) : Subgroup J where
  carrier := {x | α x = x}
  mul_mem' := fun {x y} (hx : α x = x) (hy : α y = y) => by
    show α (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := by
    show α 1 = 1
    exact map_one α
  inv_mem' := fun {x} (hx : α x = x) => by
    show α x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_fixedSub {α : MulAut J} {x : J} : x ∈ fixedSub α ↔ α x = x := Iff.rfl

theorem fix_comm (α : MulAut J) (hα : ∀ h ∈ Hj, α h = h) (hysq : yJ * yJ = 1) {m : J}
    (hm : m ∈ Hj) (hym : yJ * m * yJ ∈ Hj) : (yJ * α yJ) * m = m * (yJ * α yJ) := by
  have hyi : yJ⁻¹ = yJ := inv_eq_of_mul_eq_one_right hysq
  have hzz : α yJ * α yJ = 1 := by rw [← map_mul, hysq, map_one]
  have hzi : (α yJ)⁻¹ = α yJ := inv_eq_of_mul_eq_one_right hzz
  have h1 := hα _ hym
  rw [map_mul, map_mul, hα m hm] at h1
  have hz' : α yJ * m * (α yJ)⁻¹ = yJ * m * yJ⁻¹ := by
    rw [hzi, hyi]
    exact h1
  calc yJ * α yJ * m = yJ * (α yJ * m * (α yJ)⁻¹) * α yJ := by group
    _ = yJ * (yJ * m * yJ⁻¹) * α yJ := by rw [hz']
    _ = (yJ * yJ) * m * yJ⁻¹ * α yJ := by group
    _ = m * (yJ * α yJ) := by rw [hysq, hyi, one_mul, mul_assoc]

theorem eq_id_of_fix_Hj (hF : J4Facts) (α : MulAut J) (hα : ∀ h ∈ Hj, α h = h) (x : J) :
    α x = x := by
  have hM := hF.mat
  have hysq := yJ_sq hM
  have hyi : yJ⁻¹ = yJ := inv_eq_of_mul_eq_one_right hysq
  have hconj0 : yJ * wordProd xJ mWord0 * yJ = eta uJ 11 mConjC0 * wordProd xJ mConjW0 := by
    apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 comm_conj.1)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows] at this
    rw [map_mul, map_mul, map_mul, Mx_yJ hM, Mx_wordProd hM, Mx_etaR hM, Mx_wordProd hM]
    exact this
  have hconj1 : yJ * wordProd xJ mWord1 * yJ = eta uJ 11 mConjC1 * wordProd xJ mConjW1 := by
    apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 comm_conj.2)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows] at this
    rw [map_mul, map_mul, map_mul, Mx_yJ hM, Mx_wordProd hM, Mx_etaR hM, Mx_wordProd hM]
    exact this
  obtain ⟨hl0, hl1, hl2, hl3, hc0, hc1⟩ := comm_conj_data
  have hm0 : wordProd xJ mWord0 ∈ Hj := wordProd_mem_Hj hl0
  have hm1 : wordProd xJ mWord1 ∈ Hj := wordProd_mem_Hj hl1
  have hym0 : yJ * wordProd xJ mWord0 * yJ ∈ Hj := by
    rw [hconj0]
    exact Hj.mul_mem (Eg_le_Hj (eta_mem_Eg 11 le_rfl _)) (wordProd_mem_Hj hl2)
  have hym1 : yJ * wordProd xJ mWord1 * yJ ∈ Hj := by
    rw [hconj1]
    exact Hj.mul_mem (Eg_le_Hj (eta_mem_Eg 11 le_rfl _)) (wordProd_mem_Hj hl3)
  have hc0' := fix_comm α hα hysq hm0 hym0
  have hc1' := fix_comm α hα hysq hm1 hym1
  have h0 : Mx (yJ * α yJ) * rowsMatrix mat0 = rowsMatrix mat0 * Mx (yJ * α yJ) := by
    have e : Mx (wordProd xJ mWord0) = rowsMatrix mat0 := Mx_wordProd hM mWord0
    rw [← e, ← map_mul, ← map_mul, hc0']
  have h1 : Mx (yJ * α yJ) * rowsMatrix mat1 = rowsMatrix mat1 * Mx (yJ * α yJ) := by
    have e : Mx (wordProd xJ mWord1) = rowsMatrix mat1 := Mx_wordProd hM mWord1
    rw [← e, ← map_mul, ← map_mul, hc1']
  have hy1 : yJ * α yJ = 1 := commutant_trivial hF h0 h1
  have hyfix : α yJ = yJ := by
    calc α yJ = yJ⁻¹ * (yJ * α yJ) := (inv_mul_cancel_left yJ (α yJ)).symm
      _ = yJ⁻¹ := by rw [hy1, mul_one]
      _ = yJ := hyi
  have hlt : Hj < Hj ⊔ Subgroup.zpowers yJ := by
    refine lt_of_le_of_ne le_sup_left fun h => yJ_not_mem_Hj hF ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers yJ)
  have htop : Hj ⊔ Subgroup.zpowers yJ = ⊤ := (isCoatom_Hj hF).2 _ hlt
  have hle : Hj ⊔ Subgroup.zpowers yJ ≤ fixedSub α :=
    sup_le (fun h hh => hα h hh) (Subgroup.zpowers_le.2 hyfix)
  rw [htop] at hle
  exact hle (Subgroup.mem_top x)

end CFSG.Sporadic.J4.QT
