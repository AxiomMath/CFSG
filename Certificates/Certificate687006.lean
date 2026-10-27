module

public import CFSG.Sporadic.Th.Recog.PlacementInputs
import Certificates.Kernel.Th.Fam.C687006
import Certificates.Kernel.Th.JLet.Glue
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Spec.Big

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam.C6

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.KC.Th.Spec CFSG.KD.ThS CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.Place

def Rep (X : Array V4) (P : ℕ) : Prop := WfRows X ∧ InLayout P ∧ pkMat P = rowsMatrix X

theorem rep_one : Rep idRows ONE :=
  ⟨wfRows_idRows, inLayout_one k0, (pkMat_one k0).trans rowsMatrix_idRows.symm⟩

theorem rep_mul {X Y : Array V4} {P Q : ℕ} (h1 : Rep X P) (h2 : Rep Y Q) :
    Rep (mulRows X Y) (mP P Q) := by
  refine ⟨wfRows_mulRows h1.1 h2.1, inLayout_mulB k0 _ _, ?_⟩
  unfold mP
  rw [pkMat_mulB k0, h1.2.2, h2.2.2, rowsMatrix_mulRows]

theorem rep_eq_iff {X Y : Array V4} {P Q : ℕ} (h1 : Rep X P) (h2 : Rep Y Q) : X = Y ↔ P = Q := by
  constructor
  · rintro rfl
    exact pkMat_inj h1.2.1 h2.2.1 (h1.2.2.trans h2.2.2.symm)
  · rintro rfl
    exact rowsMatrix_inj h1.1 h2.1 (h1.2.2.symm.trans h2.2.2)

theorem eqRows_rep {X Y : Array V4} {P Q : ℕ} (h1 : Rep X P) (h2 : Rep Y Q) :
    eqRows X Y = Nat.beq P Q := by
  apply Bool.eq_iff_iff.2
  rw [eqRows_iff, rep_eq_iff h1 h2]
  exact ⟨fun h => h ▸ Nat.beq_refl _, Nat.eq_of_beq_eq_true⟩

theorem rep_canon {X : Array V4} {P : ℕ} (h : Rep X P) : Rep (Place.canon X) P := by
  refine ⟨wfRows_transposeRows _, h.2.1, ?_⟩
  unfold Place.canon
  rw [rowsMatrix_transposeRows, rowsMatrix_transposeRows, Matrix.transpose_transpose]
  exact h.2.2

theorem notInB_iff (x : ℕ) : ∀ l : List ℕ, notInB x l = true ↔ x ∉ l
  | [] => by simp [notInB]
  | y :: l => by
    change Bool.rec (notInB x l) false (Nat.beq x y) = true ↔ _
    cases h : Nat.beq x y
    · have hne := Nat.ne_of_beq_eq_false h
      simp only [List.mem_cons, not_or]
      rw [notInB_iff x l]
      exact ⟨fun h' => ⟨hne, h'⟩, fun h' => h'.2⟩
    · have heq := Nat.eq_of_beq_eq_true h
      simp [heq]

theorem nodupB_iff : ∀ l : List ℕ, nodupB l = true ↔ l.Nodup
  | [] => by simp [nodupB]
  | x :: t => by
    change Bool.rec false (nodupB t) (notInB x t) = true ↔ _
    rw [List.nodup_cons]
    cases h : notInB x t
    · have h' : ¬ x ∉ t := fun hx => by rw [(notInB_iff x t).2 hx] at h; exact Bool.noConfusion h
      simp [h']
    · rw [nodupB_iff t]
      exact ⟨fun h2 => ⟨(notInB_iff x t).1 h, h2⟩, fun h2 => h2.2⟩

theorem nodup_rep {n : ℕ} {X : Fin n → Array V4} {P : Fin n → ℕ} (h : ∀ r, Rep (X r) (P r)) :
    decide (List.ofFn fun r => Place.canon (X r)).Nodup = nodupB (List.ofFn fun r => P r) := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, nodupB_iff, List.nodup_ofFn, List.nodup_ofFn]
  constructor
  · intro hi r s e
    exact hi ((rep_eq_iff (rep_canon (h r)) (rep_canon (h s))).2 e)
  · intro hi r s e
    exact hi ((rep_eq_iff (rep_canon (h r)) (rep_canon (h s))).1 e)

theorem forceB_eq (y : ℕ) (k : ℕ → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem ord8_rep {X : Array V4} {P : ℕ} (h : Rep X P) : ord8 X = ord8P P := by
  simp only [ord8, ord8P, forceB_eq]
  have h4 := rep_mul (rep_mul h h) (rep_mul h h)
  rw [eqRows_rep (rep_mul h4 h4) rep_one, eqRows_rep (rep_canon h4) rep_one]

theorem cubeNe_rep {X : Array V4} {P : ℕ} (h : Rep X P) : cubeNe X = cubeNeP P := by
  unfold cubeNe cubeNeP
  rw [eqRows_rep (rep_canon (rep_mul (rep_mul h h) h)) rep_one]

theorem codeN_lett {n : ℕ} (w : List (Fin n × Bool)) :
    (codeN w).map lettOfCode = w.map fun l => (l.1.val, l.2) := by
  unfold codeN
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨g, b⟩ -
  cases b
  · refine Prod.ext ?_ ?_
    · change (2 * g.val + 1) / 2 = g.val
      omega
    · change decide ((2 * g.val + 1) % 2 = 0) = false
      exact decide_eq_false (by omega)
  · refine Prod.ext ?_ ?_
    · change (2 * g.val + 0) / 2 = g.val
      omega
    · change decide ((2 * g.val + 0) % 2 = 0) = true
      exact decide_eq_true (by omega)

theorem codeN_lt {n : ℕ} (hn : n ≤ 8) (w : List (Fin n × Bool)) : ∀ x ∈ codeN w, x / 2 < 8 := by
  intro x hx
  unfold codeN at hx
  obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hx
  have hg := g.isLt
  cases b
  · change (2 * g.val + 1) / 2 < 8
    omega
  · change (2 * g.val + 0) / 2 < 8
    omega

theorem wRowsArr_rep {n : ℕ} (hn : n ≤ 8) {rs rsi : Array (Array V4)} {R : ℕ → ℕ}
    (h : ∀ g : Fin n, Rep ((rs[g.val]?).getD idRows) (R (g.val + 1)) ∧
      Rep ((rsi[g.val]?).getD idRows) (R (g.val + 9)))
    (w : List (Fin n × Bool)) : Rep (wRowsArr rs rsi w) (wP R w) := by
  unfold wRowsArr wP
  refine ⟨wfRows_prodRows ?_, JLet.lay_wordV _ _ _ (inLayout_one k0), ?_⟩
  · intro X hX
    obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hX
    cases b
    · exact (h g).2.1
    · exact (h g).1.1
  · rw [JLet.pk_wordV R _ (codeN_lt hn w), codeN_lett, List.map_map,
      CFSG.KC.Th.Spec.rowsMatrix_prodRows, List.map_map]
    congr 1
    apply List.map_congr_left
    rintro ⟨g, b⟩ -
    cases b
    · exact (h g).2.2.2
    · exact (h g).1.2.2

theorem pinsB_mem {F G : ℕ → ℕ} : ∀ {rs : List ℕ}, pinsB F G rs = true → ∀ r ∈ rs, F r = G r
  | [], _, r, hr => by simp at hr
  | s :: rs, h, r, hr => by
    change Bool.rec false (pinsB F G rs) (Nat.beq (F s) (G s)) = true at h
    cases hs : Nat.beq (F s) (G s)
    · rw [hs] at h
      exact Bool.noConfusion h
    · rw [hs] at h
      rcases List.mem_cons.1 hr with rfl | hr
      · exact Nat.eq_of_beq_eq_true hs
      · exact pinsB_mem h r hr

theorem regOf_lo (f fi : ℕ → ℕ) {j : ℕ} (hj : j < 8) : regOf f fi (j + 1) = f j := by
  unfold regOf
  rw [show Nat.blt (j + 1) 9 = true by rw [Nat.blt_eq]; omega]
  change f (j + 1 - 1) = f j
  rw [Nat.add_sub_cancel]

theorem regOf_hi (f fi : ℕ → ℕ) (j : ℕ) : regOf f fi (j + 9) = fi j := by
  unfold regOf
  rw [show Nat.blt (j + 9) 9 = false from Bool.eq_false_iff.2 fun h => by
    rw [Nat.blt_eq] at h
    omega]
  change fi (j + 9 - 9) = fi j
  rw [Nat.add_sub_cancel]

theorem mem4 {a b c d r : ℕ} (h : r = a ∨ r = b ∨ r = c ∨ r = d) : r ∈ [a, b, c, d] := by
  simpa using h

@[reducible] def B₀ : Base := Base.make (rowsHswArr ()) (rowsHswInvArr ())

theorem RH_pin (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 16) : CFSG.KD.Th687006.RH r = JLet.RH r := by
  rcases Nat.lt_or_ge r 5 with h | h
  · exact pinsB_mem k687006_pinH0 r (mem4 (by omega))
  rcases Nat.lt_or_ge r 9 with h' | h'
  · exact pinsB_mem k687006_pinH1 r (mem4 (by omega))
  rcases Nat.lt_or_ge r 13 with h'' | h''
  · exact pinsB_mem k687006_pinH2 r (mem4 (by omega))
  · exact pinsB_mem k687006_pinH3 r (mem4 (by omega))

theorem repH (g : Fin 8) :
    Rep ((B₀.H[g.val]?).getD idRows) (CFSG.KD.Th687006.RH (g.val + 1)) ∧
      Rep ((B₀.HI[g.val]?).getD idRows) (CFSG.KD.Th687006.RH (g.val + 9)) := by
  have hg := g.isLt
  have e1 := JLet.RH_reg (g, true)
  have e2 := JLet.RH_reg (g, false)
  simp only [regMat, ↓reduceIte, Bool.false_eq_true] at e1 e2
  change Rep ((rowsHswArr ())[g.val]?.getD idRows) _ ∧ Rep ((rowsHswInvArr ())[g.val]?.getD idRows) _
  rw [rowsHswArr_get, rowsHswInvArr_get, RH_pin _ (by omega) (by omega),
    RH_pin _ (by omega) (by omega)]
  exact ⟨⟨JLet.wf_hsw g, JLet.lay_hV _, e1⟩, ⟨JLet.wf_hswInv g, JLet.lay_hV _, e2⟩⟩

theorem ofFn_getD {n : ℕ} (f : Fin n → Array V4) (g : Fin n) :
    ((Array.ofFn f)[g.val]?).getD idRows = f g := by
  simp [Array.getElem?_ofFn, g.isLt]

theorem repL (g : Fin 6) :
    Rep ((B₀.L[g.val]?).getD idRows) (CFSG.KD.Th687006.RL (g.val + 1)) ∧
      Rep ((B₀.LI[g.val]?).getD idRows) (CFSG.KD.Th687006.RL (g.val + 9)) := by
  have hg := g.isLt
  have p1 : CFSG.KD.Th687006.RL (g.val + 1) = lvL (g.val + 1) := by
    rcases Nat.lt_or_ge g.val 3 with h | h
    · exact pinsB_mem k687006_pinL0 _ (by simp; omega)
    · exact pinsB_mem k687006_pinL1 _ (by simp; omega)
  have p2 : CFSG.KD.Th687006.RL (g.val + 9) = lvL (g.val + 9) := by
    rcases Nat.lt_or_ge g.val 3 with h | h
    · exact pinsB_mem k687006_pinL0 _ (by simp; omega)
    · exact pinsB_mem k687006_pinL1 _ (by simp; omega)
  unfold lvL at p1 p2
  rw [regOf_lo _ _ (by omega)] at p1
  rw [regOf_hi] at p2
  change Rep ((Array.ofFn (n := 6) fun i => wRowsArr (rowsHswArr ()) (rowsHswInvArr ())
      (lWord i))[g.val]?.getD idRows) _ ∧
    Rep ((Array.ofFn (n := 6) fun i => wRowsArr (rowsHswArr ()) (rowsHswInvArr ())
      (FreeGroup.invRev (lWord i)))[g.val]?.getD idRows) _
  rw [ofFn_getD, ofFn_getD, p1, p2, JLet.lWordN_val]
  exact ⟨wRowsArr_rep (by norm_num) repH _, wRowsArr_rep (by norm_num) repH _⟩

theorem hWordN_val (j : Fin 5) : hWordN j.val = hWord j := by
  unfold hWordN
  rw [Fin.ofNat_val_eq_self]

theorem repC (g : Fin 5) :
    Rep ((B₀.h[g.val]?).getD idRows) (CFSG.KD.Th687006.RC (g.val + 1)) ∧
      Rep ((B₀.hI[g.val]?).getD idRows) (CFSG.KD.Th687006.RC (g.val + 9)) := by
  have hg := g.isLt
  have p1 : CFSG.KD.Th687006.RC (g.val + 1) = lvC (g.val + 1) :=
    pinsB_mem k687006_pinC _ (by simp; omega)
  have p2 : CFSG.KD.Th687006.RC (g.val + 9) = lvC (g.val + 9) :=
    pinsB_mem k687006_pinC _ (by simp; omega)
  unfold lvC at p1 p2
  rw [regOf_lo _ _ (by omega)] at p1
  rw [regOf_hi] at p2
  change Rep ((Array.ofFn (n := 5) fun j => wRowsArr B₀.L B₀.LI (hWord j))[g.val]?.getD idRows) _ ∧
    Rep ((Array.ofFn (n := 5) fun j =>
      wRowsArr B₀.L B₀.LI (FreeGroup.invRev (hWord j)))[g.val]?.getD idRows) _
  rw [ofFn_getD, ofFn_getD, p1, p2, hWordN_val]
  exact ⟨wRowsArr_rep (by norm_num) repL _, wRowsArr_rep (by norm_num) repL _⟩

theorem repA : Rep B₀.A aP := (repH 0).1

theorem repD : Rep B₀.D dP := (repH 3).1

theorem repDI : Rep B₀.DI dIP := (repH 3).2

theorem repV (i : Fin 2) : Rep (vRows B₀ i) (vP i) := by
  change Rep ((Array.ofFn (n := 2) fun i => wRowsArr B₀.H B₀.HI (vWord i))[i.val]?.getD idRows) _
  rw [ofFn_getD]
  exact wRowsArr_rep (by norm_num) repH _

theorem repVI (i : Fin 2) : Rep (get1 B₀.VI i) (vIP i) := by
  change Rep ((Array.ofFn (n := 2) fun i =>
    wRowsArr B₀.H B₀.HI (FreeGroup.invRev (vWord i)))[i.val]?.getD idRows) _
  rw [ofFn_getD]
  exact wRowsArr_rep (by norm_num) repH _

theorem repW (i : Fin 2) : Rep (get1 B₀.W i) (wpP i) := by
  change Rep ((Array.ofFn (n := 2) fun i => wRowsArr B₀.L B₀.LI (wpWord i))[i.val]?.getD idRows) _
  rw [ofFn_getD]
  exact wRowsArr_rep (by norm_num) repL _

theorem repWI (i : Fin 2) : Rep (get1 B₀.WI i) (wpIP i) := by
  change Rep ((Array.ofFn (n := 2) fun i =>
    wRowsArr B₀.L B₀.LI (FreeGroup.invRev (wpWord i)))[i.val]?.getD idRows) _
  rw [ofFn_getD]
  exact wRowsArr_rep (by norm_num) repL _

theorem get2_ofFn (f : Fin 2 → Fin 8 → Array V4) (i : Fin 2) (m : Fin 8) :
    get2 (Array.ofFn fun i => Array.ofFn fun m => f i m) i m = f i m := by
  simp [get2, Array.getElem?_ofFn, i.isLt, m.isLt]

theorem repR (i : Fin 2) (m : Fin 8) : Rep (repRows B₀ i m) (repP i m) := by
  change Rep (get2 (Array.ofFn fun i => Array.ofFn fun m => wRowsArr B₀.h B₀.hI (repWord i m)) i m) _
  rw [get2_ofFn]
  exact wRowsArr_rep (by norm_num) repC _

theorem repZ (i : Fin 2) (m : Fin 8) : Rep (zRows B₀ i m) (zP i m) := by
  change Rep (get2 (Array.ofFn fun i => Array.ofFn fun m => mulRows (get1 B₀.W i) (repRows B₀ i m))
    i m) _
  rw [get2_ofFn]
  exact rep_mul (repW i) (repR i m)

theorem repZI (i : Fin 2) (m : Fin 8) : Rep (zInvRows B₀ i m) (zIP i m) :=
  rep_mul (wRowsArr_rep (by norm_num) repC _) (repWI i)

theorem repOrb (i : Fin 2) (r : Fin 18) : Rep (orbRows B₀ i r) (orbP i r) :=
  rep_mul (rep_mul (wRowsArr_rep (by norm_num) repC _) (repV i)) (wRowsArr_rep (by norm_num) repC _)

theorem repFour (i : Fin 2) (u : Fin 4) : Rep (fourRows B₀ i u) (fourP i u) := by
  fin_cases u
  · exact rep_one
  · exact repA
  · exact repV i
  · exact rep_mul repA (repV i)

theorem repCent (i : Fin 2) (q : Fin 32) : Rep (centRows B₀ i q) (cntP i q) :=
  rep_mul (repR _ _) (repFour _ _)

theorem repG (x : Fin 2) (g : Fin 4) :
    Rep (((gensRows B₀ x)[g.val]?).getD idRows) (regOf (gensP x) (gensIP x) (g.val + 1)) ∧
      Rep (((gensInvRows B₀ x)[g.val]?).getD idRows)
        (regOf (gensP x) (gensIP x) (g.val + 9)) := by
  rw [regOf_lo _ _ (by omega), regOf_hi]
  fin_cases g
  · exact ⟨repV 0, repVI 0⟩
  · exact ⟨repV 1, repVI 1⟩
  · exact ⟨repZ 0 _, repZI 0 _⟩
  · exact ⟨repZ 1 _, repZI 1 _⟩

theorem checkA_eq : checkA B₀ = chkA := by
  unfold checkA chkA
  rw [eqRows_rep (wRowsArr_rep (by norm_num) repC aHWord) repA,
    eqRows_rep (rep_mul repA repA) rep_one]

theorem checkV_eq : checkV B₀ = chkV := by
  have e1 : ∀ i, eqRows (mulRows (vRows B₀ i) (vRows B₀ i)) idRows =
      Nat.beq (mP (vP i) (vP i)) ONE := fun i => eqRows_rep (rep_mul (repV i) (repV i)) rep_one
  have e2 : ∀ i, eqRows (mulRows B₀.A (vRows B₀ i)) (mulRows (vRows B₀ i) B₀.A) =
      Nat.beq (mP aP (vP i)) (mP (vP i) aP) := fun i =>
    eqRows_rep (rep_mul repA (repV i)) (rep_mul (repV i) repA)
  have v01 := rep_mul (repV 0) (repV 1)
  unfold checkV chkV
  simp only [e1, e2, eqRows_rep (rep_mul v01 v01) repA]

theorem checkH_eq : checkH B₀ = chkH := by
  have e : ∀ j : Fin 5, eqRows (mulRows (get1 B₀.h j) B₀.A) (mulRows B₀.A (get1 B₀.h j)) =
      Nat.beq (mP (CFSG.KD.Th687006.RC (j.val + 1)) aP)
        (mP aP (CFSG.KD.Th687006.RC (j.val + 1))) := fun j =>
    eqRows_rep (rep_mul (repC j).1 repA) (rep_mul repA (repC j).1)
  unfold checkH chkH
  simp only [e]

theorem checkOrb_eq : checkOrb B₀ = chkOrb := by
  have e : ∀ i, decide (List.ofFn fun r => Place.canon (orbRows B₀ i r)).Nodup =
      nodupB (List.ofFn fun r => orbP i r) := fun i => nodup_rep (repOrb i)
  unfold checkOrb chkOrb
  simp only [e]

theorem checkRep_eq : checkRep B₀ = chkRep := by
  have e : ∀ i m, eqRows (mulRows (repRows B₀ i m) (vRows B₀ i))
      (mulRows (vRows B₀ i) (repRows B₀ i m)) =
      Nat.beq (mP (repP i m) (vP i)) (mP (vP i) (repP i m)) := fun i m =>
    eqRows_rep (rep_mul (repR i m) (repV i)) (rep_mul (repV i) (repR i m))
  unfold checkRep chkRep
  simp only [e]

theorem checkCent_eq : checkCent B₀ = chkCent := by
  have e : ∀ i, decide (List.ofFn fun q => Place.canon (centRows B₀ i q)).Nodup =
      nodupB (List.ofFn fun q => cntP i q) := fun i => nodup_rep (repCent i)
  unfold checkCent chkCent
  simp only [e]

theorem checkWp_eq : checkWp B₀ = chkWp := by
  have e1 : ∀ i : Fin 2, eqRows (mulRows (mulRows (get1 B₀.W i) B₀.A) (get1 B₀.WI i)) (vRows B₀ i) =
      Nat.beq (mP (mP (wpP i) aP) (wpIP i)) (vP i) := fun i =>
    eqRows_rep (rep_mul (rep_mul (repW i) repA) (repWI i)) (repV i)
  have e2 : ∀ i : Fin 2, eqRows (mulRows (mulRows (get1 B₀.W i) (vRows B₀ i)) (get1 B₀.WI i))
      (mulRows B₀.A (vRows B₀ i)) =
      Nat.beq (mP (mP (wpP i) (vP i)) (wpIP i)) (mP aP (vP i)) := fun i =>
    eqRows_rep (rep_mul (rep_mul (repW i) (repV i)) (repWI i)) (rep_mul repA (repV i))
  unfold checkWp chkWp
  simp only [e1, e2]

theorem checkCoset_eq : checkCoset B₀ = chkCoset := by
  have e1 : ∀ (i : Fin 2) (m : Fin 8) (u : Fin 4), cubeNe (mulRows (zRows B₀ i m) (fourRows B₀ i u)) =
      cubeNeP (mP (zP i m) (fourP i u)) := fun i m u =>
    cubeNe_rep (rep_mul (repZ i m) (repFour i u))
  have e2 : ∀ (i : Fin 2) (m : Fin 8), ord8 (mulRows (vRows B₀ (1 - i)) (zRows B₀ i m)) =
      ord8P (mP (vP (1 - i)) (zP i m)) := fun i m =>
    ord8_rep (rep_mul (repV _) (repZ i m))
  unfold checkCoset chkCoset
  simp only [e1, e2]

theorem checkPair_eq : checkPair B₀ = chkPair := by
  have e : ∀ m₀ m₁ : Fin 8, ord8 (mulRows (zRows B₀ 0 m₀)
      (mulRows (mulRows B₀.D (mulRows (vRows B₀ 0) (zRows B₀ 1 m₁))) B₀.DI)) =
      ord8P (mP (zP 0 m₀) (mP (mP dP (mP (vP 0) (zP 1 m₁))) dIP)) := fun m₀ m₁ =>
    ord8_rep (rep_mul (repZ 0 m₀) (rep_mul (rep_mul repD (rep_mul (repV 0) (repZ 1 m₁))) repDI))
  unfold checkPair chkPair
  simp only [e]

theorem checkXw_eq : checkXw B₀ = chkXw := by
  have e : ∀ x k j, eqRows (wRowsArr B₀.H B₀.HI (xw (k, x) j))
      (wRowsArr (gensRows B₀ x) (gensInvRows B₀ x) (xwExpr k x j)) =
      Nat.beq (wP CFSG.KD.Th687006.RH (xw (k, x) j))
        (wP (regOf (gensP x) (gensIP x)) (xwExpr k x j)) := fun x k j =>
    eqRows_rep (wRowsArr_rep (by norm_num) repH _) (wRowsArr_rep (by norm_num) (repG x) _)
  unfold checkXw chkXw
  simp only [e]

end CertificateChecks.KernelTh.Fam.C6

namespace CertificateChecks.KernelTh.Fam

open C6 CFSG.Sporadic.Th.Recog.Place

theorem place_check_eq : CFSG.Sporadic.Th.Recog.Place.check () = check6K := by
  simp only [CFSG.Sporadic.Th.Recog.Place.check]
  rw [checkA_eq, checkV_eq, checkH_eq, checkOrb_eq, checkRep_eq, checkCent_eq, checkWp_eq,
    checkCoset_eq, checkPair_eq, checkXw_eq, check6K]

end CertificateChecks.KernelTh.Fam

namespace Certificates

open CertificateChecks

public theorem certificate687006 : CFSG.Sporadic.Th.Recog.Place.check () = true :=
  KernelTh.Fam.place_check_eq.trans KernelTh.Fam.ok687006

end Certificates
