
module

public import CFSG.Sporadic.Co1.Module.TwoBKernel

public section

namespace CFSG.Sporadic.Co1.Module.InvFam

open CFSG.Blueprint CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.TwoBK

theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getL_eq x L i

theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

theorem getL_mem {L : List Nat} {l : Nat} (hl : l < lenL L) : getL 0 L l ∈ L := by
  rw [lenL_eq] at hl
  rw [getL_eq, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.getElem_mem hl

theorem getL_idF {L : List Nat} {i : Nat} (hi : i < L.length) : getL (idF 24) L i = getL 0 L i := by
  rw [getL_eq, getL_eq, List.getElem?_eq_getElem hi, Option.getD_some, Option.getD_some]

theorem allL_iff {L : List Nat} {f : Nat → Bool} : allL L f = true ↔ ∀ a ∈ L, f a = true := by
  induction L with
  | nil => exact ⟨fun _ a ha => absurd ha List.not_mem_nil, fun _ => rfl⟩
  | cons a L ih =>
    change andB (f a) (allL L f) = true ↔ _
    rw [andB_true_iff, ih, List.forall_mem_cons]

theorem bnd_spec {n : Nat} {L : List Nat} (h : bndK n L = true) : ∀ i ∈ L, i < n :=
  fun i hi => blt_iff.1 (allL_iff.1 h i hi)

theorem fixAll_spec {RT I vs : List Nat} (h : fixAllK RT I vs = true) :
    ∀ i ∈ I, ∀ v ∈ vs, vmF 24 (getL 0 RT i) v = v :=
  fun i hi v hv => beq_iff.1 (allL_iff.1 (allL_iff.1 h i hi) v hv)

theorem anyN_of {f : Nat → Bool} : ∀ {n i : Nat}, i < n → f i = true → anyN n f = true
  | 0, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi, hf => by
    change orB (f n) (anyN n f) = true
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [anyN_of h hf]
      cases f n <;> rfl
    · rw [← h, hf]
      rfl

theorem not_memK {rec : Nat → Nat} {n wv m : Nat} (h : notB (memK rec n wv m) = true) :
    ∀ i < n, valF wv (rec i) ≠ m := by
  intro i hi e
  have hm : memK rec n wv m = true := anyN_of hi (by rw [e]; exact Nat.beq_refl m)
  rw [hm] at h
  exact Bool.false_ne_true h

theorem notB_true {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def lineGo (R : List Nat) (fac : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => CFSG.KC.Loop.strictN (Prod.rec (motive := fun _ => Nat)
      (fun i e => mulF 24 acc (powK 24 (getL (idF 24) R i) e)) p) ih) fac

theorem lineK_eq (R : List Nat) (fac : List (Nat × Nat)) : lineK 24 R fac = lineGo R fac (idF 24) :=
  rfl

theorem pm_lineGo (R : List Nat) : ∀ fac : List (Nat × Nat),
    (∀ p ∈ fac, ∃ x, PM x (getL (idF 24) R p.1)) →
    ∀ (acc : Nat) (x : NativeSporadic.Co1), PM x acc → ∃ z, PM z (lineGo R fac acc)
  | [], _, _, x, h => ⟨x, h⟩
  | (i, e) :: fac, hf, acc, x, h => by
    obtain ⟨y, hy⟩ := hf (i, e) List.mem_cons_self
    have e1 : lineGo R ((i, e) :: fac) acc =
        lineGo R fac (mulF 24 acc (powK 24 (getL (idF 24) R i) e)) :=
      strictN_eq (mulF 24 acc (powK 24 (getL (idF 24) R i) e)) (lineGo R fac)
    rw [e1]
    exact pm_lineGo R fac (fun p hp => hf p (List.mem_cons_of_mem _ hp)) _ _ (pm_mul h (pm_pow hy e))

theorem facBelow_spec {t : Nat} : ∀ {fac : List (Nat × Nat)}, facBelow fac t = true →
    ∀ p ∈ fac, p.1 < t
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: fac, h, p, hp => by
    obtain ⟨h1, h2⟩ := andB_true_iff.1 h
    rcases List.mem_cons.1 hp with e | e
    · subst e
      exact blt_iff.1 h1
    · exact facBelow_spec h2 p e

theorem progK_unfold {R : List Nat} {fac : List (Nat × Nat)} {P : List (List (Nat × Nat))} {t : Nat}
    (h : progK 24 R (fac :: P) t = true) :
    facBelow fac t = true ∧ getL 0 R t = lineK 24 R fac ∧ progK 24 R P (t + 1) = true := by
  have h' : andB (facBelow fac t) (andB (Nat.beq (getL (nat_lit 0) R t) (lineK 24 R fac))
      (progK 24 R P (Nat.succ t))) = true := by
    rw [← strictB_eq t (fun t => andB (facBelow fac t) (andB (Nat.beq (getL (nat_lit 0) R t)
      (lineK 24 R fac)) (progK 24 R P (Nat.succ t))))]
    exact h
  obtain ⟨h1, h2⟩ := andB_true_iff.1 h'
  obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
  exact ⟨h1, beq_iff.1 h2, h3⟩

theorem progK_len {R : List Nat} : ∀ (P : List (List (Nat × Nat))) (t : Nat),
    progK 24 R P t = true → t + P.length = R.length
  | [], t, h => by
    have e : lenL R = t := beq_iff.1 h
    rw [lenL_eq] at e
    simp [e]
  | fac :: P, t, h => by
    have := progK_len P (t + 1) (progK_unfold h).2.2
    simp only [List.length_cons]
    omega

theorem prog_elems {R : List Nat} : ∀ (P : List (List (Nat × Nat))) (t : Nat),
    progK 24 R P t = true → (∀ i < t, ∃ x, PM x (getL 0 R i)) →
    ∀ i < R.length, ∃ x, PM x (getL 0 R i)
  | [], t, h, hin => by
    have e := progK_len [] t h
    simp only [List.length_nil, Nat.add_zero] at e
    intro i hi
    exact hin i (by omega)
  | fac :: P, t, h, hin => by
    obtain ⟨h1, h2, h3⟩ := progK_unfold h
    have hlen := progK_len (fac :: P) t h
    simp only [List.length_cons] at hlen
    refine prog_elems P (t + 1) h3 (fun i hi => ?_)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hin i hi
    · rw [h2, lineK_eq]
      refine pm_lineGo R fac (fun p hp => ?_) (idF 24) 1 pm_one
      have hpt := facBelow_spec h1 p hp
      rw [getL_idF (by omega)]
      exact hin p.1 hpt

theorem reg_elems {W : InvFamW} (hW : InvFamOK W) :
    ∀ i < W.R.length, ∃ x : NativeSporadic.Co1, PM x (W.reg i) := by
  refine prog_elems W.P 2 hW.prog (fun i hi => ?_)
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · obtain ⟨g, hg⟩ := exists_co1_matA
    refine ⟨g, ?_⟩
    unfold PM
    have e : dat.rowsA = unpackR 24 (getL 0 W.R 0) := hW.rA
    rw [← e]
    exact hg
  · obtain ⟨g, hg⟩ := exists_co1_matB
    refine ⟨g, ?_⟩
    unfold PM
    have e : dat.rowsB = unpackR 24 (getL 0 W.R 1) := hW.rB
    rw [← e]
    exact hg

theorem co1Act_inv {x : NativeSporadic.Co1} {v : Vec24} (hx : co1Act x v = v) : co1Act x⁻¹ v = v := by
  conv_lhs => rw [← hx]
  rw [← co1Act_mul, inv_mul_cancel, co1Act_one]

theorem conj_act {x τ : NativeSporadic.Co1} {v w : Vec24} (hxv : co1Act x v = v)
    (hxw : co1Act x w = w) (hτ : co1Act τ v = w) : co1Act (x * τ * x⁻¹) v = w := by
  rw [co1Act_mul, co1Act_mul, co1Act_inv hxv, hτ, hxw]

theorem conj_conj {x y s : NativeSporadic.Co1} {c : Vec24} (hx : co1Act x c = c) (hy : co1Act y c = c) :
    ∃ z, co1Act z c = c ∧ x * (y * s * y⁻¹) * x⁻¹ = z * s * z⁻¹ :=
  ⟨x * y, by rw [co1Act_mul, hy, hx], by group⟩

theorem fibre_union (P : NativeSporadic.Co1 → Prop) {u w : Vec24} {n0 n1 m : ℕ}
    (f0 f1 g : ℕ → NativeSporadic.Co1)
    (h0 : ∀ i < n0, ∀ j < n0, f0 i = f0 j → i = j) (h0u : ∀ i < n0, co1Act (f0 i) u = u)
    (h0P : ∀ i < n0, P (f0 i))
    (h1 : ∀ i < n1, ∀ j < n1, f1 i = f1 j → i = j) (h1u : ∀ i < n1, co1Act (f1 i) u = w)
    (h1P : ∀ i < n1, P (f1 i)) (hgu : ∀ c < m, co1Act (g c) u = u)
    (hg : ∀ c < m, ∀ d < m, co1Act (g c) w = co1Act (g d) w → c = d)
    (hgne : 0 < n0 → ∀ c < m, co1Act (g c) w ≠ u)
    (hgP : ∀ c < m, ∀ t, P t → P (g c * t * (g c)⁻¹)) :
    ∃ f : ℕ → NativeSporadic.Co1, (∀ i < n0 + m * n1, ∀ j < n0 + m * n1, f i = f j → i = j) ∧
      ∀ i < n0 + m * n1, P (f i) := by
  classical
  let F : ℕ → NativeSporadic.Co1 := fun i => if i < n0 then f0 i else
    g ((i - n0) / n1) * f1 ((i - n0) % n1) * (g ((i - n0) / n1))⁻¹
  have hidx : ∀ i, n0 ≤ i → i < n0 + m * n1 → (i - n0) / n1 < m ∧ (i - n0) % n1 < n1 := by
    intro i hi1 hi2
    have hn1 : 0 < n1 := by
      rcases Nat.eq_zero_or_pos n1 with h | h
      · rw [h, Nat.mul_zero] at hi2
        omega
      · exact h
    refine ⟨?_, Nat.mod_lt _ hn1⟩
    rw [Nat.div_lt_iff_lt_mul hn1]
    omega
  have hF1 : ∀ i, ¬ i < n0 → F i = g ((i - n0) / n1) * f1 ((i - n0) % n1) * (g ((i - n0) / n1))⁻¹ :=
    fun i hi => by simp only [F, hi, ↓reduceIte]
  have hF0 : ∀ i, i < n0 → F i = f0 i := fun i hi => by simp only [F, hi, ↓reduceIte]
  have hFu : ∀ i, ¬ i < n0 → i < n0 + m * n1 → co1Act (F i) u = co1Act (g ((i - n0) / n1)) w := by
    intro i hi1 hi2
    obtain ⟨hc, hr⟩ := hidx i (not_lt.1 hi1) hi2
    rw [hF1 i hi1, co1Act_mul, co1Act_mul, co1Act_inv (hgu _ hc), h1u _ hr]
  have cross : ∀ i j, i < n0 → ¬ j < n0 → j < n0 + m * n1 → F i ≠ F j := by
    intro i j hi hj hj2 e
    have h2 : co1Act (F i) u = u := by rw [hF0 i hi]; exact h0u i hi
    rw [e, hFu j hj hj2] at h2
    exact hgne (by omega) _ (hidx j (not_lt.1 hj) hj2).1 h2
  refine ⟨F, fun i hi j hj e => ?_, fun i hi => ?_⟩
  · by_cases hi0 : i < n0 <;> by_cases hj0 : j < n0
    · rw [hF0 i hi0, hF0 j hj0] at e
      exact h0 i hi0 j hj0 e
    · exact absurd e (cross i j hi0 hj0 hj)
    · exact absurd e.symm (cross j i hj0 hi0 hi)
    · obtain ⟨hci, hri⟩ := hidx i (not_lt.1 hi0) hi
      obtain ⟨hcj, hrj⟩ := hidx j (not_lt.1 hj0) hj
      have hc := hg _ hci _ hcj (by rw [← hFu i hi0 hi, ← hFu j hj0 hj, e])
      rw [hF1 i hi0, hF1 j hj0, hc] at e
      have hr := h1 _ hri _ hrj (mul_left_cancel (mul_right_cancel e))
      have d1 := Nat.div_add_mod (i - n0) n1
      have d2 := Nat.div_add_mod (j - n0) n1
      rw [hc, hr] at d1
      omega
  · by_cases hi0 : i < n0
    · rw [hF0 i hi0]
      exact h0P i hi0
    · obtain ⟨hc, hr⟩ := hidx i (not_lt.1 hi0) hi
      rw [hF1 i hi0]
      exact hgP _ hc _ (h1P _ hr)

section Trees

variable {G β : Type*} [Group G]

theorem reach_op (C : Subgroup G) (op : G → β → β) (hop : ∀ g h b, op (g * h) b = op g (op h b))
    (hone : ∀ b, op 1 b = b) {act : ℕ → ℕ → ℕ} {ng root : ℕ} (enc : ℕ → β) (gen : ℕ → G)
    (hgen : ∀ l < ng, gen l ∈ C) (P : ℕ → Prop) (hP0 : P root)
    (hPs : ∀ l < ng, ∀ y, P y → P (act l y))
    (hact : ∀ l < ng, ∀ y, P y → enc (act l y) = op (gen l) (enc y)) {x : ℕ}
    (hx : CFSG.KC.Bfs.Reach act ng root x) : P x ∧ ∃ g ∈ C, enc x = op g (enc root) := by
  induction hx with
  | root => exact ⟨hP0, 1, C.one_mem, (hone _).symm⟩
  | step l hl _ ih =>
    obtain ⟨hPx, g, hg, hgx⟩ := ih
    refine ⟨hPs l hl _ hPx, gen l * g, C.mul_mem (hgen l hl) hg, ?_⟩
    rw [hact l hl _ hPx, hgx, hop]

theorem sort_family (C : Subgroup G) (op : G → β → β)
    (hop : ∀ g h b, op (g * h) b = op g (op h b)) (hone : ∀ b, op 1 b = b)
    {act : ℕ → ℕ → ℕ} {ng root wv n : ℕ} {T : STree} (hT : T.OK act ng root wv n)
    (enc : ℕ → β) (gen : ℕ → G) (hgen : ∀ l < ng, gen l ∈ C) (P : ℕ → Prop) (hP0 : P root)
    (hPs : ∀ l < ng, ∀ y, P y → P (act l y))
    (hact : ∀ l < ng, ∀ y, P y → enc (act l y) = op (gen l) (enc y))
    (hinj : ∀ x y, P x → P y → enc x = enc y → x = y) :
    ∃ t : ℕ → G, (∀ i < n, t i ∈ C ∧ P (valF wv (T.tab i)) ∧
      enc (valF wv (T.tab i)) = op (t i) (enc root)) ∧
      ∀ i < n, ∀ j < n, op (t i) (enc root) = op (t j) (enc root) → i = j := by
  obtain ⟨hreach, -, hlt, -⟩ := tree_sound_chunks hT.1 hT.2
  have key : ∀ i < n, P (valF wv (T.tab i)) ∧
      ∃ g ∈ C, enc (valF wv (T.tab i)) = op g (enc root) :=
    fun i hi => reach_op C op hop hone enc gen hgen P hP0 hPs hact (hreach i hi)
  choose! t ht using fun i hi => (key i hi).2
  refine ⟨t, fun i hi => ⟨(ht i hi).1, (key i hi).1, (ht i hi).2⟩, fun i hi j hj e => ?_⟩
  have hv := hinj _ _ (key i hi).1 (key j hj).1 (by rw [(ht i hi).2, (ht j hj).2, e])
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hv (ne_of_lt (hlt i j h hj))
  · exact h
  · exact absurd hv.symm (ne_of_lt (hlt j i h hi))

end Trees

theorem actC_eq (R I Ii : List Nat) (l X : Nat) : actC R I Ii l X =
    mulF 24 (mulF 24 (getL 0 R (getL 0 I l)) X) (getL 0 R (getL 0 Ii l)) := by
  unfold actC
  rw [CFSG.KC.F2W.mulW_eq, CFSG.KC.F2W.mulW_eq]

theorem conj_family (C : Subgroup NativeSporadic.Co1) {R I Ii : List Nat} {root n : ℕ} {T : STree}
    (hT : T.OK (actC R I Ii) (lenL I) root 576 n) (gen : ℕ → NativeSporadic.Co1)
    (hgen : ∀ l < lenL I, gen l ∈ C) (hG : ∀ l < lenL I, PM (gen l) (getL 0 R (getL 0 I l)))
    (hGi : ∀ l < lenL I, PM (gen l)⁻¹ (getL 0 R (getL 0 Ii l))) (hroot : Canon root)
    {τ : NativeSporadic.Co1} (hτ : PM τ root) :
    ∃ t : ℕ → NativeSporadic.Co1, (∀ i < n, t i ∈ C) ∧
      ∀ i < n, ∀ j < n, t i * τ * (t i)⁻¹ = t j * τ * (t j)⁻¹ → i = j := by
  obtain ⟨t, ht, hd⟩ := sort_family C (fun g M => matHom g * M * matHom g⁻¹)
    (fun g h M => by simp only [mul_inv_rev, map_mul, Matrix.mul_assoc])
    (fun M => by simp only [map_one, inv_one, Matrix.one_mul, Matrix.mul_one]) hT
    (fun X => rowsMatrix 24 (unpackR 24 X)) gen hgen Canon hroot
    (fun l _ y _ => by rw [actC_eq]; exact canon_mulF _ _)
    (fun l hl y _ => by
      rw [actC_eq, ← rM_mul, ← rM_mul, ← hG l hl, ← hGi l hl])
    (fun x y hx hy e => eq_of_unpackR hx hy
      (rowsMatrix_injective_of_valid (validRows_unpackR x) (validRows_unpackR y) e))
  refine ⟨t, fun i hi => (ht i hi).1, fun i hi j hj e => hd i hi j hj ?_⟩
  have hτ' : rowsMatrix 24 (unpackR 24 root) = matHom τ := hτ.symm
  rw [hτ', ← map_mul, ← map_mul, ← map_mul, ← map_mul, e]

theorem vec_family (C : Subgroup NativeSporadic.Co1) {RT I : List Nat} {root n : ℕ} {T : STree}
    (hT : T.OK (actV RT I) (lenL I) root 24 n) (hroot : root < 2 ^ 24)
    (gen : ℕ → NativeSporadic.Co1) (hgen : ∀ l < lenL I, gen l ∈ C)
    (hact : ∀ l < lenL I, ∀ v, co1Act (gen l) (toVecD 24 v) =
      toVecD 24 (vmF 24 (getL 0 RT (getL 0 I l)) v)) :
    ∃ t : ℕ → NativeSporadic.Co1, (∀ i < n, t i ∈ C ∧ valF 24 (T.tab i) < 2 ^ 24 ∧
      toVecD 24 (valF 24 (T.tab i)) = co1Act (t i) (toVecD 24 root)) ∧
      ∀ i < n, ∀ j < n, co1Act (t i) (toVecD 24 root) = co1Act (t j) (toVecD 24 root) → i = j :=
  sort_family C co1Act co1Act_mul co1Act_one hT (toVecD 24) gen hgen (fun y => y < 2 ^ 24) hroot
    (fun _ _ y _ => CFSG.KC.F2W.vmF_lt 24 _ y) (fun l hl y _ => (hact l hl y).symm)
    (fun _ _ hx hy e => toVecD_injective hx hy e)

section Fam

variable {W : InvFamW} (hW : InvFamOK W)
  (E : ℕ → NativeSporadic.Co1) (hE : ∀ i < W.R.length, PM (E i) (W.reg i))
include hW hE

omit hE in
theorem reg_tr : ∀ i < W.R.length, trK 24 (W.reg i) = W.regT i := by
  intro i hi
  have h := (allN_iff _ _).1 hW.tr i (by rw [lenL_eq]; exact hi)
  exact beq_iff.1 h

theorem reg_act {i : ℕ} (hi : i < W.R.length) (v : ℕ) :
    co1Act (E i) (toVecD 24 v) = toVecD 24 (vmF 24 (W.regT i) v) :=
  pm_act (hE i hi) (reg_tr hW i hi) v

theorem reg_fix {I vs : List Nat} (hI : ∀ i ∈ I, i < W.R.length) (h : fixAllK W.RT I vs = true) :
    ∀ i ∈ I, ∀ v ∈ vs, co1Act (E i) (toVecD 24 v) = toVecD 24 v := by
  intro i hi v hv
  rw [reg_act hW E hE (hI i hi), InvFamW.regT, fixAll_spec h i hi v hv]

omit hW in
theorem reg_inv {I Ii : List Nat} (hI : ∀ i ∈ I, i < W.R.length) (hIi : ∀ i ∈ Ii, i < W.R.length)
    (h : invPairsK W.R I Ii = true) :
    lenL I = lenL Ii ∧ ∀ l < lenL I, E (getL 0 Ii l) = (E (getL 0 I l))⁻¹ := by
  obtain ⟨h1, h2⟩ := andB_true_iff.1 h
  have hl := beq_iff.1 h1
  refine ⟨hl, fun l hl' => ?_⟩
  have hm := beq_iff.1 ((allN_iff _ _).1 h2 l hl')
  have ha := hI _ (getL_mem hl')
  have hb := hIi _ (getL_mem (hl ▸ hl'))
  have hp := pm_mul (hE _ ha) (hE _ hb)
  unfold InvFamW.reg at hp
  rw [hm] at hp
  refine eq_inv_of_mul_eq_one_right (matHom_injective ?_)
  rw [hp, map_one, unpackR_idF, rowsMatrix_idRows]

omit hW in
theorem reg_root {r : List Nat} (hr : ∀ i ∈ r, i < W.R.length) (h : rootK W.R r 7 = true)
    {s : NativeSporadic.Co1} (hs : PM s (W.reg 7)) :
    E (getL 0 r 1) = (E (getL 0 r 0))⁻¹ ∧
      PM (E (getL 0 r 0) * s * (E (getL 0 r 0))⁻¹) (W.reg (getL 0 r 2)) ∧
      Canon (W.reg (getL 0 r 2)) := by
  obtain ⟨h1, h2⟩ := andB_true_iff.1 h
  obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
  have hlen : r.length = 3 := by rw [← lenL_eq]; exact beq_iff.1 h1
  have hm : ∀ k < 3, getL 0 r k < W.R.length := fun k hk =>
    hr _ (getL_mem (by rw [lenL_eq, hlen]; exact hk))
  have hp := pm_mul (hE _ (hm 0 (by norm_num))) (hE _ (hm 1 (by norm_num)))
  unfold InvFamW.reg at hp
  rw [beq_iff.1 h2] at hp
  have hinv : E (getL 0 r 1) = (E (getL 0 r 0))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right (matHom_injective ?_)
    rw [hp, map_one, unpackR_idF, rowsMatrix_idRows]
  have he := beq_iff.1 h3
  refine ⟨hinv, ?_, ?_⟩
  · have hq := pm_mul (pm_mul (hE _ (hm 0 (by norm_num))) hs) (hE _ (hm 1 (by norm_num)))
    rw [hinv] at hq
    unfold InvFamW.reg at hq ⊢
    rw [he] at hq
    exact hq
  · unfold InvFamW.reg
    rw [← he]
    exact canon_mulF _ _

end Fam

theorem mem_stab2 {x : NativeSporadic.Co1} {a b : Vec24} (ha : co1Act x a = a) (hb : co1Act x b = b) :
    x ∈ stabOf a ⊓ stabOf b :=
  Subgroup.mem_inf.2 ⟨ha, hb⟩

theorem mem_stab3 {x : NativeSporadic.Co1} {a b c : Vec24} (ha : co1Act x a = a)
    (hb : co1Act x b = b) (hc : co1Act x c = c) : x ∈ stabOf a ⊓ stabOf b ⊓ stabOf c :=
  Subgroup.mem_inf.2 ⟨mem_stab2 ha hb, hc⟩

theorem mem_stab4 {x : NativeSporadic.Co1} {a b c d : Vec24} (ha : co1Act x a = a)
    (hb : co1Act x b = b) (hc : co1Act x c = c) (hd : co1Act x d = d) :
    x ∈ stabOf a ⊓ stabOf b ⊓ stabOf c ⊓ stabOf d :=
  Subgroup.mem_inf.2 ⟨mem_stab3 ha hb hc, hd⟩

theorem stab2_spec {x : NativeSporadic.Co1} {a b : Vec24} (h : x ∈ stabOf a ⊓ stabOf b) :
    co1Act x a = a ∧ co1Act x b = b :=
  Subgroup.mem_inf.1 h

theorem stab3_spec {x : NativeSporadic.Co1} {a b c : Vec24} (h : x ∈ stabOf a ⊓ stabOf b ⊓ stabOf c) :
    co1Act x a = a ∧ co1Act x b = b ∧ co1Act x c = c :=
  ⟨(stab2_spec (Subgroup.mem_inf.1 h).1).1, (stab2_spec (Subgroup.mem_inf.1 h).1).2,
    (Subgroup.mem_inf.1 h).2⟩

theorem stab4_spec {x : NativeSporadic.Co1} {a b c d : Vec24}
    (h : x ∈ stabOf a ⊓ stabOf b ⊓ stabOf c ⊓ stabOf d) :
    co1Act x a = a ∧ co1Act x b = b ∧ co1Act x c = c ∧ co1Act x d = d :=
  ⟨(stab3_spec (Subgroup.mem_inf.1 h).1).1, (stab3_spec (Subgroup.mem_inf.1 h).1).2.1,
    (stab3_spec (Subgroup.mem_inf.1 h).1).2.2, (Subgroup.mem_inf.1 h).2⟩

@[expose] def IsConjBy (c : Vec24) (s t : NativeSporadic.Co1) : Prop :=
  ∃ x, co1Act x c = c ∧ t = x * s * x⁻¹

theorem isConjBy_conj {c : Vec24} {s t g : NativeSporadic.Co1} (hg : co1Act g c = c)
    (ht : IsConjBy c s t) : IsConjBy c s (g * t * g⁻¹) := by
  obtain ⟨x, hx, rfl⟩ := ht
  exact conj_conj hg hx

theorem famA {W : InvFamW} (hW : InvFamOK W) {s : NativeSporadic.Co1}
    (hs : matHom s = rowsMatrix 24 rowsSA) :
    ∃ f : ℕ → NativeSporadic.Co1, (∀ i < 170775, ∀ j < 170775, f i = f j → i = j) ∧
      ∀ i < 170775, IsConjBy (toVecD 24 code3) s (f i) := by
  choose! E hE using reg_elems hW
  have hs' : PM s (W.reg 7) := by unfold PM; rw [← hW.sA]; exact hs
  have hb := bnd_spec hW.idx
  have hbK : ∀ {I : List Nat}, (∀ i ∈ I, i ∈ W.idxL) → ∀ i ∈ I, i < W.R.length :=
    fun hI i hi => by rw [← lenL_eq]; exact hb i (hI i hi)
  have bK1 := hbK (I := W.K1) (fun i hi => by simp [InvFamW.idxL, hi])
  have bK2 := hbK (I := W.K2) (fun i hi => by simp [InvFamW.idxL, hi])
  have bK2i := hbK (I := W.K2i) (fun i hi => by simp [InvFamW.idxL, hi])
  have bK3 := hbK (I := W.K3) (fun i hi => by simp [InvFamW.idxL, hi])
  have bK3i := hbK (I := W.K3i) (fun i hi => by simp [InvFamW.idxL, hi])
  have bK4 := hbK (I := W.K4) (fun i hi => by simp [InvFamW.idxL, hi])
  have bK4i := hbK (I := W.K4i) (fun i hi => by simp [InvFamW.idxL, hi])
  have br1 := hbK (I := W.r1) (fun i hi => by simp [InvFamW.idxL, hi])
  have br2 := hbK (I := W.r2) (fun i hi => by simp [InvFamW.idxL, hi])
  have br3 := hbK (I := W.r3) (fun i hi => by simp [InvFamW.idxL, hi])
  obtain ⟨hR1, hR23⟩ := andB_true_iff.1 hW.roots
  obtain ⟨hR2, hR3⟩ := andB_true_iff.1 hR23
  have l1 : lenL W.r1 = 3 := beq_iff.1 (andB_true_iff.1 hR1).1
  have l2 : lenL W.r2 = 3 := beq_iff.1 (andB_true_iff.1 hR2).1
  have l3 : lenL W.r3 = 3 := beq_iff.1 (andB_true_iff.1 hR3).1
  obtain ⟨-, hτ1, hc1⟩ := reg_root E hE br1 hR1 hs'
  obtain ⟨-, hτ2, hc2⟩ := reg_root E hE br2 hR2 hs'
  obtain ⟨-, hτ3, hc3⟩ := reg_root E hE br3 hR3 hs'
  have m1 : ∀ k < 3, getL 0 W.r1 k ∈ W.r1 := fun k hk => getL_mem (by rw [l1]; exact hk)
  have m2 : ∀ k < 3, getL 0 W.r2 k ∈ W.r2 := fun k hk => getL_mem (by rw [l2]; exact hk)
  have m3 : ∀ k < 3, getL 0 W.r3 k ∈ W.r3 := fun k hk => getL_mem (by rw [l3]; exact hk)
  have f3 := reg_fix hW E hE (I := W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
    [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0]) (fun i hi => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with (((h | h) | h) | h) | h | h | h
      · exact bK1 i h
      · exact bK2 i h
      · exact bK3 i h
      · exact bK4 i h
      · rw [h]
        exact br1 _ (m1 0 (by norm_num))
      · rw [h]
        exact br2 _ (m2 0 (by norm_num))
      · rw [h]
        exact br3 _ (m3 0 (by norm_num))) hW.fix3
  have F3 : ∀ {I : List Nat}, (∀ i ∈ I, i ∈ W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
      [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0]) → ∀ i ∈ I,
      co1Act (E i) (toVecD 24 code3) = toVecD 24 code3 :=
    fun hI i hi => f3 i (hI i hi) code3 (List.mem_singleton_self _)
  have f1 := reg_fix hW E hE bK1 hW.fix1
  have f2 := reg_fix hW E hE bK2 hW.fix2
  have fk3 := reg_fix hW E hE bK3 hW.fixK3
  have f4 := reg_fix hW E hE bK4 hW.fix4
  obtain ⟨hI2, hI34⟩ := andB_true_iff.1 hW.inv
  obtain ⟨hI3, hI4⟩ := andB_true_iff.1 hI34
  obtain ⟨li2, iv2⟩ := reg_inv E hE bK2 bK2i hI2
  obtain ⟨li3, iv3⟩ := reg_inv E hE bK3 bK3i hI3
  obtain ⟨li4, iv4⟩ := reg_inv E hE bK4 bK4i hI4
  have hvec := bnd_spec hW.vecs
  have ha0 : W.a0 < 2 ^ 24 := hvec _ (by simp)
  have ha1 : W.a1 < 2 ^ 24 := hvec _ (by simp)
  have hw0 : W.w0 < 2 ^ 24 := hvec _ (by simp)
  have hw1 : W.w1 < 2 ^ 24 := hvec _ (by simp)
  have act : ∀ {r : List Nat}, (∀ i ∈ r, i < W.R.length) → getL 0 r 2 ∈ r →
      ∀ {τ : NativeSporadic.Co1}, PM τ (W.reg (getL 0 r 2)) → ∀ v,
      co1Act τ (toVecD 24 v) = toVecD 24 (vmF 24 (W.regT (getL 0 r 2)) v) :=
    fun hr hm _ hτ v => pm_act hτ (reg_tr hW _ (hr _ hm)) v
  have ra := hW.rootAct
  simp only [andB_true_iff, beq_iff] at ra
  obtain ⟨e1a, e1b, e2a, e2b, e3⟩ := ra
  have τ1a0 := act br1 (m1 2 (by norm_num)) hτ1 W.a0
  have τ1a1 := act br1 (m1 2 (by norm_num)) hτ1 W.a1
  have τ2a0 := act br2 (m2 2 (by norm_num)) hτ2 W.a0
  have τ2a1 := act br2 (m2 2 (by norm_num)) hτ2 W.a1
  have τ3a0 := act br3 (m3 2 (by norm_num)) hτ3 W.a0
  rw [e1a] at τ1a0
  rw [e1b] at τ1a1
  rw [e2a] at τ2a0
  rw [e2b] at τ2a1
  rw [e3] at τ3a0
  set c3 := toVecD 24 code3
  set a0 := toVecD 24 W.a0
  set a1 := toVecD 24 W.a1
  set w0 := toVecD 24 W.w0
  set w1 := toVecD 24 W.w1
  set y1 := E (getL 0 W.r1 0)
  set y2 := E (getL 0 W.r2 0)
  set y3 := E (getL 0 W.r3 0)
  have y1c : co1Act y1 c3 = c3 := F3 (I := [getL 0 W.r1 0]) (fun i hi => by simp_all) _ (by simp)
  have y2c : co1Act y2 c3 = c3 := F3 (I := [getL 0 W.r2 0]) (fun i hi => by simp_all) _ (by simp)
  have y3c : co1Act y3 c3 = c3 := F3 (I := [getL 0 W.r3 0]) (fun i hi => by simp_all) _ (by simp)
  have g3 : ∀ {I : List Nat}, (∀ i ∈ I, i ∈ W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
      [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0]) → ∀ l < lenL I,
      co1Act (E (getL 0 I l)) c3 = c3 := fun hI l hl => F3 hI _ (getL_mem hl)
  have hK1 : ∀ i ∈ W.K1, i ∈ W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
      [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0] := fun i hi => by simp [hi]
  have hK2 : ∀ i ∈ W.K2, i ∈ W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
      [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0] := fun i hi => by simp [hi]
  have hK3 : ∀ i ∈ W.K3, i ∈ W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
      [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0] := fun i hi => by simp [hi]
  have hK4 : ∀ i ∈ W.K4, i ∈ W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
      [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0] := fun i hi => by simp [hi]
  obtain ⟨T1, hT1, dT1⟩ := conj_family (stabOf c3 ⊓ stabOf a0 ⊓ stabOf a1) hW.t1
    (fun l => E (getL 0 W.K3 l))
    (fun l hl => mem_stab3 (g3 hK3 l hl) (fk3 _ (getL_mem hl) _ (by simp))
      (fk3 _ (getL_mem hl) _ (by simp)))
    (fun l hl => hE _ (bK3 _ (getL_mem hl)))
    (fun l hl => by
      rw [← iv3 l hl]
      exact hE _ (bK3i _ (getL_mem (li3 ▸ hl)))) hc1 hτ1
  obtain ⟨T2, hT2, dT2⟩ := conj_family (stabOf c3 ⊓ stabOf a0 ⊓ stabOf a1 ⊓ stabOf w1) hW.t2
    (fun l => E (getL 0 W.K4 l))
    (fun l hl => mem_stab4 (g3 hK4 l hl) (f4 _ (getL_mem hl) _ (by simp))
      (f4 _ (getL_mem hl) _ (by simp)) (f4 _ (getL_mem hl) _ (by simp)))
    (fun l hl => hE _ (bK4 _ (getL_mem hl)))
    (fun l hl => by
      rw [← iv4 l hl]
      exact hE _ (bK4i _ (getL_mem (li4 ▸ hl)))) hc2 hτ2
  obtain ⟨T3, hT3, dT3⟩ := conj_family (stabOf c3 ⊓ stabOf a0 ⊓ stabOf w0) hW.t3
    (fun l => E (getL 0 W.K2 l))
    (fun l hl => mem_stab3 (g3 hK2 l hl) (f2 _ (getL_mem hl) _ (by simp))
      (f2 _ (getL_mem hl) _ (by simp)))
    (fun l hl => hE _ (bK2 _ (getL_mem hl)))
    (fun l hl => by
      rw [← iv2 l hl]
      exact hE _ (bK2i _ (getL_mem (li2 ▸ hl)))) hc3 hτ3
  obtain ⟨V1, hV1, dV1⟩ := vec_family (stabOf c3 ⊓ stabOf a0 ⊓ stabOf a1) hW.v1 hw1
    (fun l => E (getL 0 W.K3 l))
    (fun l hl => mem_stab3 (g3 hK3 l hl) (fk3 _ (getL_mem hl) _ (by simp))
      (fk3 _ (getL_mem hl) _ (by simp)))
    (fun l hl v => reg_act hW E hE (bK3 _ (getL_mem hl)) v)
  obtain ⟨V0, hV0, dV0⟩ := vec_family (stabOf c3 ⊓ stabOf a0) hW.v0 hw0
    (fun l => E (getL 0 W.K1 l))
    (fun l hl => mem_stab2 (g3 hK1 l hl) (f1 _ (getL_mem hl) _ (by simp)))
    (fun l hl v => reg_act hW E hE (bK1 _ (getL_mem hl)) v)
  obtain ⟨nm1, nm0⟩ := andB_true_iff.1 hW.mem
  have ne1 := not_memK nm1
  have ne0 := not_memK nm0
  obtain ⟨F1, dF1, pF1⟩ := fibre_union (fun t => IsConjBy c3 s t ∧ co1Act t a0 = a0)
    (u := a1) (w := w1) (n0 := 2835) (n1 := 120) (m := 162)
    (fun i => T1 i * (y1 * s * y1⁻¹) * (T1 i)⁻¹) (fun j => T2 j * (y2 * s * y2⁻¹) * (T2 j)⁻¹) V1
    dT1 (fun i hi => conj_act (stab3_spec (hT1 i hi)).2.2 (stab3_spec (hT1 i hi)).2.2 τ1a1)
    (fun i hi => ⟨conj_conj (stab3_spec (hT1 i hi)).1 y1c,
      conj_act (stab3_spec (hT1 i hi)).2.1 (stab3_spec (hT1 i hi)).2.1 τ1a0⟩)
    dT2 (fun j hj => conj_act (stab4_spec (hT2 j hj)).2.2.1 (stab4_spec (hT2 j hj)).2.2.2 τ2a1)
    (fun j hj => ⟨conj_conj (stab4_spec (hT2 j hj)).1 y2c,
      conj_act (stab4_spec (hT2 j hj)).2.1 (stab4_spec (hT2 j hj)).2.1 τ2a0⟩)
    (fun c hc => (stab3_spec (hV1 c hc).1).2.2) dV1
    (fun _ c hc e => ne1 c hc (toVecD_injective (hV1 c hc).2.1 ha1 ((hV1 c hc).2.2.trans e)))
    (fun c hc t ht => ⟨isConjBy_conj (stab3_spec (hV1 c hc).1).1 ht.1,
      conj_act (stab3_spec (hV1 c hc).1).2.1 (stab3_spec (hV1 c hc).1).2.1 ht.2⟩)
  obtain ⟨F, dF, pF⟩ := fibre_union (IsConjBy c3 s) (u := a0) (w := w0) (n0 := 2835 + 162 * 120)
    (n1 := 540) (m := 275) F1 (fun j => T3 j * (y3 * s * y3⁻¹) * (T3 j)⁻¹) V0
    dF1 (fun i hi => (pF1 i hi).2) (fun i hi => (pF1 i hi).1)
    dT3 (fun j hj => conj_act (stab3_spec (hT3 j hj)).2.1 (stab3_spec (hT3 j hj)).2.2 τ3a0)
    (fun j hj => conj_conj (stab3_spec (hT3 j hj)).1 y3c)
    (fun c hc => (stab2_spec (hV0 c hc).1).2) dV0
    (fun _ c hc e => ne0 c hc (toVecD_injective (hV0 c hc).2.1 ha0 ((hV0 c hc).2.2.trans e)))
    (fun c hc t ht => isConjBy_conj (stab2_spec (hV0 c hc).1).1 ht)
  exact ⟨F, dF, pF⟩

theorem famBC {W : InvFamW} (hW : InvFamOK W)
    (E : ℕ → NativeSporadic.Co1) (hE : ∀ i < W.R.length, PM (E i) (W.reg i)) {K : List Nat}
    {u w ri : ℕ} {T : STree} {s : NativeSporadic.Co1} (hK : ∀ i ∈ K, i < W.R.length)
    (hfix : fixAllK W.RT K [code4, u] = true) (hri : ri < W.R.length) (hs : PM s (W.reg ri))
    (himg : vmF 24 (W.regT ri) u = w) (hw : w < 2 ^ 24)
    (hT : T.OK (actV W.RT K) (lenL K) w 24 2000) :
    ∃ f : ℕ → NativeSporadic.Co1, (∀ i < 2000, ∀ j < 2000, f i = f j → i = j) ∧
      ∀ i < 2000, IsConjBy (toVecD 24 code4) s (f i) := by
  have fx := reg_fix hW E hE hK hfix
  obtain ⟨V, hV, dV⟩ := vec_family (stabOf (toVecD 24 code4) ⊓ stabOf (toVecD 24 u)) hT hw
    (fun l => E (getL 0 K l))
    (fun l hl => mem_stab2 (fx _ (getL_mem hl) _ (by simp)) (fx _ (getL_mem hl) _ (by simp)))
    (fun l hl v => reg_act hW E hE (hK _ (getL_mem hl)) v)
  have hsu : co1Act s (toVecD 24 u) = toVecD 24 w := by
    rw [pm_act hs (reg_tr hW ri hri) u, himg]
  obtain ⟨F, dF, pF⟩ := fibre_union (IsConjBy (toVecD 24 code4) s) (u := toVecD 24 u)
    (w := toVecD 24 w) (n0 := 0) (n1 := 1) (m := 2000) (fun _ => 1) (fun _ => s) V
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (fun i hi j hj _ => by omega) (fun _ _ => hsu)
    (fun _ _ => ⟨1, co1Act_one _, by group⟩) (fun c hc => (stab2_spec (hV c hc).1).2) dV
    (fun h => absurd h (Nat.lt_irrefl 0))
    (fun c hc t ht => isConjBy_conj (stab2_spec (hV c hc).1).1 ht)
  exact ⟨F, fun i hi j hj => dF i (by omega) j (by omega), fun i hi => pF i (by omega)⟩

theorem famB {W : InvFamW} (hW : InvFamOK W) {s : NativeSporadic.Co1}
    (hs : matHom s = rowsMatrix 24 rowsSB) :
    ∃ f : ℕ → NativeSporadic.Co1, (∀ i < 2000, ∀ j < 2000, f i = f j → i = j) ∧
      ∀ i < 2000, IsConjBy (toVecD 24 code4) s (f i) := by
  choose! E hE using reg_elems hW
  have hb : ∀ i ∈ W.idxL, i < W.R.length := fun i hi => by rw [← lenL_eq]; exact bnd_spec hW.idx i hi
  have hs' : PM s (W.reg 9) := by unfold PM; rw [← hW.sB]; exact hs
  exact famBC hW E hE (fun i hi => hb i (by simp [InvFamW.idxL, hi])) hW.fixB
    (hb 9 (by simp [InvFamW.idxL])) hs' (beq_iff.1 (andB_true_iff.1 hW.img).1)
    (bnd_spec hW.vecs _ (by simp)) hW.vb

theorem famC {W : InvFamW} (hW : InvFamOK W) {s : NativeSporadic.Co1}
    (hs : matHom s = rowsMatrix 24 rowsSC) :
    ∃ f : ℕ → NativeSporadic.Co1, (∀ i < 2000, ∀ j < 2000, f i = f j → i = j) ∧
      ∀ i < 2000, IsConjBy (toVecD 24 code4) s (f i) := by
  choose! E hE using reg_elems hW
  have hb : ∀ i ∈ W.idxL, i < W.R.length := fun i hi => by rw [← lenL_eq]; exact bnd_spec hW.idx i hi
  have hs' : PM s (W.reg 11) := by unfold PM; rw [← hW.sC]; exact hs
  exact famBC hW E hE (fun i hi => hb i (by simp [InvFamW.idxL, hi])) hW.fixC
    (hb 11 (by simp [InvFamW.idxL])) hs' (beq_iff.1 (andB_true_iff.1 hW.img).2)
    (bnd_spec hW.vecs _ (by simp)) hW.vc

end CFSG.Sporadic.Co1.Module.InvFam

end
