module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadAct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM2Max

public section

namespace CFSG.Quasithin.J4M2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Rad
open CFSG.Sporadic.J4.QT2 (w₀ Zl z0_mem_Zl)

namespace Om

section PushFold

variable {α : Type*}

@[expose] def pushFold (f : ℕ → Array α → α) (n : ℕ) : Array α :=
  (List.range n).foldl (fun acc i => acc.push (f i acc)) #[]

theorem pushFold_succ (f : ℕ → Array α → α) (n : ℕ) :
    pushFold f (n + 1) = (pushFold f n).push (f n (pushFold f n)) := by
  unfold pushFold
  rw [List.range_succ, List.foldl_append]
  rfl

theorem pushFold_size (f : ℕ → Array α → α) (n : ℕ) : (pushFold f n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pushFold_succ, Array.size_push, ih]

theorem pushFold_getElem_prefix [Inhabited α] (f : ℕ → Array α → α) {j i n : ℕ} (hj : j < i)
    (hin : i ≤ n) : (pushFold f n)[j]! = (pushFold f i)[j]! := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n i with h | h
    · have : i = n + 1 := by omega
      subst this
      rfl
    · rw [pushFold_succ]
      have hs : j < (pushFold f n).size := by rw [pushFold_size]; omega
      rw [← ih (by omega), getElem!_pos _ j (by simp [pushFold_size]; omega), getElem!_pos _ j hs,
        Array.getElem_push_lt]

theorem pushFold_getElem [Inhabited α] (f : ℕ → Array α → α) {i n : ℕ} (hi : i < n) :
    (pushFold f n)[i]! = f i (pushFold f i) := by
  rw [pushFold_getElem_prefix f (j := i) (i := i + 1) (n := n) (by omega) hi, pushFold_succ]
  have hs : (pushFold f i).size = i := pushFold_size f i
  rw [getElem!_pos _ i (by simp [hs]), Array.getElem_push, dite_eq_right (by omega)]

end PushFold

theorem wf_default : (default : V2).wf = true := by decide

theorem wf_getElem!_set! {r : Array V2} (hr : ∀ k : ℕ, (r[k]! : V2).wf = true) {i : ℕ} {v : V2}
    (hv : v.wf = true) (j : ℕ) : ((r.set! i v)[j]! : V2).wf = true := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  have := hr j
  simp only [getElem!_def] at this
  obtain rfl | h1 := eq_or_ne i j
  · by_cases h2 : i < r.size
    · simpa [h2] using hv
    · simpa [h2] using wf_default
  · simpa [h1] using this

theorem wf_getElem!_of_mem {r : Array V2} (hr : ∀ x ∈ r, x.wf = true) (k : ℕ) :
    (r[k]! : V2).wf = true := by
  by_cases h : k < r.size
  · rw [getElem!_pos r k h]
    exact hr _ (Array.getElem_mem h)
  · rw [getElem!_neg r k h]
    exact wf_default

@[expose] def RowInv (r : Array V2) : Prop := r.size = 112 ∧ ∀ k : ℕ, (r[k]! : V2).wf = true

theorem RowInv.wf_get {r : Array V2} (h : RowInv r) (k : ℕ) : (r[k]! : V2).wf = true := h.2 k

theorem RowInv.set {r : Array V2} (h : RowInv r) (i : ℕ) {v : V2} (hv : v.wf = true) :
    RowInv (r.set! i v) :=
  ⟨by rw [Array.size_set!]; exact h.1, wf_getElem!_set! h.2 hv⟩

theorem RowInv.xorSet {r : Array V2} (h : RowInv r) (i : ℕ) {v : V2} (hv : v.wf = true) :
    RowInv (r.set! i ((r[i]! : V2).xor v)) :=
  h.set i (V2.xor_wf (h.2 i) hv)

theorem rowInv_idRows : RowInv idRows := ⟨idRows_size, wf_getElem!_of_mem idRows_wf⟩

theorem wfR_of_rowInv {r : Array V2} (h : RowInv r) : wfR r = true :=
  wfR_of h.1 fun x hx => by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    have := h.2 i
    rwa [getElem!_pos r i hi] at this

@[expose] def YieldsP {β : Type} (P : β → Prop) : ForInStep β → Prop
  | .done _ => False
  | .yield b => P b

theorem forIn_id_inv {β : Type} (P : β → Prop) (f : ℕ → β → Id (ForInStep β)) :
    ∀ (l : List ℕ) (init : β), P init → (∀ i b, P b → YieldsP P (f i b)) →
      P (forIn l init f).run := by
  intro l
  induction l with
  | nil => intro init h0 _; simpa using h0
  | cons a l ih =>
    intro init h0 hf
    have h1 := hf a init h0
    rw [List.forIn_cons]
    generalize f a init = x at h1 ⊢
    cases x with
    | done b => exact h1.elim
    | yield b => exact ih b h1 hf

theorem yieldsP_bind {β γ : Type} {P : β → Prop} (E : Id γ) (g : γ → Id (ForInStep β))
    (h : ∀ p, YieldsP P (g p)) : YieldsP P (E >>= g : Id (ForInStep β)) := h E

theorem yieldsP_bind_inv {β γ : Type} {P : β → Prop} (Q : γ → Prop) (E : Id γ) (hE : Q E.run)
    (g : γ → Id (ForInStep β)) (h : ∀ x, Q x → YieldsP P (g x)) :
    YieldsP P (E >>= g : Id (ForInStep β)) := h E hE

theorem rowInv_invRows (X : Array V2) : RowInv (invRows X) := by
  unfold invRows
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_id_inv (fun s : Array V2 × Array V2 => RowInv s.2) _ _ (X, idRows) rowInv_idRows ?_
  intro c s hs
  refine yieldsP_bind _ _ fun p => ?_
  by_cases hp : p < 112
  · rw [ite_eq_left hp]
    refine yieldsP_bind_inv (fun s' : Array V2 × Array V2 => RowInv s'.2) _ ?_ _ (fun x hx => hx)
    refine forIn_id_inv (fun s' : Array V2 × Array V2 => RowInv s'.2) _ _ _ ?_ ?_
    · exact (hs.set p (hs.wf_get c)).set c (hs.wf_get p)
    · intro i b hb
      split_ifs
      · exact hb.xorSet i (hs.wf_get p)
      · exact hb
  · rw [ite_eq_right hp]
    exact hs

theorem wfR_invRows (X : Array V2) : wfR (invRows X) = true := wfR_of_rowInv (rowInv_invRows X)

theorem eq_of_rowsMatrix_eq_of_wfR {X Y : Array V2} (hX : wfR X = true) (hY : wfR Y = true)
    (h : rowsMatrix X = rowsMatrix Y) : X = Y := by
  by_contra hne
  have h1 : eqRows X Y = false := by
    by_contra h2
    exact hne (eqRows_iff.1 (by simpa using h2))
  exact ne_of_eqRows_false hX hY h1 h

theorem foldl_insert_contains (f : ℕ → Array V2) (l : List ℕ) (S : Std.HashSet (Array V2))
    (X : Array V2) :
    (l.foldl (fun S c => S.insert (f c)) S).contains X = true ↔
      S.contains X = true ∨ ∃ c ∈ l, f c = X := by
  induction l generalizing S with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((h | h) | ⟨d, hd, h⟩)
      · exact Or.inr ⟨c, List.mem_cons_self, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, h⟩
    · rintro (h | ⟨d, hd, h⟩)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨d, hd, h⟩

@[expose] def tMatsStep (i : ℕ) (acc : Array (Array V2)) : Array V2 :=
  if i == 0 then idRows else mulT gmats[genData[i]!]! (frTable acc[parData[i]!]!)

theorem tMats_eq : tMats = pushFold tMatsStep 77 := rfl

theorem tMats_zero : tMats[0]! = idRows := by
  rw [tMats_eq, pushFold_getElem _ (by norm_num), tMatsStep]
  simp

theorem tMats_of_pos {i : ℕ} (hi0 : 0 < i) (hi : i < 77) (hp : parData[i]! < i) :
    tMats[i]! = mulRows gmats[genData[i]!]! tMats[parData[i]!]! := by
  rw [tMats_eq, pushFold_getElem _ hi, tMatsStep, ite_eq_right (by simp; omega),
    ← pushFold_getElem_prefix _ hp hi.le, mulT_frTable]

section Cert


theorem chkGens_spec : chkGens = true := Certificates.certificate4200.1

theorem chkOrbit_spec : chkOrbit = true := Certificates.certificate4200.2.1

theorem chkV0_spec : chkV0 = true := Certificates.certificate4200.2.2.1

theorem gmats_wfR {n : ℕ} (hn : n < 32) : wfR gmats[n]! = true := by
  have h := chkGens_spec
  unfold chkGens at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact (h n hn).1

theorem chkOrbit_parts :
    vecs.size = 77 ∧ (∀ (i : ℕ) (h : i < vecs.size), (vecs[i]).wf = true) ∧ vecs[0]! = rootV ∧
    (∀ i : ℕ, 0 < i → i < 77 → parData[i]! < i ∧ genData[i]! < 32 ∧
      frApply gtabs[genData[i]!]! vecs[i]! = vecs[parData[i]!]!) ∧
    (∀ i < 77, ∀ j < i, vecs[i]! ≠ vecs[j]!) ∧
    (∀ n < 32, ∀ i < 77, (sigData[n]!)[i]! < 77 ∧
      frApply gtabs[n]! vecs[(sigData[n]!)[i]!]! = vecs[i]!) := by
  have h := chkOrbit_spec
  unfold chkOrbit at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, V2.beq_iff, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_, h6⟩
  · intro i hi0 hi
    rcases h4 i hi with h | ⟨⟨h7, h8⟩, h9⟩
    · omega
    · exact ⟨h7, h8, h9⟩
  · intro i hi j hj e
    have h7 := h5 i hi j hj
    rw [V2.beq_iff.2 e] at h7
    exact Bool.noConfusion h7

theorem vecs_wf {i : ℕ} (hi : i < 77) : (vecs[i]! : V2).wf = true := by
  have h := chkOrbit_parts.2.1 i (by rw [chkOrbit_parts.1]; exact hi)
  rwa [getElem!_pos vecs i (by rw [chkOrbit_parts.1]; exact hi)]

theorem vecs_zero : vecs[0]! = rootV := chkOrbit_parts.2.2.1

theorem tree_parts {i : ℕ} (hi0 : 0 < i) (hi : i < 77) :
    parData[i]! < i ∧ genData[i]! < 32 ∧
      frApply gtabs[genData[i]!]! vecs[i]! = vecs[parData[i]!]! :=
  chkOrbit_parts.2.2.2.1 i hi0 hi

theorem vecs_ne {i j : ℕ} (hi : i < 77) (hij : j < i) : vecs[i]! ≠ vecs[j]! :=
  chkOrbit_parts.2.2.2.2.1 i hi j hij

theorem sig_parts {n i : ℕ} (hn : n < 32) (hi : i < 77) :
    (sigData[n]!)[i]! < 77 ∧ frApply gtabs[n]! vecs[(sigData[n]!)[i]!]! = vecs[i]! :=
  chkOrbit_parts.2.2.2.2.2 n hn i hi

theorem cMat_fix {i : ℕ} (hi : i < 77) : frApply (frTable cMat) vecs[i]! = vecs[i]! := by
  have h : chkC = true := Certificates.certificate4200.2.2.2
  unfold chkC at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, V2.beq_iff] at h
  exact h.2 i hi

theorem chkV0_parts {i : ℕ} (hi : i < 77) : invOK i = true ∧ inI5 i = i5List.contains i := by
  have h := chkV0_spec
  unfold chkV0 at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h i hi

theorem wfR_wordT_uWord {j : ℕ} (hj : j < 11) : wfR (wordT (uWord j)) = true := by
  have h := gmats_wfR (n := 17 + j) (by omega)
  rwa [genWord_getElem_gmats (by omega), genWord_u hj] at h

theorem wfR_etaMn (n : ℕ) (hn : n ≤ 11) (c : ℕ) : wfR (etaMn n c) = true := by
  induction n with
  | zero => simpa [etaMn] using wfR_idRows
  | succ n ih =>
    rw [etaMn_succ]
    split_ifs
    · rw [uTabs_getElem (by omega), mulT_frTable]
      exact wfR_mulRows (ih (by omega)) (wfR_wordT_uWord (by omega))
    · exact ih (by omega)

theorem wfR_etaM (c : ℕ) : wfR (etaM c) = true := wfR_etaMn 11 le_rfl c

end Cert

end Om

open Om

noncomputable def ptElt (i : ℕ) : J :=
  if _h : 0 < i ∧ parData[i]! < i then gE genData[i]! * ptElt parData[i]! else 1
termination_by i
decreasing_by omega

theorem ptElt_zero : ptElt 0 = 1 := by
  rw [ptElt]
  simp

theorem ptElt_of_pos {i : ℕ} (hi : 0 < i) (hp : parData[i]! < i) :
    ptElt i = gE genData[i]! * ptElt parData[i]! := by
  rw [ptElt, dite_eq_left ⟨hi, hp⟩]

section Tree


theorem ptElt_tree {i : ℕ} (hi0 : 0 < i) (hi : i < 77) :
    ptElt i = gE genData[i]! * ptElt parData[i]! :=
  ptElt_of_pos hi0 (tree_parts hi0 hi).1

theorem Mx_ptElt_wfR (hM : MatFacts) {i : ℕ} (hi : i < 77) :
    Mx (ptElt i) = rowsMatrix tMats[i]! ∧ wfR tMats[i]! = true := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [ptElt_zero, tMats_zero, map_one]
      exact ⟨rowsMatrix_idRows.symm, wfR_idRows⟩
    · obtain ⟨hp, hg, -⟩ := tree_parts hi0 hi
      obtain ⟨ih1, ih2⟩ := ih _ hp (by omega)
      rw [ptElt_of_pos hi0 hp, tMats_of_pos hi0 hi hp, map_mul, Mx_gE hM hg, ih1,
        rowsMatrix_mulRows]
      exact ⟨rfl, wfR_mulRows (gmats_wfR hg) ih2⟩

theorem Mx_ptElt (hM : MatFacts) {i : ℕ} (hi : i < 77) : Mx (ptElt i) = rowsMatrix tMats[i]! :=
  (Mx_ptElt_wfR hM hi).1

theorem wfR_tMats (hM : MatFacts) {i : ℕ} (hi : i < 77) : wfR tMats[i]! = true :=
  (Mx_ptElt_wfR hM hi).2

end Tree

theorem ptElt_mem_M2
    (hM : MatFacts) {i : ℕ} (hi : i < 77) : ptElt i ∈ M2 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [ptElt_zero]
      exact M2.one_mem
    · obtain ⟨hp, hg, -⟩ := tree_parts hi0 hi
      rw [ptElt_of_pos hi0 hp]
      exact M2.mul_mem (gE_mem_M2 hM hg) (ih _ hp (by omega))

@[expose] noncomputable def pt (i : ℕ) : J ⧸ Hj := ((ptElt i : J) : J ⧸ Hj)

theorem pt_zero : pt 0 = basePt := by
  rw [pt, ptElt_zero]
  rfl

theorem ptElt_smul_basePt (i : ℕ) : ptElt i • (basePt : J ⧸ Hj) = pt i :=
  smul_basePt_eq_mk _

theorem rowOf_smul (hM : MatFacts) (g : J) (x : J ⧸ Hj) :
    rowOf hM (g • x) = g • rowOf hM x := by
  induction x using QuotientGroup.induction_on with
  | _ h =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, rowOf_mk, rowOf_mk, mul_smul]

theorem smul_toRow_of_frApply {g : J} {X : Array V2} (hX : Mx g = rowsMatrix X) {v u : V2}
    (h : frApply (frTable X) v = u) : g • toRow u.toVec = toRow v.toVec := by
  have e : Mx g * Mx g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [← ofRow_inj, smul_row, ← h, frApply_toVec_eq_vecMul, ← hX, ← Mx_apply]
  simp only [ofRow, toRow]
  rw [Matrix.vecMul_vecMul, e, Matrix.vecMul_one]

section Rows


theorem rowOf_pt (hM : MatFacts) {i : ℕ} (hi : i < 77) :
    rowOf hM (pt i) = toRow (vecs[i]! : V2).toVec := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pt_zero]
      show rowOf hM (((1 : J) : J ⧸ Hj)) = _
      rw [rowOf_mk, one_smul, vecs_zero]
      rfl
    · obtain ⟨hp, hg, hfr⟩ := tree_parts hi0 hi
      have ih' := ih _ hp (by omega)
      rw [pt, ptElt_of_pos hi0 hp, rowOf_mk, mul_smul]
      have h1 : ptElt parData[i]! • w₀ = toRow (vecs[parData[i]!]! : V2).toVec := by
        rw [← rowOf_mk hM]
        exact ih'
      rw [h1]
      refine smul_toRow_of_frApply (Mx_gE hM hg) ?_
      rw [← gtabs_getElem hg]
      exact hfr

theorem pt_injective (hF : J4Facts) {i j : ℕ} (hi : i < 77) (hj : j < 77) (h : pt i = pt j) :
    i = j := by
  have h1 := congrArg (rowOf hF.mat) h
  rw [rowOf_pt hF.mat hi, rowOf_pt hF.mat hj] at h1
  have h2 : (vecs[i]! : V2).toVec = (vecs[j]! : V2).toVec := h1
  have h3 : vecs[i]! = vecs[j]! := (V2.toVec_inj (vecs_wf hi) (vecs_wf hj)).1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact vecs_ne hj hlt h3.symm
  · exact vecs_ne hi hgt h3

theorem pt_eq_pt_iff (hF : J4Facts) {i j : ℕ} (hi : i < 77) (hj : j < 77) :
    pt i = pt j ↔ i = j :=
  ⟨pt_injective hF hi hj, fun h => h ▸ rfl⟩

theorem pt_ne_basePt (hF : J4Facts) {i : ℕ} (hi : i < 77) (hi0 : 0 < i) : pt i ≠ basePt := by
  rw [← pt_zero]
  exact fun h => absurd (pt_injective hF hi (by norm_num) h) (by omega)

theorem ptElt_mem_Hj_iff (hF : J4Facts) {i : ℕ} (hi : i < 77) : ptElt i ∈ Hj ↔ i = 0 := by
  rw [← smul_basePt_eq_self_iff, ptElt_smul_basePt, ← pt_zero, pt_eq_pt_iff hF hi (by norm_num)]

end Rows

noncomputable abbrev OrbM2 : Set (J ⧸ Hj) := MulAction.orbit ↥M2 (basePt : J ⧸ Hj)

theorem mem_OrbM2_iff {w : J ⧸ Hj} : w ∈ OrbM2 ↔ ∃ q ∈ M2, q • basePt = w := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, q.2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩

theorem pt_mem_OrbM2
    (hM : MatFacts) {i : ℕ} (hi : i < 77) : pt i ∈ OrbM2 :=
  mem_OrbM2_iff.2 ⟨ptElt i, ptElt_mem_M2 hM hi, ptElt_smul_basePt i⟩

section Orbit


theorem pt_range (hF : J4Facts) :
    {w : J ⧸ Hj | ∃ q ∈ M2, q • basePt = w} = {w | ∃ i < 77, w = pt i} := by
  have hsub : {w : J ⧸ Hj | ∃ i < 77, w = pt i} ⊆ {w : J ⧸ Hj | ∃ q ∈ M2, q • basePt = w} := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨ptElt i, ptElt_mem_M2 hF.mat hi, ptElt_smul_basePt i⟩
  have himg : {w : J ⧸ Hj | ∃ i < 77, w = pt i} = pt '' (Set.Iio 77) := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  have hinj : Set.InjOn pt (Set.Iio 77) := fun i hi j hj h => pt_injective hF hi hj h
  have hcard : ({w : J ⧸ Hj | ∃ i < 77, w = pt i}).ncard = 77 := by
    rw [himg, hinj.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  have h77 : {w : J ⧸ Hj | ∃ q ∈ M2, q • basePt = w}.ncard = 77 :=
    ncard_orbit_centralizer hF (z := z0) z0_mem_Zl
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, h77])).symm

noncomputable def ePt (hF : J4Facts) : Fin 77 ≃ ↥OrbM2 :=
  Equiv.ofBijective (fun i => ⟨pt i, pt_mem_OrbM2 hF.mat i.2⟩)
    ⟨fun i j h => Fin.ext (pt_injective hF i.2 j.2 (congrArg Subtype.val h)), fun w => by
      have h : w.1 ∈ {w : J ⧸ Hj | ∃ q ∈ M2, q • basePt = w} := mem_OrbM2_iff.1 w.2
      rw [pt_range hF] at h
      obtain ⟨i, hi, hw⟩ := h
      exact ⟨⟨i, hi⟩, Subtype.ext hw.symm⟩⟩

noncomputable def rho (hF : J4Facts) : ↥M2 →* Equiv.Perm (Fin 77) :=
  (Equiv.permCongrHom (ePt hF).symm).toMonoidHom.comp (MulAction.toPermHom ↥M2 ↥OrbM2)

theorem rho_apply (hF : J4Facts) (m : ↥M2) (x : ↥OrbM2) :
    rho hF m ((ePt hF).symm x) = (ePt hF).symm (m • x) := by
  simp [rho, Equiv.permCongrHom]

theorem rho_spec (hF : J4Facts) (g : ↥M2) (i j : Fin 77) :
    rho hF g i = j ↔ (g : J) • pt i = pt j := by
  have h1 : rho hF g i = (ePt hF).symm (g • ePt hF i) := by
    simpa using rho_apply hF g (ePt hF i)
  rw [h1, Equiv.symm_apply_eq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem smul_pt_eq_pt_rho (hF : J4Facts) (g : ↥M2) (i : Fin 77) :
    (g : J) • pt i = pt (rho hF g i) :=
  (rho_spec hF g i (rho hF g i)).1 rfl

theorem rho_gE (hF : J4Facts) (n : ℕ) (hn : n < 32) (i : Fin 77) :
    (rho hF ⟨gE n, gE_mem_M2 hF.mat hn⟩ i : ℕ) = (sigData[n]!)[i.val]! := by
  obtain ⟨hlt, hfr⟩ := sig_parts hn i.2
  have h1 : gE n • pt i = pt ((sigData[n]!)[i.val]!) := by
    apply rowOf_injective hF
    rw [rowOf_smul hF.mat, rowOf_pt hF.mat i.2, rowOf_pt hF.mat hlt]
    refine smul_toRow_of_frApply (Mx_gE hF.mat hn) ?_
    rw [← gtabs_getElem hn]
    exact hfr
  have h2 := (rho_spec hF ⟨gE n, gE_mem_M2 hF.mat hn⟩ i ⟨(sigData[n]!)[i.val]!, hlt⟩).2 h1
  rw [h2]

theorem rho_zero_iff (hF : J4Facts) (g : ↥M2) : rho hF g 0 = 0 ↔ (g : J) ∈ Hj := by
  rw [rho_spec hF g 0 0]
  have h0 : pt ((0 : Fin 77) : ℕ) = basePt := pt_zero
  rw [h0]
  exact smul_basePt_eq_self_iff

theorem rho_cE (hF : J4Facts) : rho hF ⟨cE, cE_mem_M2 hF.mat⟩ = 1 := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  refine (rho_spec hF _ i i).2 ?_
  apply rowOf_injective hF
  rw [rowOf_smul hF.mat, rowOf_pt hF.mat i.2]
  exact smul_toRow_of_frApply (Mx_cE hF.mat) (cMat_fix i.2)

theorem rho_ptElt_zero (hF : J4Facts) {i : ℕ} (hi : i < 77) :
    rho hF ⟨ptElt i, ptElt_mem_M2 hF.mat hi⟩ 0 = ⟨i, hi⟩ := by
  rw [rho_spec hF _ 0 ⟨i, hi⟩]
  show ptElt i • pt 0 = pt i
  rw [pt_zero, ptElt_smul_basePt]

theorem rho_transitive (hF : J4Facts) (i j : Fin 77) : ∃ g : ↥M2, rho hF g i = j := by
  let a : ↥M2 := ⟨ptElt i, ptElt_mem_M2 hF.mat i.2⟩
  let b : ↥M2 := ⟨ptElt j, ptElt_mem_M2 hF.mat j.2⟩
  have ha : rho hF a 0 = i := rho_ptElt_zero hF i.2
  have hb : rho hF b 0 = j := rho_ptElt_zero hF j.2
  have hai : (rho hF a)⁻¹ i = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, ha]
  refine ⟨b * a⁻¹, ?_⟩
  rw [map_mul, Equiv.Perm.mul_apply, map_inv, hai, hb]

end Orbit

theorem mem_eSet_iff (X : Array V2) : eSet.contains X = true ↔ ∃ c < 2048, X = etaM c := by
  unfold eSet
  rw [foldl_insert_contains etaM (List.range 2048) ∅ X, Std.HashSet.contains_empty]
  simp only [Bool.false_eq_true, false_or, List.mem_range]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

section V0


theorem conj_mem_Eg_iff (hM : MatFacts) {i : ℕ} (hi : i < 77) (c : ℕ) :
    (ptElt i)⁻¹ * eta uJ 11 c * ptElt i ∈ Eg uJ 11 ↔
      eSet.contains (mulT (mulT (invRows tMats[i]!) (frTable (etaM c))) (frTable tMats[i]!)) =
        true := by
  obtain ⟨hMt, hwT⟩ := Mx_ptElt_wfR hM hi
  have hMti : Mx (ptElt i)⁻¹ = rowsMatrix (invRows tMats[i]!) :=
    rowsMatrix_inv_of_mul hMt (chkV0_parts hi).1
  have hX : rowsMatrix (mulT (mulT (invRows tMats[i]!) (frTable (etaM c))) (frTable tMats[i]!)) =
      Mx ((ptElt i)⁻¹ * eta uJ 11 c * ptElt i) := by
    rw [mulT_frTable, mulT_frTable, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_etaM hM,
      map_mul, map_mul, hMti, hMt]
  have hwX : wfR (mulT (mulT (invRows tMats[i]!) (frTable (etaM c))) (frTable tMats[i]!)) =
      true := by
    rw [mulT_frTable, mulT_frTable]
    exact wfR_mulRows (wfR_mulRows (wfR_invRows _) (wfR_etaM c)) hwT
  rw [mem_eSet_iff]
  constructor
  · intro h
    obtain ⟨d, hd, hd'⟩ := (mem_Eg_iff (elem_uJ hM)).1 h
    refine ⟨d, hd, eq_of_rowsMatrix_eq_of_wfR hwX (wfR_etaM d) ?_⟩
    rw [hX, rowsMatrix_etaM hM, hd']
  · rintro ⟨d, hd, hXd⟩
    have h : (ptElt i)⁻¹ * eta uJ 11 c * ptElt i = eta uJ 11 d := by
      apply Mx_injective
      rw [← hX, hXd, rowsMatrix_etaM hM]
    rw [h]
    exact eta_mem_Eg 11 le_rfl d

end V0

theorem V0_le_conjSub_iff (g : J) (A : Subgroup J) :
    V0 ≤ conjSub g A ↔ g⁻¹ * eta uJ 11 422 * g ∈ A ∧ g⁻¹ * eta uJ 11 553 * g ∈ A ∧
      g⁻¹ * eta uJ 11 1131 * g ∈ A := by
  simp only [V0, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
    SetLike.mem_coe, mem_conjSub]

theorem v0_le_conj_iff
    (hM : MatFacts) (i : Fin 77) : V0 ≤ conjSub (ptElt i) (Eg uJ 11) ↔ i.val ∈ i5List := by
  have hi : i.val < 77 := i.2
  obtain ⟨-, h5⟩ := chkV0_parts hi
  rw [V0_le_conjSub_iff, conj_mem_Eg_iff hM hi, conj_mem_Eg_iff hM hi, conj_mem_Eg_iff hM hi,
    ← List.contains_iff_mem, ← h5]
  unfold inI5 v0Tabs zT zM
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]

end CFSG.Quasithin.J4M2
