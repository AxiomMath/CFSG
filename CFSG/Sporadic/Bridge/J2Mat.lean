module

public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Sporadic.Bridge.J2

open Matrix

@[expose] def dotL : List ℕ → List ℕ → ℕ
  | a :: r, b :: c => Nat.add (Nat.mul a b) (dotL r c)
  | _, _ => 0

@[expose] def mvL (X : List (List ℕ)) (v : List ℕ) : List ℕ :=
  X.map fun r => Nat.mod (dotL r v) 5

@[expose] def colsL (Y : List (List ℕ)) : List (List ℕ) :=
  (List.range 14).map fun j => Y.map fun r => r.getD j 0

@[expose] def mulL (X Y : List (List ℕ)) : List (List ℕ) :=
  X.map fun r => (colsL Y).map fun c => Nat.mod (dotL r c) 5

@[expose] def wfM (X : List (List ℕ)) : Bool :=
  X.length == 14 && X.all fun r => r.length == 14

@[expose] def toV (v : List ℕ) : Fin 14 → ZMod 5 := fun i => ((v.getD i.val 0 : ℕ) : ZMod 5)

@[expose] def toM (X : List (List ℕ)) : Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  Matrix.of fun i j => (((X.getD i.val []).getD j.val 0 : ℕ) : ZMod 5)

theorem dotL_eq_sum : ∀ (n : ℕ) (r c : List ℕ), r.length = n → c.length = n →
    dotL r c = ∑ k ∈ Finset.range n, r.getD k 0 * c.getD k 0 := by
  intro n
  induction n with
  | zero =>
    intro r c hr hc
    rw [List.length_eq_zero_iff] at hr
    subst hr
    simp [dotL]
  | succ n ih =>
    intro r c hr hc
    obtain ⟨a, r, rfl⟩ := List.exists_cons_of_length_eq_add_one hr
    obtain ⟨b, c, rfl⟩ := List.exists_cons_of_length_eq_add_one hc
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hr hc
    rw [dotL, Nat.add_eq, Nat.mul_eq, ih r c hr hc, Finset.sum_range_succ']
    simp [Nat.add_comm]

theorem wfM_iff {X : List (List ℕ)} :
    wfM X = true ↔ X.length = 14 ∧ ∀ r ∈ X, r.length = 14 := by
  simp [wfM]

theorem getD_of_wfM {X : List (List ℕ)} (h : wfM X = true) (i : ℕ) (hi : i < 14) :
    (X.getD i []).length = 14 := by
  rw [wfM_iff] at h
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact h.2 _ (List.getElem_mem _)

private theorem natCast_mod_five (n : ℕ) : ((n % 5 : ℕ) : ZMod 5) = (n : ZMod 5) :=
  ZMod.natCast_mod n 5

private theorem nat_mod_eq' (x y : ℕ) : Nat.mod x y = x % y := rfl

private theorem getD_map_lt {α β : Type*} (f : α → β) {l : List α} {n : ℕ} (d : β) (d' : α)
    (h : n < l.length) : (l.map f).getD n d = f (l.getD n d') := by
  rw [List.getD_eq_getElem (l.map f) d (by simpa using h), List.getElem_map,
    List.getD_eq_getElem l d' h]

theorem toV_mvL {X : List (List ℕ)} {v : List ℕ} (hX : wfM X = true) (hv : v.length = 14) :
    toV (mvL X v) = toM X *ᵥ toV v := by
  funext i
  have hlen : X.length = 14 := (wfM_iff.mp hX).1
  have hrow := getD_of_wfM hX i.val i.isLt
  have hi : i.val < X.length := by rw [hlen]; exact i.isLt
  simp only [toV, mvL, mulVec, dotProduct, toM, of_apply]
  rw [getD_map_lt _ 0 [] hi, nat_mod_eq', natCast_mod_five, dotL_eq_sum 14 _ _ hrow hv]
  push_cast
  exact (Fin.sum_univ_eq_sum_range
    (fun k => (((X.getD i.val []).getD k 0 : ℕ) : ZMod 5) * ((v.getD k 0 : ℕ) : ZMod 5)) 14).symm

theorem mulL_getD {X Y : List (List ℕ)} (hX : wfM X = true) {i j : ℕ} (hi : i < 14)
    (hj : j < 14) : ((mulL X Y).getD i []).getD j 0 =
      dotL (X.getD i []) (Y.map fun r => r.getD j 0) % 5 := by
  have hlen : X.length = 14 := (wfM_iff.mp hX).1
  have hcl : (colsL Y).length = 14 := by simp [colsL]
  unfold mulL
  rw [getD_map_lt _ [] [] (show i < X.length by omega),
    getD_map_lt _ 0 [] (show j < (colsL Y).length by omega), nat_mod_eq']
  unfold colsL
  rw [getD_map_lt _ [] 0 (show j < (List.range 14).length by simpa using hj),
    List.getD_eq_getElem (List.range 14) 0 (by simpa using hj), List.getElem_range]

theorem toM_mulL {X Y : List (List ℕ)} (hX : wfM X = true) (hY : wfM Y = true) :
    toM (mulL X Y) = toM X * toM Y := by
  ext i j
  have hlenY : Y.length = 14 := (wfM_iff.mp hY).1
  have hrow := getD_of_wfM hX i.val i.isLt
  simp only [toM, of_apply, mul_apply]
  rw [mulL_getD hX i.isLt j.isLt, natCast_mod_five, dotL_eq_sum 14 _ _ hrow (by simp [hlenY])]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (((X.getD i.val []).getD k 0 : ℕ) : ZMod 5) *
      ((((Y.map fun r => r.getD j.val 0).getD k 0) : ℕ) : ZMod 5)) 14]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getD_map_lt _ 0 [] (show k.val < Y.length by rw [hlenY]; exact k.isLt)]

theorem wfM_mulL {X Y : List (List ℕ)} (hX : wfM X = true) : wfM (mulL X Y) = true := by
  rw [wfM_iff] at hX ⊢
  refine ⟨by simp [mulL, hX.1], fun r hr => ?_⟩
  simp only [mulL, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp [colsL]

theorem toV_inj {v w : List ℕ} (hv : v.length = 14) (hw : w.length = 14)
    (hv5 : ∀ x ∈ v, x < 5) (hw5 : ∀ x ∈ w, x < 5) (h : toV v = toV w) : v = w := by
  apply List.ext_getElem (by rw [hv, hw])
  intro k hk1 hk2
  have := congrFun h ⟨k, by omega⟩
  simp only [toV] at this
  rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2] at this
  have h1 := hv5 _ (List.getElem_mem hk1)
  have h2 := hw5 _ (List.getElem_mem hk2)
  have := congrArg ZMod.val this
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

@[expose] def idL : List (List ℕ) :=
  (List.range 14).map fun i => (List.range 14).map fun j => if i = j then 1 else 0

theorem wfM_idL : wfM idL = true := by decide

theorem toM_idL : toM idL = 1 := by
  ext i j
  simp only [toM, idL, of_apply, one_apply]
  rw [getD_map_lt _ [] 0 (by simp), List.getD_eq_getElem (List.range 14) 0 (by simp),
    List.getElem_range, getD_map_lt _ 0 0 (by simp), List.getD_eq_getElem (List.range 14) 0
    (by simp), List.getElem_range]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (Fin.ext h')), ite_eq_right h]
    simp

@[expose] noncomputable def unitL (X Y : List (List ℕ)) (hX : wfM X = true) (hY : wfM Y = true)
    (h₁ : mulL X Y = idL) (h₂ : mulL Y X = idL) : GL (Fin 14) (ZMod 5) :=
  ⟨toM X, toM Y, by rw [← toM_mulL hX hY, h₁, toM_idL], by rw [← toM_mulL hY hX, h₂, toM_idL]⟩

@[expose] def letterL (X Xi : ℕ → List (List ℕ)) (l : ℕ × Bool) : List (List ℕ) :=
  cond l.2 (X l.1) (Xi l.1)

@[expose] def lwordL (X Xi : ℕ → List (List ℕ)) : List (ℕ × Bool) → List (List ℕ) →
    List (List ℕ)
  | [], acc => acc
  | l :: w, acc => lwordL X Xi w (mulL acc (letterL X Xi l))

theorem toM_lwordL {u : ℕ → GL (Fin 14) (ZMod 5)} {X Xi : ℕ → List (List ℕ)}
    (hX : ∀ i, wfM (X i) = true) (hXi : ∀ i, wfM (Xi i) = true)
    (hu : ∀ i, (u i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (X i))
    (hui : ∀ i, (((u i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (Xi i)) :
    ∀ (w : List (ℕ × Bool)) (acc : List (List ℕ)), wfM acc = true →
      toM acc * ((Bridge.wordProd u w : GL (Fin 14) (ZMod 5)) :
        Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (lwordL X Xi w acc) := by
  intro w
  induction w with
  | nil => intro acc _; simp [Bridge.wordProd, lwordL]
  | cons l w ih =>
    intro acc hacc
    have hl : wfM (letterL X Xi l) = true := by
      unfold letterL; cases l.2 <;> simp [hX, hXi]
    have hval : (((if l.2 then u l.1 else (u l.1)⁻¹ : GL (Fin 14) (ZMod 5))) :
        Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (letterL X Xi l) := by
      unfold letterL; cases l.2 <;> simp [hu, hui]
    have hw : Bridge.wordProd u (l :: w) =
        (if l.2 then u l.1 else (u l.1)⁻¹) * Bridge.wordProd u w := by
      simp [Bridge.wordProd]
    rw [hw, Units.val_mul, ← mul_assoc, hval, ← toM_mulL hacc hl, lwordL]
    exact ih _ (wfM_mulL hacc)

theorem wordProd_eq_one_of_lwordL {u : ℕ → GL (Fin 14) (ZMod 5)} {X Xi : ℕ → List (List ℕ)}
    (hX : ∀ i, wfM (X i) = true) (hXi : ∀ i, wfM (Xi i) = true)
    (hu : ∀ i, (u i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (X i))
    (hui : ∀ i, (((u i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (Xi i)) {w : List (ℕ × Bool)} (h : lwordL X Xi w idL = idL) :
    Bridge.wordProd u w = 1 := by
  apply Units.ext
  have := toM_lwordL hX hXi hu hui w idL wfM_idL
  rw [toM_idL, one_mul, h, toM_idL] at this
  rw [this, Units.val_one]

theorem val_wordProd_of_lwordL {u : ℕ → GL (Fin 14) (ZMod 5)} {X Xi : ℕ → List (List ℕ)}
    (hX : ∀ i, wfM (X i) = true) (hXi : ∀ i, wfM (Xi i) = true)
    (hu : ∀ i, (u i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (X i))
    (hui : ∀ i, (((u i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (Xi i)) {w : List (ℕ × Bool)} {Z : List (List ℕ)} (h : lwordL X Xi w idL = Z) :
    ((Bridge.wordProd u w : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM Z := by
  have := toM_lwordL hX hXi hu hui w idL wfM_idL
  rw [toM_idL, one_mul, h] at this
  exact this

@[expose] def orbitOK (Xs : List (List (List ℕ))) (O : List (List ℕ)) (par lab : List ℕ) : Bool :=
  !O.isEmpty && O.Nodup && O.all (fun v => v.length == 14 && v.all fun x => x < 5) &&
    Xs.all wfM && Xs.all (fun X => O.all fun v => mvL X v ∈ O) &&
    (List.range O.length).all fun i => i == 0 ||
      (par.getD i 0 < i && lab.getD i 0 < Xs.length &&
        mvL (Xs.getD (lab.getD i 0) []) (O.getD (par.getD i 0) []) == O.getD i [])

theorem smul_mem_of_closure {s : Set (GL (Fin 14) (ZMod 5))} {S : Set (Fin 14 → ZMod 5)}
    (hs : ∀ g ∈ s, ∀ x ∈ S, g • x ∈ S) : ∀ g ∈ Subgroup.closure s, ∀ x ∈ S, g • x ∈ S := by
  intro g hg
  have hg' : g ∈ Submonoid.closure s := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]; exact hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem g hg => exact hs g hg
  | one => intro x hx; rwa [one_smul]
  | mul g g' _ _ ihg ihg' =>
    intro x hx
    rw [mul_smul]
    exact ihg _ (ihg' x hx)

theorem length_dvd_card_of_orbitOK {Xs : List (List (List ℕ))} {O : List (List ℕ)}
    {par lab : List ℕ} (us : ℕ → GL (Fin 14) (ZMod 5))
    (hus : ∀ j < Xs.length, (us j : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (Xs.getD j []))
    (h : orbitOK Xs O par lab = true) :
    O.length ∣ Nat.card (Subgroup.closure {g | ∃ j < Xs.length, us j = g}) := by
  simp only [orbitOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hne, hnd⟩, hO⟩, hXs⟩, hcl⟩, htree⟩ := h
  have hlen : ∀ v ∈ O, v.length = 14 := fun v hv => (hO v hv).1
  have h5 : ∀ v ∈ O, ∀ x ∈ v, x < 5 := fun v hv => (hO v hv).2
  have hact : ∀ j < Xs.length, ∀ v ∈ O, us j • toV v = toV (mvL (Xs.getD j []) v) := by
    intro j hj v hv
    have hX : wfM (Xs.getD j []) = true := hXs _ (by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
    rw [toV_mvL hX (hlen v hv), ← hus j hj]
    rfl
  have hclosed := smul_mem_of_closure (s := {g | ∃ j < Xs.length, us j = g})
    (S := {x | ∃ v ∈ O, toV v = x}) (by
      rintro _ ⟨j, hj, rfl⟩ _ ⟨v, hv, rfl⟩
      refine ⟨mvL (Xs.getD j []) v, ?_, (hact j hj v hv).symm⟩
      exact hcl _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj) v hv)
  have h0 : 0 < O.length := List.length_pos_iff.mpr hne
  have hx0 : O.getD 0 [] ∈ O := by
    rw [List.getD_eq_getElem _ _ h0]; exact List.getElem_mem h0
  have hreach : ∀ i < O.length, ∃ k ∈ Subgroup.closure {g | ∃ j < Xs.length, us j = g},
      k • toV (O.getD 0 []) = toV (O.getD i []) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
      · obtain ⟨⟨hp, hl⟩, he⟩ := (htree i hi).resolve_left (by omega)
        obtain ⟨k, hk, hkx⟩ := ih _ hp (by omega)
        have hpv : O.getD (par.getD i 0) [] ∈ O := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
        refine ⟨us (lab.getD i 0) * k, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hl, rfl⟩)
          hk, ?_⟩
        rw [mul_smul, hkx, hact _ hl _ hpv, he]
  set K := Subgroup.closure {g | ∃ j < Xs.length, us j = g}
  set x0 := toV (O.getD 0 [])
  have horbit : MulAction.orbit K x0 = {x | ∃ v ∈ O, toV v = x} := by
    ext x
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact hclosed k hk x0 ⟨_, hx0, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      obtain ⟨k, hk, hkx⟩ := hreach i hi
      refine ⟨⟨k, hk⟩, ?_⟩
      rw [List.getD_eq_getElem _ _ hi] at hkx
      exact hkx
  have hS : {x | ∃ v ∈ O, toV v = x} = ↑(O.map toV).toFinset := by
    ext x
    simp
  have hnd' : (O.map toV).Nodup := hnd.map_on fun v hv w hw hvw =>
    toV_inj (hlen v hv) (hlen w hw) (h5 v hv) (h5 w hw) hvw
  have hcard : (MulAction.orbit K x0).ncard = O.length := by
    rw [horbit, hS, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', List.length_map]
  rw [← hcard, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

end CFSG.Sporadic.Bridge.J2
