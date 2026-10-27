module

public import CFSG.Sporadic.Schreier.Co1SplitCheck
public import CFSG.Sporadic.Schreier.Co1EigenPlanes

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (rowsMatrix toVecD toVecD_injective rowsMatrix_mulVec)
open ElemThree Matrix

abbrev Mat24 : Type := Matrix (Fin 24) (Fin 24) (ZMod 2)

@[expose] def MS (g : Mat24) (p : Fin 12 → Fin 12) (a s : Fin 12 → ZMod 3) : Prop :=
  ∀ j (e : ZMod 3), g *ᵥ (zM ^ e.val *ᵥ q j) = zM ^ (a j + s j * e).val *ᵥ q (p j)

theorem MS.one : MS 1 id 0 1 := by
  intro j e
  rw [one_mulVec, Pi.zero_apply, Pi.one_apply, zero_add, one_mul]
  rfl

theorem MS.mul {g h : Mat24} {p p' : Fin 12 → Fin 12} {a s a' s' : Fin 12 → ZMod 3}
    (hg : MS g p a s) (hh : MS h p' a' s') :
    MS (g * h) (p ∘ p') (fun j => a (p' j) + s (p' j) * a' j) (fun j => s (p' j) * s' j) := by
  intro j e
  rw [← mulVec_mulVec, hh j e, hg (p' j) (a' j + s' j * e)]
  have : a (p' j) + s (p' j) * (a' j + s' j * e) =
      a (p' j) + s (p' j) * a' j + s (p' j) * s' j * e := by ring
  rw [this]
  rfl

theorem zM_pow_q
    (e : ℕ) (j : Fin 12) (he : e < 3) :
    zM ^ e *ᵥ q j = toVecD 24 (Native.zq e j.val) := by
  rw [Native.zq_eq he j.isLt, toVecD_zPow, q_eq]

theorem zq_inj
    {e f : ZMod 3} {j k : Fin 12} (h : zM ^ e.val *ᵥ q j = zM ^ f.val *ᵥ q k) :
    j = k ∧ e = f := by
  have hc := zq_check
  simp only [Native.zqCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  have h1 := hc j.val j.isLt e.val (ZMod.val_lt e)
  have h2 := hc k.val k.isLt f.val (ZMod.val_lt f)
  rw [zM_pow_q _ _ (ZMod.val_lt e), zM_pow_q _ _ (ZMod.val_lt f)] at h
  have h3 : Native.zq e.val j.val = Native.zq f.val k.val := toVecD_injective h1.1 h2.1 h
  have h4 := h1.2 k.val k.isLt f.val (ZMod.val_lt f)
  rw [h3, beq_self_eq_true, Bool.true_beq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h4
  exact ⟨Fin.ext h4.1, ZMod.val_injective _ h4.2⟩

theorem MS.unique
    {g : Mat24} {p p' : Fin 12 → Fin 12} {a s a' s' : Fin 12 → ZMod 3}
    (h : MS g p a s) (h' : MS g p' a' s') : p = p' ∧ a = a' ∧ s = s' := by
  have key : ∀ j, p j = p' j ∧ a j = a' j := by
    intro j
    have e0 := (h j 0).symm.trans (h' j 0)
    rw [mul_zero, add_zero, mul_zero, add_zero] at e0
    exact zq_inj e0
  refine ⟨funext fun j => (key j).1, funext fun j => (key j).2, funext fun j => ?_⟩
  have e1 := (h j 1).symm.trans (h' j 1)
  rw [(key j).1] at e1
  have := (zq_inj e1).2
  rw [mul_one, mul_one, (key j).2] at this
  exact add_left_cancel this

theorem eq_of_zq
    {M N : Mat24}
    (h : ∀ j (e : ZMod 3), M *ᵥ (zM ^ e.val *ᵥ q j) = N *ᵥ (zM ^ e.val *ᵥ q j)) : M = N := by
  have hv : ∀ v, M *ᵥ v = N *ᵥ v := by
    intro v
    have hv : v ∈ Submodule.span (ZMod 2)
        (Set.range fun p : Fin 12 × Fin 2 => (zM ^ p.2.val) *ᵥ q p.1) := by
      rw [span_q]
      trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨j, e⟩, rfl⟩ := hx
      have := h j (e.val : ZMod 3)
      rwa [ZMod.val_cast_of_lt (by omega : e.val < 3)] at this
    | zero => rw [mulVec_zero, mulVec_zero]
    | add x y _ _ hx hy => rw [mulVec_add, mulVec_add, hx, hy]
    | smul c x _ hx => rw [mulVec_smul, mulVec_smul, hx]
  exact Matrix.ext_of_mulVec_single fun i => hv _

theorem MS.ext
    {g h : Mat24} {p : Fin 12 → Fin 12} {a s : Fin 12 → ZMod 3} (hg : MS g p a s)
    (hh : MS h p a s) : g = h :=
  eq_of_zq fun j e => (hg j e).trans (hh j e).symm

@[expose] def IsMS (g : Mat24) : Prop := ∃ p a s, (∀ j, s j ≠ 0) ∧ MS g p a s

theorem IsMS.one : IsMS 1 := ⟨id, 0, 1, fun _ => one_ne_zero, MS.one⟩

theorem IsMS.mul {g h : Mat24} (hg : IsMS g) (hh : IsMS h) : IsMS (g * h) := by
  obtain ⟨p, a, s, hs, hg⟩ := hg
  obtain ⟨p', a', s', hs', hh⟩ := hh
  exact ⟨_, _, _, fun j => mul_ne_zero (hs _) (hs' j), hg.mul hh⟩

open Classical in
@[expose] noncomputable def msData (g : Mat24) :
    (Fin 12 → Fin 12) × (Fin 12 → ZMod 3) × (Fin 12 → ZMod 3) :=
  if h : IsMS g then (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (id, 0, 1)

theorem msData_spec {g : Mat24} (h : IsMS g) :
    (∀ j, (msData g).2.2 j ≠ 0) ∧ MS g (msData g).1 (msData g).2.1 (msData g).2.2 := by
  unfold msData
  simp only [h, ↓reduceDIte]
  exact h.choose_spec.choose_spec.choose_spec

theorem msData_eq
    {g : Mat24} {p : Fin 12 → Fin 12} {a s : Fin 12 → ZMod 3}
    (hs : ∀ j, s j ≠ 0) (h : MS g p a s) : msData g = (p, a, s) := by
  have hg : IsMS g := ⟨p, a, s, hs, h⟩
  obtain ⟨h1, h2, h3⟩ := (msData_spec hg).2.unique h
  rw [← h1, ← h2, ← h3]

theorem val_add_mul (a s : ℕ) (e : ZMod 3) :
    (((a : ZMod 3) + (s : ZMod 3) * e).val) = (a + s * e.val) % 3 := by
  rw [← ZMod.val_natCast]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem MS.of_msOK
    {X : Native.Rows} (h : Native.msOK X = true) :
    MS (rowsMatrix 24 X) (fun j => Fin.ofNat 12 (Native.msSearch X j.val).1)
      (fun j => ((Native.msSearch X j.val).2.1 : ZMod 3)) (fun j => (Native.msSgn X j.val : ZMod 3))
      ∧ ∀ j : Fin 12, (Native.msSgn X j.val : ZMod 3) ≠ 0 := by
  simp only [Native.msOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  refine ⟨fun j e => ?_, fun j => ?_⟩
  · obtain ⟨⟨⟨hk, ha⟩, _⟩, he⟩ := h j.val j.isLt
    have hke : (Fin.ofNat 12 (Native.msSearch X j.val).1).val = (Native.msSearch X j.val).1 :=
      Nat.mod_eq_of_lt hk
    rw [zM_pow_q _ _ (ZMod.val_lt e), rowsMatrix_mulVec, ← Native.act, he e.val (ZMod.val_lt e),
      val_add_mul, zM_pow_q _ _ (Nat.mod_lt _ (by norm_num)), hke]
    rfl
  · obtain ⟨⟨⟨_, _⟩, hs⟩, _⟩ := h j.val j.isLt
    have hlt : Native.msSgn X j.val < 3 := Nat.mod_lt _ (by norm_num)
    have hne : Native.msSgn X j.val ≠ 0 := hs
    generalize Native.msSgn X j.val = m at hlt hne ⊢
    interval_cases m
    · exact absurd rfl hne
    · decide
    · decide

theorem IsMS.of_msOK
    {X : Native.Rows} (h : Native.msOK X = true) : IsMS (rowsMatrix 24 X) :=
  ⟨_, _, _, (MS.of_msOK h).2, (MS.of_msOK h).1⟩

theorem split_parts :
    Native.mul Native.aR (Native.inv Native.aR) = Native.one ∧
    Native.mul Native.bR (Native.inv Native.bR) = Native.one ∧ Native.strongDag.2.2 = true ∧
    (∀ i < 3, Native.gRows i = (Data.liftRows.getD i []).toArray) ∧
    ∀ X ∈ Native.splitGens, (Native.mul X (Native.inv X) = Native.one ∧
      Native.msOK X = true) ∧ Native.msOK (Native.inv X) = true := by
  have h := split_check
  simp only [Native.splitCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem MRep.val_eq {X : Native.Rows} {x : GL24} (h : MRep X x) :
    ((x : GL24) : Mat24) = rowsMatrix 24 X :=
  h.symm

private theorem foldl_step_flag' (derivs : List (List ℤ))
    (st : List Native.Rows × List Native.Rows × Bool) :
    (derivs.foldl Native.step st).2.2 = true → st.2.2 = true := by
  induction derivs generalizing st with
  | nil => exact id
  | cons w ws ih =>
    intro h
    have := ih _ h
    simp only [Native.step, Bool.and_eq_true] at this
    exact this.1

private theorem foldl_step_rep' (derivs : List (List ℤ))
    (st : List Native.Rows × List Native.Rows × Bool) (gs : List GL24)
    (hst : ListRep st.1 st.2.1 gs) (hflag : (derivs.foldl Native.step st).2.2 = true) :
    ListRep (derivs.foldl Native.step st).1 (derivs.foldl Native.step st).2.1
      (derivs.foldl (fun acc w => acc ++ [wordG acc w]) gs) := by
  induction derivs generalizing st gs with
  | nil => exact hst
  | cons w ws ih =>
    refine ih (Native.step st w) (gs ++ [wordG gs w]) ?_ hflag
    have hc := foldl_step_flag' ws _ hflag
    simp only [Native.step, Bool.and_eq_true, beq_iff_eq] at hc
    have hm := MRep.word hst w
    refine ⟨List.rel_append hst.1 (List.Forall₂.cons hm List.Forall₂.nil), ?_⟩
    exact List.rel_append hst.2 (List.Forall₂.cons (hm.inv hc.2) List.Forall₂.nil)

theorem dag_listRep {base : List Native.Rows} {baseG : List GL24}
    (hb : List.Forall₂ MRep base baseG) (derivs : List (List ℤ))
    (hflag : (Native.dag base derivs).2.2 = true) :
    ListRep (Native.dag base derivs).1 (Native.dag base derivs).2.1 (dagG baseG derivs) := by
  have h0 := foldl_step_flag' derivs _ hflag
  simp only [List.all_eq_true, beq_iff_eq] at h0
  have hinv : List.Forall₂ (fun I g => MRep I g⁻¹) (base.map Native.inv) baseG := by
    clear hflag
    induction hb with
    | nil => exact List.Forall₂.nil
    | @cons a b l₁ l₂ hab _ ih =>
      refine List.Forall₂.cons (hab.inv (h0 a (by simp))) (ih fun x hx => h0 x (by simp [hx]))
  exact foldl_step_rep' derivs _ baseG ⟨hb, hinv⟩ hflag

theorem ab_listRep :
    ListRep [Native.aR, Native.bR] [Native.inv Native.aR, Native.inv Native.bR]
    [A₁, A₂] :=
  ⟨List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil),
    List.Forall₂.cons (rep_A₁.inv split_parts.1)
      (List.Forall₂.cons (rep_A₂.inv split_parts.2.1) List.Forall₂.nil)⟩

theorem hAmb_rep :
    List.Forall₂ MRep Native.hAmbRows hAmb := by
  unfold Native.hAmbRows hAmb
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun w _ => MRep.word ab_listRep (Native.decWord w)

theorem strong_listRep :
    ListRep Native.strongDag.1 Native.strongDag.2.1 strong :=
  dag_listRep hAmb_rep _ split_parts.2.2.1

theorem MRep.foldl_words {rs is : List Native.Rows} {gs : List GL24} (h : ListRep rs is gs)
    (ws : List (List ℕ)) : ∀ (X : Native.Rows) (x : GL24), MRep X x →
      MRep (ws.foldl (fun X w => Native.mul X (Native.word rs is (Native.decWord w))) X)
        (ws.foldl (fun x w => x * wordG gs (Native.decWord w)) x) := by
  induction ws with
  | nil => exact fun _ _ h => h
  | cons w ws ih =>
    intro X x hX
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (hX.mul (MRep.word h _))

theorem g_rep
    (i : Fin 3) : MRep (Native.gRows i.val) (g i) :=
  MRep.foldl_words strong_listRep _ _ _ (MRep.word ab_listRep _)

theorem g_inv_rep
    (i : Fin 3) : MRep (Native.inv (Native.gRows i.val)) (g i)⁻¹ := by
  refine (g_rep i).inv (split_parts.2.2.2.2 _ ?_).1.1
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)

theorem a_inv_rep
    (i : Fin 6) : MRep (Native.inv (Native.aRows i.val)) (a i)⁻¹ := by
  refine (a_rep i).inv (split_parts.2.2.2.2 _ ?_).1.1
  exact List.mem_append_left _ (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)

theorem g_eq_lift (i : Fin 3) :
    ((g i : GL24) : Mat24) = rowsMatrix 24 (Data.liftRows.getD i.val []).toArray := by
  rw [(g_rep i).val_eq, split_parts.2.2.2.1 i.val i.isLt]

theorem isMS_a
    (i : Fin 6) : IsMS ((a i : GL24) : Mat24) ∧ IsMS (((a i)⁻¹ : GL24) : Mat24) := by
  have h := split_parts.2.2.2.2 (Native.aRows i.val)
    (List.mem_append_left _ (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩))
  refine ⟨?_, ?_⟩
  · rw [(a_rep i).val_eq]; exact IsMS.of_msOK h.1.2
  · rw [(a_inv_rep i).val_eq]; exact IsMS.of_msOK h.2

theorem isMS_g
    (i : Fin 3) : IsMS ((g i : GL24) : Mat24) ∧ IsMS (((g i)⁻¹ : GL24) : Mat24) := by
  have h := split_parts.2.2.2.2 (Native.gRows i.val)
    (List.mem_append_right _ (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩))
  refine ⟨?_, ?_⟩
  · rw [(g_rep i).val_eq]; exact IsMS.of_msOK h.1.2
  · rw [(g_inv_rep i).val_eq]; exact IsMS.of_msOK h.2

theorem closure_induction_inv {G : Type*} [Group G] {S : Set G} {P : G → Prop} (h1 : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (hS : ∀ x ∈ S, P x ∧ P x⁻¹) :
    ∀ x ∈ Subgroup.closure S, P x := by
  intro x hx
  replace hx : x ∈ Submonoid.closure (S ∪ S⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hx
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact (hS y hy).1
    · have := (hS _ (Set.mem_inv.mp hy)).2
      rwa [inv_inv] at this
  | one => exact h1
  | mul y z _ _ hy hz => exact hmul y z hy hz

theorem E_isMS :
    ∀ x ∈ E, IsMS ((x : GL24) : Mat24) := by
  apply closure_induction_inv (P := fun x : GL24 => IsMS (x : Mat24))
  · rw [Units.val_one]; exact IsMS.one
  · intro x y hx hy
    rw [Units.val_mul]
    exact hx.mul hy
  · rintro _ ⟨i, rfl⟩
    exact isMS_a i

theorem g_two : g 2 = r := rfl

theorem A_isMS :
    ∀ x ∈ A, IsMS ((x : GL24) : Mat24) := by
  apply closure_induction_inv (P := fun x : GL24 => IsMS (x : Mat24))
  · rw [Units.val_one]; exact IsMS.one
  · intro x y hx hy
    rw [Units.val_mul]
    exact hx.mul hy
  · rintro x (hx | hx)
    · exact ⟨E_isMS x hx, E_isMS _ (E.inv_mem hx)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      exacts [isMS_g 0, isMS_g 1, isMS_g 2]

end CFSG.Sporadic.Co1Schreier
