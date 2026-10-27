module

public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

abbrev GL24 : Type := GL (Fin 24) (ZMod 2)

abbrev Vec24 : Type := Fin 24 → ZMod 2

@[expose] def MRep (R : Native.Rows) (g : GL24) : Prop :=
  rowsMatrix 24 R = (g : Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem MRep.one : MRep Native.one 1 := rowsMatrix_idRows 24

theorem MRep.mul {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h) :
    MRep (Native.mul X Y) (g * h) := by
  unfold MRep Native.mul
  rw [rowsMatrix_mulRows, hX, hY, Units.val_mul]

theorem MRep.eq {X : Native.Rows} {g h : GL24} (hg : MRep X g) (hh : MRep X h) : g = h :=
  Units.ext (hg.symm.trans hh)

theorem MRep.inv {X Y : Native.Rows} {g : GL24} (hX : MRep X g)
    (h : Native.mul X Y = Native.one) : MRep Y g⁻¹ := by
  have h1 : (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) * rowsMatrix 24 Y = 1 := by
    rw [← hX, ← rowsMatrix_mulRows]
    exact (congrArg (rowsMatrix 24) h).trans MRep.one
  unfold MRep
  calc rowsMatrix 24 Y = ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
        ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) * rowsMatrix 24 Y) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by rw [h1, mul_one]

theorem MRep.pow {X : Native.Rows} {g : GL24} (hX : MRep X g) (e : ℕ) :
    MRep (Native.pow X e) (g ^ e) := by
  induction e with
  | zero => exact MRep.one
  | succ e ih => rw [pow_succ]; exact ih.mul hX

theorem MRep.mulVec {X : Native.Rows} {g : GL24} (hX : MRep X g) (v : ℕ) :
    (g : Matrix (Fin 24) (Fin 24) (ZMod 2)).mulVec (toVecD 24 v) = toVecD 24 (Native.act X v) := by
  rw [← hX]
  exact rowsMatrix_mulVec 24 X v

@[expose] def letterG (gs : List GL24) (j : ℤ) : GL24 :=
  if 0 < j then gs.getD (j.toNat - 1) 1 else (gs.getD ((-j).toNat - 1) 1)⁻¹

@[expose] def wordG (gs : List GL24) (w : List ℤ) : GL24 := w.foldl (fun x j => x * letterG gs j) 1

@[expose] def ListRep (rs is : List Native.Rows) (gs : List GL24) : Prop :=
  List.Forall₂ MRep rs gs ∧ List.Forall₂ (fun I g => MRep I g⁻¹) is gs

theorem getD_rep {P : Native.Rows → GL24 → Prop} {rs : List Native.Rows} {gs : List GL24}
    (h : List.Forall₂ P rs gs) (hd : P Native.one 1) (k : ℕ) :
    P (rs.getD k Native.one) (gs.getD k 1) := by
  induction h generalizing k with
  | nil => simpa using hd
  | cons hab _ ih =>
    cases k with
    | zero => simpa using hab
    | succ k => simpa using ih k

theorem MRep.letter {rs is : List Native.Rows} {gs : List GL24} (h : ListRep rs is gs) (j : ℤ) :
    MRep (Native.letter rs is j) (letterG gs j) := by
  unfold Native.letter letterG
  split_ifs
  · exact getD_rep h.1 MRep.one _
  · have := getD_rep (P := fun I g => MRep I g⁻¹) h.2 (by simpa using MRep.one) ((-j).toNat - 1)
    exact this

theorem MRep.foldl {rs is : List Native.Rows} {gs : List GL24} (h : ListRep rs is gs)
    (w : List ℤ) : ∀ (acc : Native.Rows) (g : GL24), MRep acc g →
      MRep (w.foldl (fun acc j => Native.mul acc (Native.letter rs is j)) acc)
        (w.foldl (fun x j => x * letterG gs j) g) := by
  induction w with
  | nil => exact fun _ _ h => h
  | cons j w ih =>
    intro acc g hacc
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (Native.mul acc (Native.letter rs is j)) (g * letterG gs j)
      (hacc.mul (MRep.letter h j))

theorem MRep.word {rs is : List Native.Rows} {gs : List GL24} (h : ListRep rs is gs)
    (w : List ℤ) : MRep (Native.word rs is w) (wordG gs w) :=
  MRep.foldl h w _ _ MRep.one

theorem getD_mem_of_forall {H : Subgroup GL24} {gs : List GL24} (h : ∀ g ∈ gs, g ∈ H) (k : ℕ) :
    gs.getD k 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : gs[k]? with
  | none => exact H.one_mem
  | some g => exact h g (List.mem_of_getElem? hk)

theorem letterG_mem {H : Subgroup GL24} {gs : List GL24} (h : ∀ g ∈ gs, g ∈ H) (j : ℤ) :
    letterG gs j ∈ H := by
  unfold letterG
  split_ifs
  · exact getD_mem_of_forall h _
  · exact H.inv_mem (getD_mem_of_forall h _)

theorem wordG_mem {H : Subgroup GL24} {gs : List GL24} (h : ∀ g ∈ gs, g ∈ H) (w : List ℤ) :
    wordG gs w ∈ H := by
  unfold wordG
  suffices ∀ x ∈ H, w.foldl (fun x j => x * letterG gs j) x ∈ H from this 1 H.one_mem
  induction w with
  | nil => exact fun x hx => hx
  | cons j w ih =>
    intro x hx
    rw [List.foldl_cons]
    exact ih (x * letterG gs j) (H.mul_mem hx (letterG_mem h j))

@[expose] def dagG (base : List GL24) (derivs : List (List ℤ)) : List GL24 :=
  derivs.foldl (fun acc w => acc ++ [wordG acc w]) base

private theorem foldl_step_flag (derivs : List (List ℤ))
    (st : List Native.Rows × List Native.Rows × Bool) :
    (derivs.foldl Native.step st).2.2 = true → st.2.2 = true := by
  induction derivs generalizing st with
  | nil => exact id
  | cons w ws ih =>
    intro h
    have := ih _ h
    simp only [Native.step, Bool.and_eq_true] at this
    exact this.1

private theorem foldl_step_rep (derivs : List (List ℤ))
    (st : List Native.Rows × List Native.Rows × Bool) (gs : List GL24)
    (hst : ListRep st.1 st.2.1 gs) (hflag : (derivs.foldl Native.step st).2.2 = true) :
    ListRep (derivs.foldl Native.step st).1 (derivs.foldl Native.step st).2.1
      (derivs.foldl (fun acc w => acc ++ [wordG acc w]) gs) := by
  induction derivs generalizing st gs with
  | nil => exact hst
  | cons w ws ih =>
    refine ih (Native.step st w) (gs ++ [wordG gs w]) ?_ hflag
    have hc := foldl_step_flag ws _ hflag
    simp only [Native.step, Bool.and_eq_true, beq_iff_eq] at hc
    have hm := MRep.word hst w
    refine ⟨List.rel_append hst.1 (List.Forall₂.cons hm List.Forall₂.nil), ?_⟩
    exact List.rel_append hst.2 (List.Forall₂.cons (hm.inv hc.2) List.Forall₂.nil)

theorem dagG_mem {H : Subgroup GL24} {base : List GL24} (h : ∀ g ∈ base, g ∈ H)
    (derivs : List (List ℤ)) : ∀ g ∈ dagG base derivs, g ∈ H := by
  unfold dagG
  induction derivs generalizing base with
  | nil => exact h
  | cons w ws ih =>
    rw [List.foldl_cons]
    apply ih
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h g hg
    · rw [List.mem_singleton] at hg
      rw [hg]
      exact wordG_mem h w

theorem dag_rep {base : List Native.Rows} {baseG : List GL24} (hb : List.Forall₂ MRep base baseG)
    (derivs : List (List ℤ)) (hflag : (Native.dag base derivs).2.2 = true) :
    List.Forall₂ MRep (Native.dag base derivs).1 (dagG baseG derivs) := by
  have h0 := foldl_step_flag derivs _ hflag
  simp only [List.all_eq_true, beq_iff_eq] at h0
  have hinv : List.Forall₂ (fun I g => MRep I g⁻¹) (base.map Native.inv) baseG := by
    clear hflag
    induction hb with
    | nil => exact List.Forall₂.nil
    | @cons a b l₁ l₂ hab _ ih =>
      refine List.Forall₂.cons (hab.inv (h0 a (by simp))) (ih fun x hx => h0 x (by simp [hx]))
  exact (foldl_step_rep derivs _ baseG ⟨hb, hinv⟩ hflag).1

end CFSG.Sporadic.Co1Schreier
