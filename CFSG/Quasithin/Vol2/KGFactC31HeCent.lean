module

public import CFSG.Quasithin.Vol2.KGFactC31HeRef
public import CFSG.Quasithin.Vol2.KGFactC31HeBase

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native _root_.Certificates

@[expose] noncomputable def vOf (W : List (List ℤ)) (k : ℕ) (i : Fin k) : Equiv.Perm (Fin 8330) :=
  elt (W.getD i [])

theorem ofFn_vOf {W : List (List ℤ)} {k : ℕ} (hk : W.length = k) :
    List.ofFn (vOf W k) = W.map elt := by
  subst hk
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_ofFn, List.getElem_map]
  simp only [vOf]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

theorem forall₂_vOf {W : List (List ℤ)} {k : ℕ}
    (hk : W.length = k) (hW : W.all (lettersOK 2) = true) :
    List.Forall₂ (Rep 8330) (W.map wA) (List.ofFn (vOf W k)) := by
  rw [ofFn_vOf hk, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun w hw =>
    rep_wA (lettersOK_mono (by norm_num) (List.all_eq_true.1 hW w hw))

theorem vOf_mem {W : List (List ℤ)} {k : ℕ}
    (hW : W.all (lettersOK 2) = true) (i : Fin k) : vOf W k i ∈ heP := by
  unfold vOf
  rcases lt_or_ge (i : ℕ) W.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact elt_mem_heP (List.all_eq_true.1 hW _ (List.getElem_mem hi))
  · rw [List.getD_eq_default _ _ hi]
    exact elt_mem_heP rfl

theorem letters_eW : eW.all (lettersOK 2) = true := by
  have h := c_letters
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.1.1

theorem letters_qW : qW.all (lettersOK 2) = true := by
  have h := c_letters
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.1.2

theorem len_w5W : w5W.length = 4 := by
  rw [c_w5, List.length_take, c_eLen]
  rfl

theorem len_w7W : w7W.length = 3 := by
  rw [c_w7, List.length_take, c_qLen]
  rfl

@[expose] noncomputable def vE : Fin 6 → Equiv.Perm (Fin 8330) := vOf eW 6

@[expose] noncomputable def vQ : Fin 4 → Equiv.Perm (Fin 8330) := vOf qW 4

@[expose] noncomputable def vW5 : Fin 4 → Equiv.Perm (Fin 8330) := vOf w5W 4

@[expose] noncomputable def vW7 : Fin 3 → Equiv.Perm (Fin 8330) := vOf w7W 3

theorem basis_E : EBasis vE := c_basisE

theorem basis_Q : EBasis vQ := c_basisQ

theorem heE_eq : heE = eSub basis_E := (eSub_eq_closure basis_E).symm

theorem heQ_eq : heQ = eSub basis_Q := (eSub_eq_closure basis_Q).symm

theorem vW5_eq (i : Fin 4) : vW5 i = vE ⟨i, by omega⟩ := by
  have h : w5W.getD i [] = eW.getD i [] := by
    rw [c_w5, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left i.2]
  change elt (w5W.getD i []) = elt (eW.getD i [])
  rw [h]

theorem vW7_eq (i : Fin 3) : vW7 i = vQ ⟨i, by omega⟩ := by
  have h : w7W.getD i [] = qW.getD i [] := by
    rw [c_w7, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left i.2]
  change elt (w7W.getD i []) = elt (qW.getD i [])
  rw [h]

theorem mem_E_of_cent {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hxc : ∀ i, x * vW5 i = vW5 i * x) : x ∈ eSub basis_E := by
  rw [← heE_eq]
  refine c_centE hx fun i => ?_
  have h := hxc i
  rw [vW5_eq] at h
  exact h

theorem mem_Q_of_cent {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hxc : ∀ i, x * vW7 i = vW7 i * x) : x ∈ eSub basis_Q := by
  rw [← heQ_eq]
  refine c_centQ hx fun i => ?_
  have h := hxc i
  rw [vW7_eq] at h
  exact h

end CFSG.Quasithin.KGC31.He

end
