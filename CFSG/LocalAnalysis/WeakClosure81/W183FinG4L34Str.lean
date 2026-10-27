module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Chk
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.GH74.KGroups.Generic
import CFSG.CGT.Stroth77.Section42Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Quasithin CFSG.Open
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.GH74.KGroups
open CFSG.CGT.Stroth77.Stroth42Core

@[expose] def invP (i : ℕ) : Equiv.Perm (Fin 42) := wordPerm (c1W.getD (invI.getD i 0) [])

@[expose] def span3 (x y z : Equiv.Perm (Fin 42)) : Set (Equiv.Perm (Fin 42)) :=
  {1, x, y, z, x * y, x * z, y * z, x * y * z}

@[expose] def e16Set (m : ℕ) : Set (Equiv.Perm (Fin 42)) :=
  {x | ∃ i ∈ e16Idx.getD m [], wordPerm (c1W.getD i []) = x}

@[expose] def e8Set (m : ℕ) : Set (Equiv.Perm (Fin 42)) :=
  {x | ∃ i ∈ e8Idx.getD m [], wordPerm (c1W.getD i []) = x}

@[expose] def w183finL34InvCover : Bool :=
  (List.range 64).all fun k =>
    !(eqN (compN (c1N.getD k 0) (c1N.getD k 0)) idN) ||
      decide (k ∈ e16Idx.getD 0 [] ∨ k ∈ e16Idx.getD 1 [])

private theorem w183finL34_invCover_eq : w183finL34InvCover = true := by decide +kernel

private theorem w183finL34_c1N_getD {k : ℕ} (hk : k < 64) :
    c1N.getD k 0 = wN (c1W.getD k []) := by
  have hkN : k < (c1W.map wN).length := by rw [List.length_map, c1W_length]; exact hk
  rw [c1N, List.getD_eq_getElem (l := c1W.map wN) (d := 0) (n := k) hkN, List.getElem_map,
    List.getD_eq_getElem (l := c1W) (d := ([] : List ℕ)) (n := k)
      (by rw [c1W_length]; exact hk)]

private theorem w183finL34_c1W_getD {k : ℕ} (hk : k < 64) :
    c1W.getD k [] = c1W[k]'(by rw [c1W_length]; exact hk) :=
  List.getD_eq_getElem (l := c1W) (d := ([] : List ℕ)) (n := k)
    (by rw [c1W_length]; exact hk)

private theorem w183finL34_mem_e16Set_or
    {x : Equiv.Perm (Fin 42)} (hxC : x ∈ C₁) (hx2 : x * x = 1) :
    x ∈ e16Set 0 ∨ x ∈ e16Set 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_c1 hxC
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
  have hk64 : k < 64 := by rw [c1W_length] at hk; exact hk
  have hc1Nk : c1N.getD k 0 = wN w := by
    rw [w183finL34_c1N_getD hk64, w183finL34_c1W_getD hk64, hkw]
  have hsq : eqN (compN (wN w) (wN w)) idN = true :=
    (RepN.eq_iff ((repN_wN w).comp (repN_wN w)) RepN.one).2 hx2
  have hck := List.all_eq_true.1 w183finL34_invCover_eq k (List.mem_range.2 hk64)
  rw [hc1Nk, hsq] at hck
  simp only [Bool.not_true, Bool.false_or] at hck
  have hmem : k ∈ e16Idx.getD 0 [] ∨ k ∈ e16Idx.getD 1 [] := of_decide_eq_true hck
  have hword : c1W.getD k [] = w := by
    rw [w183finL34_c1W_getD hk64, hkw]
  rcases hmem with hmem | hmem
  · exact Or.inl ⟨k, hmem, by rw [hword]⟩
  · exact Or.inr ⟨k, hmem, by rw [hword]⟩

private theorem w183finL34_e16Idx0_lt :
    (e16Idx.getD 0 []).all (fun i => decide (i < 64)) = true := by decide +kernel

private theorem w183finL34_e16Idx1_lt :
    (e16Idx.getD 1 []).all (fun i => decide (i < 64)) = true := by decide +kernel

private theorem w183finL34_repN_eq {p : ℕ} {g h : Equiv.Perm (Fin 42)} (hg : RepN p g)
    (hh : RepN p h) : g = h := by
  ext i
  have : (g i : ℕ) = (h i : ℕ) := by rw [← hg i, hh i]
  exact this

private theorem w183finL34_e16N_getD_zero :
    e16N.getD 0 [] = (e16Idx.getD 0 []).map (fun i => c1N.getD i 0) := by decide +kernel

private theorem w183finL34_e16N_getD_one :
    e16N.getD 1 [] = (e16Idx.getD 1 []).map (fun i => c1N.getD i 0) := by decide +kernel

private theorem w183finL34_mem_q1N {p : ℕ} (hp : p ∈ q1N) :
    ∃ i ∈ e16Idx.getD 0 [], c1N.getD i 0 = p := by
  rw [q1N, w183finL34_e16N_getD_zero] at hp
  exact List.mem_map.1 hp

private theorem w183finL34_mem_q2N {p : ℕ} (hp : p ∈ q2N) :
    ∃ i ∈ e16Idx.getD 1 [], c1N.getD i 0 = p := by
  rw [q2N, w183finL34_e16N_getD_one] at hp
  exact List.mem_map.1 hp

private theorem w183finL34_mem_q1N_of_mem {i : ℕ} (hi : i ∈ e16Idx.getD 0 []) :
    c1N.getD i 0 ∈ q1N := by
  rw [q1N, w183finL34_e16N_getD_zero]
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

private theorem w183finL34_mem_q2N_of_mem {i : ℕ} (hi : i ∈ e16Idx.getD 1 []) :
    c1N.getD i 0 ∈ q2N := by
  rw [q2N, w183finL34_e16N_getD_one]
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

private theorem w183finL34_e16Idx_lt {m i : ℕ} (hm : m < 2)
    (hi : i ∈ e16Idx.getD m []) : i < 64 := by
  have hm0 : m = 0 ∨ m = 1 := by omega
  rcases hm0 with rfl | rfl
  · exact of_decide_eq_true (List.all_eq_true.1 w183finL34_e16Idx0_lt i hi)
  · exact of_decide_eq_true (List.all_eq_true.1 w183finL34_e16Idx1_lt i hi)

private theorem w183finL34_not_comm_of_mem_q {ua ub : Equiv.Perm (Fin 42)} {p q : ℕ}
    (hp : RepN p ua) (hq : RepN q ub) (hp1 : p ∈ q1N) (hp2 : p ∉ q2N)
    (hq1 : q ∈ q2N) (hq2 : q ∉ q1N) : ua * ub ≠ ub * ua := by
  have h := List.all_eq_true.1 q_noncomm p hp1
  have hp2' : q2N.contains p = false := by
    rw [Bool.eq_false_iff]
    intro hc
    exact hp2 ((List.contains_iff_mem).mp hc)
  rw [hp2', Bool.false_or] at h
  have h2 := List.all_eq_true.1 h q hq1
  have hq2' : q1N.contains q = false := by
    rw [Bool.eq_false_iff]
    intro hc
    exact hq2 ((List.contains_iff_mem).mp hc)
  rw [hq2', Bool.false_or] at h2
  have hcomm : commN p q = false := by simpa using h2
  intro heq
  have htrue : commN p q = true := by
    rw [commN]
    exact (RepN.eq_iff (hp.comp hq) (hq.comp hp)).2 heq
  exact Bool.false_ne_true (hcomm ▸ htrue)

private theorem w183finL34_le_e16Set_or
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAC : A ≤ C₁)
    (hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    A ≤ e16Set 0 ∨ A ≤ e16Set 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨a, haA, ha0⟩ := (Set.not_subset).1 h1
  obtain ⟨b, hbA, hb1⟩ := (Set.not_subset).1 h2
  have ha1 : a ∈ e16Set 1 := (w183finL34_mem_e16Set_or (hAC haA) (hsq a haA)).resolve_left ha0
  have hb0 : b ∈ e16Set 0 := (w183finL34_mem_e16Set_or (hAC hbA) (hsq b hbA)).resolve_right hb1
  obtain ⟨i, hi, hia⟩ := ha1
  obtain ⟨i', hi', hi'b⟩ := hb0
  have hi64 : i < 64 := w183finL34_e16Idx_lt (by omega) hi
  have hi64' : i' < 64 := w183finL34_e16Idx_lt (by omega) hi'
  have hpaRep : RepN (wN (c1W.getD i [])) a := by rw [← hia]; exact repN_wN _
  have hpbRep : RepN (wN (c1W.getD i' [])) b := by rw [← hi'b]; exact repN_wN _
  have hpaQ2 : wN (c1W.getD i []) ∈ q2N := by
    rw [← w183finL34_c1N_getD hi64]
    exact w183finL34_mem_q2N_of_mem hi
  have hpbQ1 : wN (c1W.getD i' []) ∈ q1N := by
    rw [← w183finL34_c1N_getD hi64']
    exact w183finL34_mem_q1N_of_mem hi'
  have hpaQ1 : wN (c1W.getD i []) ∉ q1N := by
    intro hp
    obtain ⟨j, hj, hjp⟩ := w183finL34_mem_q1N hp
    have hj64 : j < 64 := w183finL34_e16Idx_lt (by omega) hj
    have hrep : RepN (wN (c1W.getD i [])) (wordPerm (c1W.getD j [])) := by
      rw [← hjp, w183finL34_c1N_getD hj64]
      exact repN_wN _
    exact ha0 ⟨j, hj, w183finL34_repN_eq hrep hpaRep⟩
  have hpbQ2 : wN (c1W.getD i' []) ∉ q2N := by
    intro hp
    obtain ⟨j, hj, hjp⟩ := w183finL34_mem_q2N hp
    have hj64 : j < 64 := w183finL34_e16Idx_lt (by omega) hj
    have hrep : RepN (wN (c1W.getD i' [])) (wordPerm (c1W.getD j [])) := by
      rw [← hjp, w183finL34_c1N_getD hj64]
      exact repN_wN _
    exact hb1 ⟨j, hj, w183finL34_repN_eq hrep hpbRep⟩
  have hneq : b * a ≠ a * b :=
    w183finL34_not_comm_of_mem_q hpbRep hpaRep hpbQ1 hpbQ2 hpaQ2 hpaQ1
  exact hneq (hcommA a haA b hbA).symm

private theorem w183finL34_e16Set_eq_image (m : ℕ) :
    e16Set m = wordPerm '' {w : List ℕ | w ∈ (e16Idx.getD m []).map (fun i => c1W.getD i [])} := by
  ext x
  constructor
  · rintro ⟨i, hi, hix⟩
    exact ⟨c1W.getD i [], List.mem_map.mpr ⟨i, hi, rfl⟩, hix⟩
  · rintro ⟨w, hw, hwx⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, hi, hwx⟩

private theorem w183finL34_ncard_e16Set_le {m : ℕ} (hm : m < 2) : (e16Set m).ncard ≤ 16 := by
  have hm0 : m = 0 ∨ m = 1 := by omega
  rcases hm0 with rfl | rfl
  · rw [w183finL34_e16Set_eq_image]
    have hs : {w : List ℕ | w ∈ (e16Idx.getD 0 []).map (fun i => c1W.getD i [])} =
        (((e16Idx.getD 0 []).map (fun i => c1W.getD i [])).toFinset : Set (List ℕ)) := by
      ext w; simp
    calc (wordPerm '' {w : List ℕ | w ∈ (e16Idx.getD 0 []).map (fun i => c1W.getD i [])}).ncard
        = (wordPerm '' (((e16Idx.getD 0 []).map (fun i => c1W.getD i [])).toFinset :
            Set (List ℕ))).ncard := by rw [hs]
      _ ≤ (((e16Idx.getD 0 []).map (fun i => c1W.getD i [])).toFinset :
            Set (List ℕ)).ncard :=
          Set.ncard_image_le (hs :=
            ((e16Idx.getD 0 []).map (fun i => c1W.getD i [])).toFinset.finite_toSet)
      _ = (((e16Idx.getD 0 []).map (fun i => c1W.getD i [])).toFinset).card :=
          Set.ncard_coe_finset _
      _ ≤ ((e16Idx.getD 0 []).map (fun i => c1W.getD i [])).length := List.toFinset_card_le _
      _ = 16 := by decide +kernel
  · rw [w183finL34_e16Set_eq_image]
    have hs : {w : List ℕ | w ∈ (e16Idx.getD 1 []).map (fun i => c1W.getD i [])} =
        (((e16Idx.getD 1 []).map (fun i => c1W.getD i [])).toFinset : Set (List ℕ)) := by
      ext w; simp
    calc (wordPerm '' {w : List ℕ | w ∈ (e16Idx.getD 1 []).map (fun i => c1W.getD i [])}).ncard
        = (wordPerm '' (((e16Idx.getD 1 []).map (fun i => c1W.getD i [])).toFinset :
            Set (List ℕ))).ncard := by rw [hs]
      _ ≤ (((e16Idx.getD 1 []).map (fun i => c1W.getD i [])).toFinset :
            Set (List ℕ)).ncard :=
          Set.ncard_image_le (hs :=
            ((e16Idx.getD 1 []).map (fun i => c1W.getD i [])).toFinset.finite_toSet)
      _ = (((e16Idx.getD 1 []).map (fun i => c1W.getD i [])).toFinset).card :=
          Set.ncard_coe_finset _
      _ ≤ ((e16Idx.getD 1 []).map (fun i => c1W.getD i [])).length := List.toFinset_card_le _
      _ = 16 := by decide +kernel

private theorem w183finL34_invI_getD_lt {i : ℕ} (hi : i < 27) : invI.getD i 0 < 64 := by
  have hlen : i < invI.length := by rw [invI_length]; exact hi
  rw [List.getD_eq_getElem (l := invI) (d := 0) (n := i) hlen]
  exact List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hlen)).1

private theorem w183finL34_repN_invN {i : ℕ} (hi : i < 27) :
    RepN (invN.getD i 0) (invP i) := by
  have hlenI : i < invI.length := by rw [invI_length]; exact hi
  have h1 : invN.getD i 0 = wN (c1W.getD (invI.getD i 0) []) := by
    rw [invN, List.getD_eq_getElem (l := invI.map (fun k => c1N.getD k 0)) (d := 0) (n := i)
        (by rw [List.length_map]; exact hlenI), List.getElem_map,
      ← List.getD_eq_getElem (l := invI) (d := 0) (n := i) hlenI,
      w183finL34_c1N_getD (w183finL34_invI_getD_lt hi)]
  rw [h1]
  exact repN_wN _

private theorem w183finL34_exists_invP
    {x : Equiv.Perm (Fin 42)} (hxC : x ∈ C₁) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ i < 27, invP i = x := by
  obtain ⟨w, hw, rfl⟩ := mem_c1 hxC
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
  have hk64 : k < 64 := by rw [c1W_length] at hk; exact hk
  have hc1Nk : c1N.getD k 0 = wN w := by
    rw [w183finL34_c1N_getD hk64, w183finL34_c1W_getD hk64, hkw]
  have hne : eqN (wN w) idN = false := by
    rw [Bool.eq_false_iff]
    intro hcon
    exact hx1 ((RepN.eq_iff (repN_wN w) RepN.one).1 hcon)
  have hsq' : eqN (compN (wN w) (wN w)) idN = true :=
    (RepN.eq_iff ((repN_wN w).comp (repN_wN w)) RepN.one).2 hx2
  have hkmem : k ∈ invI := by
    rw [invI]
    refine List.mem_filter.2 ⟨List.mem_range.2 hk64, ?_⟩
    simp only [hc1Nk, hne, hsq', Bool.not_false, Bool.true_and]
  obtain ⟨n, hn, hnk⟩ := List.getElem_of_mem hkmem
  have hn27 : n < 27 := by rw [invI_length] at hn; exact hn
  refine ⟨n, hn27, ?_⟩
  rw [invP, List.getD_eq_getElem (l := invI) (d := 0) (n := n) hn, hnk,
    w183finL34_c1W_getD hk64, hkw]

private theorem w183finL34_cm_getD {i j : ℕ} (hi : i < 27) (hj : j < 27) :
    cm i j = commN (invN.getD i 0) (invN.getD j 0) := by
  have hiN : i < invN.length := by rw [invN, List.length_map, invI_length]; exact hi
  have hjN : j < invN.length := by rw [invN, List.length_map, invI_length]; exact hj
  have h1 : commM.getD i [] = invN.map (fun b => commN (invN.getD i 0) b) := by
    rw [commM, List.getD_eq_getElem (l := invN.map (fun a => invN.map (fun b => commN a b)))
        (d := ([] : List Bool)) (n := i) (by rw [List.length_map]; exact hiN), List.getElem_map,
      ← List.getD_eq_getElem (l := invN) (d := 0) (n := i) hiN]
  rw [cm, h1, List.getD_eq_getElem (l := invN.map (fun b => commN (invN.getD i 0) b))
      (d := false) (n := j) (by rw [List.length_map]; exact hjN), List.getElem_map,
    ← List.getD_eq_getElem (l := invN) (d := 0) (n := j) hjN]

private theorem w183finL34_cm_eq {i j : ℕ} (hi : i < 27) (hj : j < 27) :
    cm i j = true ↔ invP i * invP j = invP j * invP i := by
  rw [w183finL34_cm_getD hi hj, commN]
  exact RepN.eq_iff ((w183finL34_repN_invN hi).comp (w183finL34_repN_invN hj))
    ((w183finL34_repN_invN hj).comp (w183finL34_repN_invN hi))

private theorem w183finL34_prodM_getD {i j : ℕ} (hi : i < 27) (hj : j < 27) :
    (prodM.getD i []).getD j 0 = compN (invN.getD i 0) (invN.getD j 0) := by
  have hiN : i < invN.length := by rw [invN, List.length_map, invI_length]; exact hi
  have hjN : j < invN.length := by rw [invN, List.length_map, invI_length]; exact hj
  have h1 : prodM.getD i [] = invN.map (fun b => compN (invN.getD i 0) b) := by
    rw [prodM, List.getD_eq_getElem (l := invN.map (fun a => invN.map (fun b => compN a b)))
        (d := ([] : List Nat)) (n := i) (by rw [List.length_map]; exact hiN), List.getElem_map,
      ← List.getD_eq_getElem (l := invN) (d := 0) (n := i) hiN]
  rw [h1, List.getD_eq_getElem (l := invN.map (fun b => compN (invN.getD i 0) b))
      (d := 0) (n := j) (by rw [List.length_map]; exact hjN), List.getElem_map,
    ← List.getD_eq_getElem (l := invN) (d := 0) (n := j) hjN]

private theorem w183finL34_prodM_ne {i j k : ℕ} (hi : i < 27) (hj : j < 27) (hk : k < 27)
    (h : invP i * invP j ≠ invP k) :
    ((prodM.getD i []).getD j 0 != invN.getD k 0) = true := by
  rw [w183finL34_prodM_getD hi hj, bne_iff_ne]
  intro hab
  exact h (w183finL34_repN_eq (hab ▸ ((w183finL34_repN_invN hi).comp (w183finL34_repN_invN hj)))
    (w183finL34_repN_invN hk))

theorem isSylowIn_C1 : IsSylowIn 2 C₁ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowIn_of_card_eq inf_le_right ?_
  rw [card_C₁, card_S]
  decide +kernel

theorem card_eight_or_sixteen {A : Subgroup (Equiv.Perm (Fin 42))}
    (hAC : A ≤ C₁) (hel : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) :
    Nat.card A = 8 ∨ Nat.card A = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => hel.2 x hx
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hA2 : IsPGroup 2 A := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := A)).1 hA2
  have hle : Nat.card A ≤ 16 := by
    rcases w183finL34_le_e16Set_or hAC hcommA hsq with hm | hm
    · refine (Set.ncard_le_ncard hm).trans (w183finL34_ncard_e16Set_le (m := 0) (by omega))
    · refine (Set.ncard_le_ncard hm).trans (w183finL34_ncard_e16Set_le (m := 1) (by omega))
  have hn3 : 3 ≤ n := by
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 ?_
    rw [← hn, (by norm_num : (2 : ℕ) ^ 3 = 8)]
    exact h8
  have hn4 : n ≤ 4 := by
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 ?_
    rw [← hn, (by norm_num : (2 : ℕ) ^ 4 = 16)]
    exact hle
  have hn34 : n = 3 ∨ n = 4 := by omega
  rcases hn34 with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr hn

theorem eq_e16_of_card {A : Subgroup (Equiv.Perm (Fin 42))}
    (hAC : A ≤ C₁) (hel : IsElemAbelian 2 A) (h16 : Nat.card A = 16) :
    ∃ m < 2, (A : Set (Equiv.Perm (Fin 42))) = e16Set m := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => hel.2 x hx
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hA : (A : Set (Equiv.Perm (Fin 42))).ncard = 16 := by
    rw [← Nat.card_coe_set_eq (A : Set (Equiv.Perm (Fin 42)))]
    exact h16
  rcases w183finL34_le_e16Set_or hAC hcommA hsq with hm | hm
  · exact ⟨0, by omega, Set.eq_of_subset_of_ncard_le hm
      (by rw [hA]; exact w183finL34_ncard_e16Set_le (m := 0) (by omega))⟩
  · exact ⟨1, by omega, Set.eq_of_subset_of_ncard_le hm
      (by rw [hA]; exact w183finL34_ncard_e16Set_le (m := 1) (by omega))⟩

theorem exists_triple {A : Subgroup (Equiv.Perm (Fin 42))}
    (hAC : A ≤ C₁) (hel : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    ∃ i < 27, ∃ j < 27, ∃ k < 27, i ≠ j ∧ k ≠ i ∧ k ≠ j ∧ cm i j = true ∧ cm i k = true ∧
      cm j k = true ∧ ((prodM.getD i []).getD j 0 != invN.getD k 0) = true ∧
      (A : Set (Equiv.Perm (Fin 42))) = span3 (invP i) (invP j) (invP k) := by
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by simpa [pow_two] using hel.2 x hx
  obtain ⟨x, hxA, y, hyA, hx1, hyn⟩ := exists_two_independent A (by omega)
  obtain ⟨z, hzA, hzn⟩ := exists_mem_notMem_list A [1, x, y, x * y]
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hx2 : x * x = 1 := hsq x hxA
  have hy2 : y * y = 1 := hsq y hyA
  have hz2 : z * z = 1 := hsq z hzA
  have hy1 : y ≠ 1 := fun h => hyn (by simp [h])
  have hyx : y ≠ x := fun h => hyn (by simp [h])
  have hz1 : z ≠ 1 := fun h => hzn (by simp [h])
  have hzx : z ≠ x := fun h => hzn (by simp [h])
  have hzy : z ≠ y := fun h => hzn (by simp [h])
  have hzxy : z ≠ x * y := fun h => hzn (by simp [h])
  have hxy : x * y = y * x := hcommA x hxA y hyA
  have hxz : x * z = z * x := hcommA x hxA z hzA
  have hyz : y * z = z * y := hcommA y hyA z hzA
  have hxy1 : x * y ≠ 1 := fun h => hyx (by
    have h2 := congrArg (fun t => x * t) h
    simp only [mul_one] at h2
    rw [← mul_assoc, hx2, one_mul] at h2
    exact h2)
  have hxz1 : x * z ≠ 1 := fun h => hzx (by
    have h2 := congrArg (fun t => x * t) h
    simp only [mul_one] at h2
    rw [← mul_assoc, hx2, one_mul] at h2
    exact h2)
  have hyz1 : y * z ≠ 1 := fun h => hzy (by
    have h2 := congrArg (fun t => y * t) h
    simp only [mul_one] at h2
    rw [← mul_assoc, hy2, one_mul] at h2
    exact h2)
  have hxy2 : x * y * (x * y) = 1 := hsq (x * y) (A.mul_mem hxA hyA)
  have hxyz1 : x * (y * z) ≠ 1 := by
    intro h
    exact hzxy (by
      have h2 : x * y * z = 1 := by rw [← mul_assoc] at h; exact h
      have h3 := eq_inv_of_mul_eq_one_right h2
      rwa [inv_eq_of_mul_eq_one_right hxy2] at h3)
  have hind : ∀ a b c : Bool, bpow x a * bpow y b * bpow z c = 1 →
      a = false ∧ b = false ∧ c = false := by
    intro a b c h
    cases a <;> cases b <;> cases c <;>
      simp [bpow] at h ⊢
    all_goals
      first
      | exact absurd h hx1
      | exact absurd h hy1
      | exact absurd h hz1
      | exact absurd h hxy1
      | exact absurd h hxz1
      | exact absurd h hyz1
      | exact absurd h hxyz1
  let f : Bool × Bool × Bool → Equiv.Perm (Fin 42) :=
    fun w => prod4 x y z 1 ((w.1, w.2.1), (w.2.2, false))
  have hf : ∀ w w' : Bool × Bool × Bool,
      f w * f w' = f (xor w.1 w'.1, xor w.2.1 w'.2.1, xor w.2.2 w'.2.2) := by
    intro w w'
    have h := prod4_mul_prod4 (x₁ := x) (x₂ := y) (y₃ := z) (y₄ := 1)
      hx2 hy2 hz2 (by simp) hxy hxz (by simp) hyz (by simp) (by simp)
      ((w.1, w.2.1), (w.2.2, false)) ((w'.1, w'.2.1), (w'.2.2, false))
    dsimp only [f]
    rw [h]
    simp [xor4, Bool.xor_false]
  have hf_bpow : ∀ p q r : Bool, f (p, q, r) = bpow x p * bpow y q * bpow z r := by
    intro p q r
    dsimp only [f]
    simp [prod4, bpow]
  have hf_sq : ∀ w, f w * f w = 1 := by
    intro w
    rw [hf w w]
    simp only [Bool.xor_self]
    exact prod4_zero x y z 1
  have hf_inj : Function.Injective f := by
    intro w w' hww
    have h1 : f (xor w.1 w'.1, xor w.2.1 w'.2.1, xor w.2.2 w'.2.2) = 1 := by
      rw [← hf, hww, hf_sq]
    rw [hf_bpow] at h1
    obtain ⟨ha, hb, hc⟩ := hind _ _ _ h1
    obtain ⟨a, b, c⟩ := w
    obtain ⟨a', b', c'⟩ := w'
    revert ha hb hc
    cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> decide
  have hf_range : Set.range f = span3 x y z := by
    ext u
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨a, b, c⟩ := w
      cases a <;> cases b <;> cases c <;>
        dsimp only [f]
      all_goals simp [span3, prod4, bpow, Set.mem_insert_iff, Set.mem_singleton_iff]
    · intro hu
      simp only [span3, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨(false, false, false), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(true, false, false), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(false, true, false), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(false, false, true), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(true, true, false), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(true, false, true), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(false, true, true), by dsimp only [f]; simp [prod4, bpow]⟩
      · exact ⟨(true, true, true), by dsimp only [f]; simp [prod4, bpow]⟩
  have hcard : (span3 x y z).ncard = 8 := by
    rw [← hf_range, Set.ncard_range_of_injective hf_inj]
    simp
  have hsub : span3 x y z ⊆ (A : Set (Equiv.Perm (Fin 42))) := by
    intro u hu
    simp only [span3, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact hxA
    · exact hyA
    · exact hzA
    · exact A.mul_mem hxA hyA
    · exact A.mul_mem hxA hzA
    · exact A.mul_mem hyA hzA
    · exact A.mul_mem (A.mul_mem hxA hyA) hzA
  have hA8 : (A : Set (Equiv.Perm (Fin 42))).ncard = 8 := by
    rw [← Nat.card_coe_set_eq (A : Set (Equiv.Perm (Fin 42)))]
    exact h8
  have hEq : (A : Set (Equiv.Perm (Fin 42))) = span3 x y z :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hA8])).symm
  obtain ⟨i, hi27, hix⟩ := w183finL34_exists_invP (hAC hxA) hx2 hx1
  obtain ⟨j, hj27, hjy⟩ := w183finL34_exists_invP (hAC hyA) hy2 hy1
  obtain ⟨k, hk27, hkz⟩ := w183finL34_exists_invP (hAC hzA) hz2 hz1
  refine ⟨i, hi27, j, hj27, k, hk27, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => (fun hxyx : x = y => hyx hxyx.symm) (by rw [← hix, ← hjy, h])
  · exact fun h => (fun hxzx : x = z => hzx hxzx.symm) (by rw [← hix, ← hkz, h])
  · exact fun h => (fun hyzy : y = z => hzy hyzy.symm) (by rw [← hjy, ← hkz, h])
  · exact (w183finL34_cm_eq hi27 hj27).2 (by rw [hix, hjy]; exact hxy)
  · exact (w183finL34_cm_eq hi27 hk27).2 (by rw [hix, hkz]; exact hxz)
  · exact (w183finL34_cm_eq hj27 hk27).2 (by rw [hjy, hkz]; exact hyz)
  · exact w183finL34_prodM_ne hi27 hj27 hk27 (by rw [hix, hjy, hkz]; exact fun h => hzxy h.symm)
  · rw [hix, hjy, hkz]
    exact hEq

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
