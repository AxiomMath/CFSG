module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLD6Gen

public section

namespace CFSG.StandardType.QTwoD6

open Module

open Module

@[expose] def qd6a_dev (j : Fin 6) (c : Fin 6 → ZMod 3) : ZMod 3 :=
  if j = 0 then 2 * c 0 - c 1
  else if j = 1 then -c 0 + 2 * c 1 - c 2
  else if j = 2 then -c 1 + 2 * c 2 - c 3
  else if j = 3 then -c 2 + 2 * c 3 - c 4 - c 5
  else if j = 4 then -c 3 + 2 * c 4
  else -c 3 + 2 * c 5

@[expose] def qd6a_gen (j : Fin 6) (c : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  Function.update c j (c j - qd6a_dev j c)

@[expose] def qd6a_applyCWord : List (Fin 6) → (Fin 6 → ZMod 3) → (Fin 6 → ZMod 3)
  | [], c => c
  | j :: w, c => qd6a_applyCWord w (qd6a_gen j c)

@[expose] def qd6a_toEps (c : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![c 0, 2 * c 0 + c 1, 2 * c 1 + c 2, 2 * c 2 + c 3, 2 * c 3 + c 4 + c 5, 2 * c 4 + c 5]

@[expose] def qd6a_succFin (j : Fin 6) (h : j.val < 5) : Fin 6 := ⟨j.val + 1, by omega⟩

@[expose] def qd6a_epsGen (j : Fin 6) (a : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  if h : j.val < 5 then fun i => a (Equiv.swap j (qd6a_succFin j h) i)
  else ![a 0, a 1, a 2, a 3, -a 5, -a 4]

@[expose] def qd6a_bubblePass (st : List (Fin 6) × (Fin 6 → ZMod 3)) (j : Fin 5) :
    List (Fin 6) × (Fin 6 → ZMod 3) :=
  if (st.2 j.castSucc).val > (st.2 j.succ).val then
    (st.1 ++ [j.castSucc], qd6a_epsGen j.castSucc st.2)
  else st

@[expose] def qd6a_sortAux (a : Fin 6 → ZMod 3) : List (Fin 6) × (Fin 6 → ZMod 3) :=
  (List.range 5).foldl (fun st _ => (List.finRange 5).foldl qd6a_bubblePass st) ([], a)

@[expose] def qd6a_normWord (c : Fin 6 → ZMod 3) : List (Fin 6) := (qd6a_sortAux (qd6a_toEps c)).1

@[expose] def qd6a_can (c : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 := qd6a_applyCWord (qd6a_normWord c) c

@[expose] def qd6a_cOfEps (b : Fin 6) : Fin 6 → ZMod 3 := fun i => epsVec b i.succ

@[expose] def qd6a_ws : List (List (Fin 6)) := [
    [],
    [0, 4, 2, 3, 2, 5, 1],
    [4, 5, 2, 3, 2, 5, 3, 5, 0],
    [0, 5, 3, 5, 2, 1, 4],
    [5, 3, 2, 4, 3, 2],
    [3, 2, 4],
    [4, 0, 3, 5, 2],
    [5, 3, 2, 1, 5, 4, 0],
    [0, 3, 4, 3, 2, 1, 0],
    [5, 3, 3, 4, 3, 2, 1, 0],
    [2, 3, 5, 4, 3],
    [4, 3, 5, 0, 2, 1, 0],
    [2, 4, 3, 2, 4, 0, 3, 2],
    [2, 2, 2, 3],
    [5, 4, 3, 5, 2, 1, 4, 3, 5],
    [3, 0, 1, 2, 1, 3, 4, 3],
    [3, 3, 3, 0, 5, 3, 4, 2],
    [1, 4, 2, 3, 5, 2, 3, 1, 4],
    [3, 3, 5, 1, 3, 4, 2, 3, 5],
    [3, 4, 5, 2, 1, 0, 3, 2, 1]]

@[expose] def qd6a_canNonAxisSet : Finset (Fin 6 → ZMod 3) := {
    ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 2],
    ![0, 0, 0, 1, 2, 0],
    ![0, 0, 0, 1, 2, 1],
    ![0, 0, 0, 2, 1, 0],
    ![0, 0, 1, 0, 0, 2],
    ![0, 0, 1, 2, 1, 0],
    ![0, 0, 1, 2, 1, 2],
    ![0, 0, 1, 2, 2, 1],
    ![0, 0, 2, 1, 2, 1],
    ![0, 1, 0, 2, 1, 0],
    ![0, 1, 2, 0, 0, 1],
    ![0, 1, 2, 0, 0, 2],
    ![0, 1, 2, 0, 1, 0],
    ![0, 1, 2, 1, 2, 1],
    ![0, 2, 1, 0, 0, 2],
    ![1, 0, 2, 1, 2, 1],
    ![1, 2, 0, 1, 0, 2],
    ![1, 2, 0, 1, 2, 0],
    ![1, 2, 0, 1, 2, 1],
    ![1, 2, 0, 2, 1, 0],
    ![1, 2, 1, 0, 0, 2],
    ![2, 1, 0, 2, 1, 0]}

@[expose] abbrev qd6a_NonAxis (c : Fin 6 → ZMod 3) : Prop :=
  (∀ b : Fin 6, c ≠ qd6a_cOfEps b ∧ c ≠ - qd6a_cOfEps b) ∧ c ≠ 0

set_option maxRecDepth 100000 in
lemma qd6a_can_mem : ∀ c : Fin 6 → ZMod 3,
    qd6a_NonAxis c → qd6a_can c ∈ qd6a_canNonAxisSet := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma qd6a_canon_check : ∀ c ∈ qd6a_canNonAxisSet,
    13 ≤ (qd6a_ws.map (fun w => qd6a_applyCWord w c)).dedup.length := by
  decide +kernel

@[expose] def qd6a_cOf (v : V7) : Fin 6 → ZMod 3 := fun i => v i.succ

@[expose] def qd6a_toVec (c : Fin 6 → ZMod 3) : V7 := ∑ i, c i • hvec i

lemma qd6a_toVec_apply (c : Fin 6 → ZMod 3) (k : Fin 6) :
    qd6a_toVec c k.succ = c k := by
  classical
  simp only [qd6a_toVec, hvec, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    have hki : k ≠ i := fun hh => hi hh.symm
    simp [Fin.succ_inj, hki]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

lemma qd6a_toVec_injective : Function.Injective qd6a_toVec := by
  intro c c' h
  funext k
  have hk := congr_fun h k.succ
  rwa [qd6a_toVec_apply, qd6a_toVec_apply] at hk

lemma qd6a_toVec_cOf (v : V7) (hv : v 0 = 0) : qd6a_toVec (qd6a_cOf v) = v := by
  funext k
  induction k using Fin.cases with
  | zero => simp [qd6a_toVec, hvec, hv]
  | succ m => exact qd6a_toVec_apply (qd6a_cOf v) m

lemma qd6a_toVec_neg (c : Fin 6 → ZMod 3) : qd6a_toVec (-c) = -qd6a_toVec c := by
  simp only [qd6a_toVec, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

lemma qd6a_epsVec_zero (b : Fin 6) : epsVec b 0 = 0 := by
  fin_cases b <;> decide

lemma qd6a_toVec_cOfEps (b : Fin 6) : qd6a_toVec (qd6a_cOfEps b) = epsVec b :=
  qd6a_toVec_cOf (epsVec b) (qd6a_epsVec_zero b)

lemma qd6a_avec_toVec (j : Fin 6) (c : Fin 6 → ZMod 3) :
    avec j (qd6a_toVec c) = qd6a_dev j c := by
  have h1 : avec j (qd6a_toVec c) = ∑ i : Fin 6, (cartanD6 i j : ZMod 3) * c i := by
    simp only [avec, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [qd6a_toVec_apply])
  rw [h1]
  fin_cases j <;> simp [qd6a_dev, Fin.sum_univ_succ, cartanD6] <;> ring

lemma qd6a_toVec_gen (j : Fin 6) (c : Fin 6 → ZMod 3) :
    qd6a_toVec (qd6a_gen j c) = simpleD6 j (qd6a_toVec c) := by
  rw [simpleD6, Module.reflection_apply]
  funext k
  induction k using Fin.cases with
  | zero => simp [qd6a_toVec, hvec]
  | succ m =>
    by_cases hm : m = j
    · subst hm
      simp [qd6a_toVec_apply, qd6a_avec_toVec, qd6a_gen, Function.update_apply, hvec,
        Pi.single_apply]
    · simp [qd6a_toVec_apply, qd6a_avec_toVec, qd6a_gen, Function.update_apply, hvec,
        Pi.single_apply, hm, Ne.symm hm, Fin.succ_inj]

@[expose] noncomputable def qd6a_applyWord : List (Fin 6) → V7 ≃ₗ[ZMod 3] V7
  | [] => 1
  | j :: w => qd6a_applyWord w * simpleD6 j

lemma qd6a_applyWord_mem (w : List (Fin 6)) : qd6a_applyWord w ∈ W6 := by
  induction w with
  | nil => exact W6.one_mem
  | cons j w ih =>
    change qd6a_applyWord w * simpleD6 j ∈ W6
    exact W6.mul_mem ih (Subgroup.subset_closure ⟨j, rfl⟩)

lemma qd6a_applyWord_toVec (w : List (Fin 6)) (c : Fin 6 → ZMod 3) :
    qd6a_toVec (qd6a_applyCWord w c) = qd6a_applyWord w (qd6a_toVec c) := by
  induction w generalizing c with
  | nil => rfl
  | cons j w ih =>
    simp only [qd6a_applyCWord, qd6a_applyWord, LinearEquiv.mul_apply]
    rw [ih, qd6a_toVec_gen]

end CFSG.StandardType.QTwoD6

end
