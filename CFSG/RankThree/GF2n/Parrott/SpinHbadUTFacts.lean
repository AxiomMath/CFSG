module

public import CFSG.RankThree.GF2n.Parrott.SpinHbadUTChecks
public import CFSG.RankThree.GF2n.Parrott.SpinTFacts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def hbadS : A45 := evalSpinWord spinGenA (toW lHbadS)

@[expose] def hbadA : A45 := evalSpinWord spinGenA (toW lHbadA)

section Perm


theorem utA_mul_self : (uA * tA) * (uA * tA) = 1 := by
  apply Subtype.ext
  show (u * t) * (u * t) = 1
  decide +kernel

theorem utA_mem_QP45 : uA * tA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
  Subgroup.mem_subgroupOf.mpr (QP45.originalSubgroup.mul_mem u_mem_Q t_mem_Q)

private theorem permTab_utA : permTab ((uA * tA : A45) : P45) = tUT := by
  show permTab (u * t) = tUT
  decide +kernel

theorem hbadS_comm_utA : hbadS * (uA * tA) = (uA * tA) * hbadS := by
  unfold hbadS
  exact comm_of_tab permTab_utA hbadS_comm

theorem hbadS_pow_three : hbadS ^ 3 = 1 := by
  apply eq_of_permTab_eq
  unfold hbadS
  rw [permTab_coe_pow, permTab_coe_one, permTab_coe_evalSpinWord,
    show (fun i => permTab ((spinGenA i : A45) : P45)) = t3 from funext permTab_spinGenA]
  exact hbadS_cube

theorem hbadS_ne_one : hbadS ≠ 1 := by
  intro h
  apply hbadS_ne
  have h' := congrArg (fun a : A45 => permTab (a : P45)) h
  unfold hbadS at h'
  rw [permTab_coe_one, permTab_coe_evalSpinWord,
    show (fun i => permTab ((spinGenA i : A45) : P45)) = t3 from funext permTab_spinGenA] at h'
  exact h'

private theorem coe_evalSpinWord_mem_QP45 : ∀ (l : List ℕ), (∀ i ∈ l, i % 3 ≠ 2) →
    ((evalSpinWord spinGenA (toW l) : A45) : P45) ∈ QP45.originalSubgroup := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [toW, List.map_nil, evalSpinWord_nil, Subgroup.coe_one]
    exact QP45.originalSubgroup.one_mem
  | cons a l ih =>
    intro hl
    simp only [toW, List.map_cons, evalSpinWord_cons, Subgroup.coe_mul, pow_one]
    have ha : a % 3 = 0 ∨ a % 3 = 1 := by
      have hlt : a % 3 < 3 := Nat.mod_lt _ (by decide)
      have hne : a % 3 ≠ 2 := hl a (by simp)
      omega
    have hgen : ((spinGenA ⟨a % 3, Nat.mod_lt _ (by decide)⟩ : A45) : P45) ∈
        QP45.originalSubgroup := by
      rcases ha with h | h
      · have hfin : (⟨a % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 := Fin.ext h
        rw [hfin]
        show x45 ∈ QP45.originalSubgroup
        rw [QP45_closure]
        exact Subgroup.subset_closure (by simp)
      · have hfin : (⟨a % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 := Fin.ext h
        rw [hfin]
        show y45 ∈ QP45.originalSubgroup
        rw [QP45_closure]
        exact Subgroup.subset_closure (by simp)
    exact QP45.originalSubgroup.mul_mem hgen (ih (fun i hi => hl i (List.mem_cons_of_mem a hi)))

theorem hbadS_mem_QP45 : hbadS ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  apply Subgroup.mem_subgroupOf.mpr
  unfold hbadS
  exact coe_evalSpinWord_mem_QP45 lHbadS (by
    intro i hi
    have hall : lHbadS.all (fun i => i % 3 != 2) = true := by decide +kernel
    have h := (List.all_eq_true.mp hall) i hi
    simpa using h)

theorem hbadA_comm_utA : hbadA * (uA * tA) = (uA * tA) * hbadA := by
  unfold hbadA
  exact comm_of_tab permTab_utA hbadA_comm

private theorem hbadA_eq : hbadA = evalSpinWord spinGenA (toW [1, 1, 1, 0, 1, 0]) *
    spinGenA 2 * evalSpinWord spinGenA (toW [1]) := by
  apply eq_of_permTab_eq
  decide +kernel

theorem hbadA_not_mem_QP45 : hbadA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  intro h
  have hA : ((hbadA : A45) : P45) ∈ QP45.originalSubgroup := Subgroup.mem_subgroupOf.mp h
  let p1 : A45 := evalSpinWord spinGenA (toW [1, 1, 1, 0, 1, 0])
  let p2 : A45 := evalSpinWord spinGenA (toW [1])
  have hp1 : ((p1 : A45) : P45) ∈ QP45.originalSubgroup :=
    coe_evalSpinWord_mem_QP45 [1, 1, 1, 0, 1, 0] (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega)
  have hp2 : ((p2 : A45) : P45) ∈ QP45.originalSubgroup :=
    coe_evalSpinWord_mem_QP45 [1] (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega)
  have hdecomp : hbadA = p1 * spinGenA 2 * p2 := by
    simpa only [p1, p2] using hbadA_eq
  have hmem : ((p1 : A45) : P45) * ((spinGenA 2 : A45) : P45) *
      ((p2 : A45) : P45) ∈ QP45.originalSubgroup := by
    have h' := hA
    rw [hdecomp] at h'
    simpa only [Subgroup.coe_mul] using h'
  have hf : ((spinGenA 2 : A45) : P45) ∈ QP45.originalSubgroup := by
    have h1 : ((p1 : A45) : P45)⁻¹ * (((p1 : A45) : P45) * ((spinGenA 2 : A45) : P45) *
        ((p2 : A45) : P45)) * ((p2 : A45) : P45)⁻¹ ∈ QP45.originalSubgroup :=
      QP45.originalSubgroup.mul_mem
        (QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem hp1) hmem)
        (QP45.originalSubgroup.inv_mem hp2)
    rwa [show ((p1 : A45) : P45)⁻¹ * (((p1 : A45) : P45) * ((spinGenA 2 : A45) : P45) *
        ((p2 : A45) : P45)) * ((p2 : A45) : P45)⁻¹ = ((spinGenA 2 : A45) : P45) from by group] at h1
  apply v_not_mem_Q
  have hvf : t * f45 = v := by decide +kernel
  rw [← hvf]
  exact QP45.originalSubgroup.mul_mem t_mem_Q (by simpa only [spinGenA] using hf)

end Perm

section Spin


private theorem colsOf_utA_spin : colsOf (spinMat (uA * tA)) = bUT := by
  rw [map_mul, colsOf_mul, cols_uA, cols_tA]
  rfl

private theorem colsOf_utA : colsOf (((rhoA (uA * tA) : GL8) : Mat8)) = bUT := by
  rw [← spinMat_apply (uA * tA)]
  exact colsOf_utA_spin

private theorem bitmask_rhoA_utA_mulVec (v : V) :
    bitmask (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ v) = bapply bUT (bitmask v) := by
  rw [← bapply_colsOf (((rhoA (uA * tA) : GL8) : Mat8)) v, colsOf_utA]

private theorem bitmask_rhoA_hbadS_mulVec (v : V) :
    bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ v) = bapply bHbadS (bitmask v) := by
  rw [← spinMat_apply hbadS]
  exact bitmask_rhoA_mulVec_word (toW lHbadS) v

private theorem bitmask_rhoA_hbadA_mulVec (v : V) :
    bitmask (((rhoA hbadA : GL8) : Mat8) *ᵥ v) = bapply bHbadA (bitmask v) := by
  rw [← spinMat_apply hbadA]
  exact bitmask_rhoA_mulVec_word (toW lHbadA) v

private theorem bitmask_utA_add (v : V) :
    bitmask (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ v + v) =
      bapply bUT (bitmask v) ^^^ bitmask v := by
  rw [bitmask_add, bitmask_rhoA_utA_mulVec]

private theorem bitmask_hbadS_utA_add (v : V) :
    bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ
      (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ v + v)) =
      bapply bHbadS (bapply bUT (bitmask v) ^^^ bitmask v) := by
  rw [bitmask_rhoA_hbadS_mulVec, bitmask_utA_add]

private theorem hbadF_bitmask (v : V) :
    hbadF (bitmask v) = bq (bitmask v) (bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ
      (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ v + v))) := by
  unfold hbadF
  rw [bitmask_hbadS_utA_add]

theorem card_spin_fixed_utA :
    Nat.card {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} = 16 := by
  let S : Set V := {w : V | ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w}
  have hS : Nat.card {w : V // ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w} = S.ncard := by
    change Nat.card S = S.ncard
    exact Nat.card_coe_set_eq S
  have hcongr : S.ncard = (hbadW.toFinset : Set ℕ).ncard := by
    refine Set.ncard_congr (fun v _ => bitmask v) ?_ ?_ ?_
    · intro v hv
      have hv' : bapply bUT (bitmask v) = bitmask v := by
        have h := (spinFixes_iff (uA * tA) v).1 hv
        rwa [colsOf_utA_spin] at h
      change bitmask v ∈ hbadW.toFinset
      rw [List.mem_toFinset]
      exact (hbadW_spec _ (bitmask_lt v)).2 hv'
    · intro v _ w _ h
      exact bitmask_injective h
    · intro n hn
      have hn256 : n < 256 := hbadW_lt n (List.mem_toFinset.1 hn)
      refine ⟨vecOfNat n, ?_, ?_⟩
      · apply (spinFixes_iff (uA * tA) (vecOfNat n)).2
        rw [colsOf_utA_spin, bitmask_vecOfNat n hn256]
        exact (hbadW_spec n hn256).1 (List.mem_toFinset.1 hn)
      · exact bitmask_vecOfNat n hn256
  rw [hS, hcongr, Set.ncard_coe_finset, List.toFinset_card_of_nodup hbadW_nodup, hbadW_length]

theorem spin_exists_eq_mul_utA_add (w : V)
    (hw : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w) :
    ∃ m : V, w = ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ m + m := by
  have hwfix : bapply bUT (bitmask w) = bitmask w := by
    have h := (spinFixes_iff (uA * tA) w).1 hw
    rwa [colsOf_utA_spin] at h
  have hmem : bitmask w ∈ hbadW := (hbadW_spec _ (bitmask_lt w)).2 hwfix
  obtain ⟨n, hn, hnim⟩ := hbadW_im _ hmem
  refine ⟨vecOfNat n, ?_⟩
  apply bitmask_injective
  rw [bitmask_add, ← bapply_colsOf (((rhoA (uA * tA) : GL8) : Mat8)) (vecOfNat n), colsOf_utA,
    bitmask_vecOfNat n hn]
  exact hnim.symm

theorem spin_q_eq_zero_of_utA (w : V)
    (hw : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w) : q w = 0 := by
  rw [q_eq_zero_iff]
  have hwfix : bapply bUT (bitmask w) = bitmask w := by
    have h := (spinFixes_iff (uA * tA) w).1 hw
    rwa [colsOf_utA_spin] at h
  exact hbadW_q _ ((hbadW_spec _ (bitmask_lt w)).2 hwfix)

theorem spin_hbadS_sum (w : V)
    (hw : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w) :
    ((rhoA hbadS : GL8) : Mat8) *ᵥ (((rhoA hbadS : GL8) : Mat8) *ᵥ w) +
      ((rhoA hbadS : GL8) : Mat8) *ᵥ w + w = 0 := by
  have hwfix : bapply bUT (bitmask w) = bitmask w := by
    have h := (spinFixes_iff (uA * tA) w).1 hw
    rwa [colsOf_utA_spin] at h
  have hmem : bitmask w ∈ hbadW := (hbadW_spec _ (bitmask_lt w)).2 hwfix
  have hsum := hbadS_sum _ hmem
  apply bitmask_injective
  rw [bitmask_zero, bitmask_add, bitmask_add, bitmask_rhoA_hbadS_mulVec,
    bitmask_rhoA_hbadS_mulVec]
  exact hsum

theorem spin_hbadA (m : V)
    (hf : b m (((rhoA hbadS : GL8) : Mat8) *ᵥ (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ m + m)) = 1) :
    ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m) +
        (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m) ≠ 0 ∧
      b (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m)
        (((rhoA hbadS : GL8) : Mat8) *ᵥ
          (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m) +
            (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m))) = 0 := by
  have hfne : b m (((rhoA hbadS : GL8) : Mat8) *ᵥ
      (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ m + m)) ≠ 0 := by
    rw [hf]
    decide
  have hbq_ne : bq (bitmask m) (bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ
      (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ m + m))) ≠ 0 := by
    intro h0
    exact hfne ((b_eq_zero_iff m _).2 h0)
  have hbq_val : bq (bitmask m) (bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ
      (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ m + m))) = 1 := by
    have hlt : bq (bitmask m) (bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ
        (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ m + m))) < 2 := by
      unfold bq
      exact Nat.mod_lt _ (by decide)
    omega
  have hF1 : hbadF (bitmask m) = 1 := by
    rw [hbadF_bitmask]
    exact hbq_val
  obtain ⟨hne, hF0⟩ := hbadA_check (bitmask m) (bitmask_lt m) hF1
  have hm' : bitmask (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m) =
      bitmask m ^^^ bapply bHbadA (bitmask m) := by
    rw [bitmask_add, bitmask_rhoA_hbadA_mulVec]
  constructor
  · intro h0
    apply hne
    have h1 : bitmask (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ
        (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m) +
          (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m)) = 0 := by
      rw [h0, bitmask_zero]
    rw [bitmask_utA_add, hm'] at h1
    exact h1
  · rw [b_eq_zero_iff]
    have hbit : bitmask (((rhoA hbadS : GL8) : Mat8) *ᵥ
        (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m) +
          (m + ((rhoA hbadA : GL8) : Mat8) *ᵥ m))) =
        bapply bHbadS (bapply bUT (bitmask m ^^^ bapply bHbadA (bitmask m)) ^^^
          (bitmask m ^^^ bapply bHbadA (bitmask m))) := by
      rw [bitmask_hbadS_utA_add, hm']
    rw [hbit, hm']
    exact hF0

theorem card_utA_fix_le :
    Nat.card {a : A45 // a * (uA * tA) = (uA * tA) * a ∧
      ∀ w : V, ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w → ((rhoA a : GL8) : Mat8) *ᵥ w = w} ≤
      16 := by
  classical
  let K := {a : A45 // a * (uA * tA) = (uA * tA) * a ∧
      ∀ w : V, ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ w = w → ((rhoA a : GL8) : Mat8) *ᵥ w = w}
  change Nat.card K ≤ 16
  let C : Subgroup A45 := Subgroup.centralizer ({uA * tA} : Set A45)
  have hCcard : Nat.card C = 192 := qa45_involution_centralizers.2.1
  have hmemC : ∀ x : A45, x * (uA * tA) = (uA * tA) * x → x ∈ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx
  let ws : Fin hbadTrans.length → A45 := fun i => evalSpinWord spinGenA (toW (hbadTrans.get i))
  have hws_comm : ∀ i : Fin hbadTrans.length, ws i * (uA * tA) = (uA * tA) * ws i := by
    intro i
    exact comm_of_tab permTab_utA (hbadTrans_comm (hbadTrans.get i) (List.getElem_mem i.isLt))
  let f : Fin hbadTrans.length × K → C := fun p =>
    ⟨ws p.1 * (p.2 : A45), hmemC _ (by
      rw [mul_assoc, p.2.2.1, ← mul_assoc, hws_comm p.1, mul_assoc])⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨i, k⟩ ⟨j, k'⟩ hfij
    have hndT : hbadTrans.Nodup := List.Nodup.of_map _ hbadTrans_distinct
    have hval : ws i * (k : A45) = ws j * (k' : A45) := congrArg Subtype.val hfij
    have hcomp : ∀ e ∈ hbadBasis, bapply (evalB b3 (toW (hbadTrans.get i))) e =
        bapply (evalB b3 (toW (hbadTrans.get j))) e := by
      intro e he
      have heW : e ∈ hbadW := hbadBasis_sub e he
      have he256 : e < 256 := hbadW_lt e heW
      have hefix : bapply bUT e = e := (hbadW_spec e he256).1 heW
      have hfixut : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ vecOfNat e = vecOfNat e := by
        apply (spinFixes_iff (uA * tA) (vecOfNat e)).2
        rw [colsOf_utA_spin, bitmask_vecOfNat e he256, hefix]
      have hk : ((rhoA (k : A45) : GL8) : Mat8) *ᵥ vecOfNat e = vecOfNat e := k.2.2 _ hfixut
      have hk' : ((rhoA (k' : A45) : GL8) : Mat8) *ᵥ vecOfNat e = vecOfNat e := k'.2.2 _ hfixut
      have hb := congrArg (fun a : A45 => bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat e)) hval
      simp only [ws, rhoA_mulVec_mul, hk, hk', bitmask_rhoA_mulVec_word,
        bitmask_vecOfNat e he256] at hb
      exact hb
    have hRe : hbadRestr (evalB b3 (toW (hbadTrans.get i))) =
        hbadRestr (evalB b3 (toW (hbadTrans.get j))) := by
      unfold hbadRestr
      apply List.map_congr_left
      exact hcomp
    have hget : hbadTrans.get i = hbadTrans.get j :=
      List.inj_on_of_nodup_map hbadTrans_distinct (List.getElem_mem i.isLt)
        (List.getElem_mem j.isLt) hRe
    have hij : i = j := Fin.ext ((List.Nodup.getElem_inj_iff hndT).1 hget)
    have hk_eq : (k : A45) = (k' : A45) := by
      rw [hij] at hval
      exact mul_left_cancel hval
    exact Prod.ext hij (Subtype.ext hk_eq)
  have hcard := Nat.card_le_card_of_injective f hf_inj
  rw [Nat.card_prod, Nat.card_fin, hbadTrans_length, hCcard] at hcard
  omega

end Spin

end CFSG.RankThree.GF2n.Parrott
