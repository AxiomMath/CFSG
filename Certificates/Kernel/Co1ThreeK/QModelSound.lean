module

public import Certificates.Kernel.Co1ThreeK.FusionK
public import CFSG.Certificates.Kernel.Co1Three.QModelSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B

variable {M : Type*} [Group M]

structure QHyp (ι : M →* Matrix (Fin 24) (Fin 24) (ZMod 2)) (f : Nat → M) : Prop where
  inj : Function.Injective ι
  mat : ∀ k < 39, matK (TS k) = ι (f k)
  comm : ∀ x ∈ ([0, 1, 2, 3, 4, 5] : List Nat), ∀ y ∈ ([0, 1, 2, 3, 4, 5] : List Nat),
    Commute (f x) (f y)
  cube : ∀ x ∈ ([0, 1, 2, 3, 4, 5] : List Nat), f x ^ 3 = 1

@[expose] def eQ (f : Nat → M) (v : Nat) : M := epM f 3 [0, 1, 2, 3, 4, 5] v 1

@[expose] def mdlQ (f : Nat → M) (c : Nat) : M := f (12 + c / 729) * eQ f (c % 729)

variable {ι : M →* Matrix (Fin 24) (Fin 24) (ZMod 2)} {f : Nat → M}

theorem eQ_mat (H : QHyp ι f) (v : Nat) :
    epM (fun k => matK (TS k)) 3 [0, 1, 2, 3, 4, 5] v 1 = ι (eQ f v) := by
  have hG : ∀ g ∈ ([0, 1, 2, 3, 4, 5] : List Nat), g < 39 := by decide
  rw [eQ, ← epM_map ι f 3 _ v 1, map_one]
  exact epM_congr 3 _ (fun g hg => H.mat g (hG g hg)) v 1

theorem eQ_zero : eQ f 0 = 1 := epM_zero f 3 _

theorem eQ_add (H : QHyp ι f) (x y : Nat) : eQ f (addVK 3 6 x y) = eQ f x * eQ f y :=
  epM_addVK f (by norm_num) [0, 1, 2, 3, 4, 5] H.comm H.cube x y

theorem eQ_comm (H : QHyp ι f) (x y : Nat) : Commute (eQ f x) (eQ f y) := by
  have hx : ∀ g ∈ ([0, 1, 2, 3, 4, 5] : List Nat), Commute (eQ f x) (f g) := fun g hg =>
    (commute_epM f 3 (f g) _ (fun z hz => (H.comm g hg z hz)) x 1 (Commute.one_right _)).symm
  exact commute_epM f 3 (eQ f x) _ hx y 1 (Commute.one_right _)

theorem eQ_actK (H : QHyp ι f) (rows : List Nat) (v acc : Nat) :
    eQ f (actK 3 6 rows v acc) = eQ f acc * eQ f (actK 3 6 rows v 0) := by
  have e1 := epM_actK f (p := 3) (by norm_num) [0, 1, 2, 3, 4, 5] H.comm H.cube rows v acc
  have e0 := epM_actK f (p := 3) (by norm_num) [0, 1, 2, 3, 4, 5] H.comm H.cube rows v 0
  rw [epM_zero, one_mul] at e0
  change eQ f (actK 3 6 rows v acc) = eQ f acc * _ at e1
  change eQ f (actK 3 6 rows v 0) = _ at e0
  rw [e1, ← e0]

theorem f_twelve (H : QHyp ι f) : f 12 = 1 := by
  have h := kQTab
  simp only [Bool.and_eq_true] at h
  have e : TS 12 = oneK := Nat.eq_of_beq_eq_true h.1
  apply H.inj
  rw [← H.mat 12 (by norm_num), e, matK_oneK, map_one]

theorem norm_conj (H : QHyp ι f) {L : List (Nat × List Nat)} (hL : normK TS 3 EG L = true)
    {x : Nat × List Nat} (hx : x ∈ L) (hx39 : x.1 < 39) (v : Nat) :
    (f x.1)⁻¹ * eQ f v * f x.1 = eQ f (actK 3 6 x.2 v 0) := by
  obtain ⟨hl, h⟩ := normK_sound hL x hx
  have hr : ∀ j < x.2.length, f (([0, 1, 2, 3, 4, 5] : List Nat).getD j 0) * f x.1 =
      f x.1 * epM f 3 [0, 1, 2, 3, 4, 5] (x.2.getD j 0) 1 := by
    intro j hj
    apply H.inj
    have e := h j hj
    have hj6 : ([0, 1, 2, 3, 4, 5] : List Nat).getD j 0 < 39 := by
      by_cases hj' : j < 6
      · interval_cases j <;> decide
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        decide
    change matK (TS (([0, 1, 2, 3, 4, 5] : List Nat).getD j 0)) * matK (TS x.1) =
      matK (TS x.1) * epM (fun k => matK (TS k)) 3 [0, 1, 2, 3, 4, 5] (x.2.getD j 0) 1 at e
    rw [H.mat _ hj6, H.mat _ hx39, eQ_mat H] at e
    rw [map_mul, map_mul]
    exact e
  exact conj_actK f (by norm_num) [0, 1, 2, 3, 4, 5] H.comm H.cube (f x.1) x.2 hl hr v

theorem NT_mem : ∀ l < 27, (12 + l, getLL CS.TR l) ∈ NT := by decide +kernel

theorem NZ_memQ : ∀ j < 2, (9 + j, getLL QB j) ∈ NZ := by decide +kernel

theorem TR_lt : ∀ l < 27, ∀ r ∈ getLL CS.TR l, r < 729 := by decide +kernel

theorem t_conj (H : QHyp ι f) {l : Nat} (hl : l < 27) (v : Nat) :
    (f (12 + l))⁻¹ * eQ f v * f (12 + l) = eQ f (actK 3 6 (getLL CS.TR l) v 0) := by
  have h := kAct
  simp only [Bool.and_eq_true] at h
  exact norm_conj H h.2 (NT_mem l hl) (by simp only; omega) v

theorem q_conj (H : QHyp ι f) {j : Nat} (hj : j < 2) (v : Nat) :
    (f (9 + j))⁻¹ * eQ f v * f (9 + j) = eQ f (actK 3 6 (getLL QB j) v 0) := by
  have h := kNorm
  simp only [Bool.and_eq_true] at h
  exact norm_conj H h.2 (NZ_memQ j hj) (by simp only; omega) v

theorem termM_even (g : Nat → Matrix (Fin 24) (Fin 24) (ZMod 2)) (n : Nat) :
    termM g 3 EG (2 * n) = g n := by
  unfold termM
  rw [if_pos (Nat.mul_mod_right 2 n), Nat.mul_div_cancel_left n (by norm_num)]

theorem termM_odd (g : Nat → Matrix (Fin 24) (Fin 24) (ZMod 2)) (c : Nat) :
    termM g 3 EG (8 * c + 1) = epM g 3 [0, 1, 2, 3, 4, 5] c 1 := by
  unfold termM
  have h1 : (8 * c + 1) / 2 % 4 = 0 := by omega
  have h2 : (8 * c + 1) / 8 = c := by omega
  rw [if_neg (by omega), h1, h2]
  rfl

theorem q_rel (H : QHyp ι f) {k j : Nat} (hk : k < 27) (hj : j < 2) :
    getL 0 FM.RL (2 * k + j) < 729 * 27 ∧
      f (12 + k) * f (9 + j) = eQ f (getL 0 FM.RL (2 * k + j) % 729) *
        f (12 + getL 0 FM.RL (2 * k + j) / 729) := by
  have hR := kQRel
  simp only [Bool.and_eq_true] at hR
  have hE := kRel
  simp only [Bool.and_eq_true] at hE
  have hi : 2 * k + j < 2 * 27 := by omega
  obtain ⟨hlt, hq⟩ := relQK_spec hR.2 hi
  refine ⟨hlt, ?_⟩
  have hlen : CS.Q.length = 54 := Nat.eq_of_beq_eq_true hE.1
  have hmem : getLL CS.Q (2 * k + j) ∈ CS.Q := by
    rw [getLL_eq, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  obtain ⟨-, e⟩ := eqsK_sound hE.2 _ hmem
  rw [hq] at e
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e
  have h2 : (2 * k + j) / 2 = k := by omega
  have h3 : (2 * k + j) % 2 = j := by omega
  rw [h2, h3, termM_even, termM_even, termM_odd, termM_even] at e
  have hm : getL 0 FM.RL (2 * k + j) / 729 < 27 := Nat.div_lt_of_lt_mul hlt
  rw [H.mat _ (by omega), H.mat _ (by omega), eQ_mat H, H.mat _ (by omega), ← map_mul,
    ← map_mul] at e
  exact H.inj e

theorem t_prog (H : QHyp ι f) {l : Nat} (hl : l < 27) (h0 : Nat.land (getL 0 CS.W l) 1 = 0)
    (h3 : 3 ≤ Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575)
    (hi : Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575 - 3 < l)
    (hj : Nat.shiftRight (getL 0 CS.W l) 21 < 2) :
    f (12 + l) = f (12 + (Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575 - 3)) *
      f (9 + Nat.shiftRight (getL 0 CS.W l) 21) := by
  have h := kProg
  simp only [Bool.and_eq_true] at h
  have hlen : CS.W.length = 27 := Nat.eq_of_beq_eq_true h.1
  have hr := runK_sound h.2 l (by omega)
  rw [← CFSG.KC.Co1Cl.getL_eq] at hr
  have e := recK_mul hr h0
  have hS : ([9, 10, 11] : List Nat).length = 3 := rfl
  rw [hS] at e
  have e1 : refK [9, 10, 11] 3 12 (Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575) =
      12 + (Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575 - 3) := by
    unfold refK
    rw [nrec_eq, if_neg (by rw [Nat.blt_eq]; omega)]
    rfl
  have e2 : refK [9, 10, 11] 3 12 (Nat.shiftRight (getL 0 CS.W l) 21) =
      9 + Nat.shiftRight (getL 0 CS.W l) 21 := by
    unfold refK
    rw [nrec_eq, if_pos (by rw [Nat.blt_eq]; omega)]
    generalize Nat.shiftRight (getL 0 CS.W l) 21 = j at hj ⊢
    interval_cases j <;> rfl
  rw [e1, e2] at e
  apply H.inj
  rw [← H.mat _ (by omega), map_mul, ← H.mat _ (by omega), ← H.mat _ (by omega), e, matK_mulWK]

@[expose] noncomputable def TTe (k l : Nat) : Nat := getL 0 (getLL FM.TT k) l

theorem t_mul (H : QHyp ι f) :
    ∀ l < 27, ∀ k < 27, TTe k l < 729 * 27 ∧ f (12 + k) * f (12 + l) = mdlQ f (TTe k l) := by
  have hT := kQTab
  simp only [Bool.and_eq_true] at hT
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hl k hk
    obtain ⟨hlt, hcase⟩ := tabQK_spec hT.2 hk hl
    refine ⟨hlt, ?_⟩
    rcases hcase with ⟨rfl, he⟩ | ⟨hl0, h0, h3, hi, hj, he⟩
    · rw [TTe, he, mdlQ, Nat.mul_mod_right, eQ_zero, mul_one, Nat.mul_div_cancel_left k (by norm_num),
        Nat.add_zero, f_twelve H, mul_one]
    · set c := getL 0 CS.W l
      set i := Nat.land (Nat.shiftRight c 1) 1048575 - 3
      set j := Nat.shiftRight c 21
      obtain ⟨hti, hmi⟩ := ih i hi (by omega) k hk
      set t := getL 0 (getLL FM.TT k) i
      have ht : TTe k i = t := rfl
      rw [ht] at hti hmi
      have hm : t / 729 < 27 := Nat.div_lt_of_lt_mul hti
      obtain ⟨hr, hrel⟩ := q_rel H hm hj
      set r := getL 0 FM.RL (2 * (t / 729) + j)
      have hm' : r / 729 < 27 := Nat.div_lt_of_lt_mul hr
      have hb := actK_lt (n := 6) (show 0 < 3 by norm_num) (getLL QB j) (t % 729) 0 (by norm_num)
      have ha := actK_lt (n := 6) (show 0 < 3 by norm_num) (getLL CS.TR (r / 729)) (r % 729)
        (actK 3 6 (getLL QB j) (t % 729) 0) hb
      norm_num at ha
      have hE : TTe k l = 729 * (r / 729) +
          actK 3 6 (getLL CS.TR (r / 729)) (r % 729) (actK 3 6 (getLL QB j) (t % 729) 0) := he
      have hd : TTe k l / 729 = r / 729 := by omega
      have hmo : TTe k l % 729 =
          actK 3 6 (getLL CS.TR (r / 729)) (r % 729) (actK 3 6 (getLL QB j) (t % 729) 0) := by
        omega
      rw [mdlQ, hd, hmo, eQ_actK H, t_prog H hl h0 h3 hi hj, ← mul_assoc, hmi, mdlQ]
      have hq := q_conj H hj (t % 729)
      have ht' := t_conj H hm' (r % 729)
      calc f (12 + t / 729) * eQ f (t % 729) * f (9 + j)
          = f (12 + t / 729) * f (9 + j) * ((f (9 + j))⁻¹ * eQ f (t % 729) * f (9 + j)) := by group
        _ = eQ f (r % 729) * f (12 + r / 729) * eQ f (actK 3 6 (getLL QB j) (t % 729) 0) := by
          rw [hrel, hq]
        _ = f (12 + r / 729) * ((f (12 + r / 729))⁻¹ * eQ f (r % 729) * f (12 + r / 729)) *
            eQ f (actK 3 6 (getLL QB j) (t % 729) 0) := by group
        _ = f (12 + r / 729) * (eQ f (actK 3 6 (getLL QB j) (t % 729) 0) *
            eQ f (actK 3 6 (getLL CS.TR (r / 729)) (r % 729) 0)) := by
          rw [ht', mul_assoc, (eQ_comm H _ _).eq]

theorem mdlQ_mul (H : QHyp ι f) {x y : Nat} (hx : x < 729 * 27) (hy : y < 729 * 27) :
    mulQK FM.ADT FM.TT FM.AT x y < 729 * 27 ∧
      mdlQ f (mulQK FM.ADT FM.TT FM.AT x y) = mdlQ f x * mdlQ f y := by
  have hk : x / 729 < 27 := Nat.div_lt_of_lt_mul hx
  have hl : y / 729 < 27 := Nat.div_lt_of_lt_mul hy
  have e := mulQK_eq kQAdd kQAct TR_lt (TT := FM.TT) (x := x) hl
  obtain ⟨htt, hmt⟩ := t_mul H _ hl _ hk
  set t := TTe (x / 729) (y / 729)
  have ht : getL 0 (getLL FM.TT (x / 729)) (y / 729) = t := rfl
  rw [ht] at e
  have hm : t / 729 < 27 := Nat.div_lt_of_lt_mul htt
  have ha := addVK_lt (show 0 < 3 by norm_num) 6 (addVK 3 6 (t % 729) (y % 729))
    (actK 3 6 (getLL CS.TR (y / 729)) (x % 729) 0)
  norm_num at ha
  rw [e]
  refine ⟨by omega, ?_⟩
  have hd : (729 * (t / 729) + addVK 3 6 (addVK 3 6 (t % 729) (y % 729))
      (actK 3 6 (getLL CS.TR (y / 729)) (x % 729) 0)) / 729 = t / 729 := by omega
  have hmo : (729 * (t / 729) + addVK 3 6 (addVK 3 6 (t % 729) (y % 729))
      (actK 3 6 (getLL CS.TR (y / 729)) (x % 729) 0)) % 729 = addVK 3 6 (addVK 3 6 (t % 729)
        (y % 729)) (actK 3 6 (getLL CS.TR (y / 729)) (x % 729) 0) := by omega
  have hc := t_conj H hl (x % 729)
  rw [mdlQ, hd, hmo, eQ_add H, eQ_add H, mdlQ, mdlQ]
  calc f (12 + t / 729) * (eQ f (t % 729) * eQ f (y % 729) *
        eQ f (actK 3 6 (getLL CS.TR (y / 729)) (x % 729) 0))
      = mdlQ f t * (eQ f (actK 3 6 (getLL CS.TR (y / 729)) (x % 729) 0) * eQ f (y % 729)) := by
        rw [mdlQ]
        simp only [mul_assoc]
        rw [(eQ_comm H (y % 729) _).eq]
    _ = f (12 + x / 729) * f (12 + y / 729) *
        ((f (12 + y / 729))⁻¹ * eQ f (x % 729) * f (12 + y / 729) * eQ f (y % 729)) := by
        rw [hmt, hc]
    _ = f (12 + x / 729) * eQ f (x % 729) * (f (12 + y / 729) * eQ f (y % 729)) := by group

theorem kQFus' : ∀ k, 1 ≤ k → k < 27 →
    fusQK 27 FM.ADT FM.TT FM.AT FM.GC FM.RP FM.DP k (getLL FM.FT (k - 1)) = true := by
  have h := kQFus
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  rw [CFSG.KS.Raw.Orb.allBlk_eq, List.all_eq_true] at h2
  intro k hk1 hk2
  have := h2 (k - 1) (List.mem_range.2 (by omega))
  rwa [Nat.add_sub_cancel' hk1] at this

theorem GC_lt : ∀ g < FM.GC.length, getL 0 FM.GC g < 729 * 27 := by
  have h := kQGC
  simp only [Bool.and_eq_true] at h
  have hl : lenL FM.GC = 8 := Nat.eq_of_beq_eq_true h.1
  rw [CFSG.KC.Co1Cl.lenL_eq] at hl
  intro g hg
  have := CFSG.KS.Raw.Orb.allN_iff.1 h.2 g (by omega)
  rw [Nat.blt_eq] at this
  exact this

theorem fus_rep (H : QHyp ι f) (h1 : ∀ x < 729 * 27, mdlQ f x = 1 → x = 0) :
    ∀ x, 729 ≤ x → x < 729 * 27 → mdlQ f x ^ 3 = 1 → ∃ r ∈ FM.RP, IsConj (mdlQ f r) (mdlQ f x) :=
  fus_conj (FL := fun k => getLL FM.FT (k - 1)) (mdlQ f) (fun x y hx hy => mdlQ_mul H hx hy) h1
    GC_lt kQFus'

open CFSG.KS.SporSch.M24 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T in
theorem rep_root (H : QHyp ι f) {i : Nat} (hi : i < 42) :
    getL 0 Data.repRoot i < 3 ∧ getL 0 FM.RP i < 729 * 27 ∧
      lettersK 75 (getLL Data.repConj i) = true ∧
      matK (wordWK L.M L.MI (getLL Data.repConj i)) * ι (mdlQ f (getL 0 FM.RP i)) =
        matK (R.M (getL 0 Data.repRoot i)) * matK (wordWK L.M L.MI (getLL Data.repConj i)) := by
  have h := kQRep
  simp only [Bool.and_eq_true] at h
  have hi' := CFSG.KS.Raw.Orb.allN_iff.1 h.2 i hi
  simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at hi'
  obtain ⟨h1, h2, h3, h4⟩ := hi'
  rw [Nat.blt_eq] at h1 h2
  refine ⟨h2, h1, h3, ?_⟩
  have e := congrArg matK (Nat.eq_of_beq_eq_true h4)
  rw [matK_mulWK, matK_mulWK] at e
  have hm : matK (mdlK TS 3 729 12 (getLL EG 0) (getL 0 FM.RP i)) = ι (mdlQ f (getL 0 FM.RP i)) := by
    unfold mdlK
    rw [matK_mulWK, epK_mat, matK_oneK]
    change matK (TS (12 + getL 0 FM.RP i / 729)) *
      epM (fun k => matK (TS k)) 3 [0, 1, 2, 3, 4, 5] (getL 0 FM.RP i % 729) 1 = _
    rw [H.mat _ (by omega), eQ_mat H, ← map_mul]
    rfl
  rw [← hm]
  exact e

theorem TR_len : ∀ l < 27, (getLL CS.TR l).length = 6 := by decide +kernel

theorem TR_unit : ∀ l < 27, ∀ j < 6, actK 3 6 (getLL CS.TR l) (3 ^ j) 0 = (getLL CS.TR l).getD j 0 :=
  by decide +kernel

theorem TR_nodup : CS.TR.Nodup := by
  have h := kDist
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem TR_length : CS.TR.length = 27 := by
  have h := kAct
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem TR_inj {k l : Nat} (hk : k < 27) (hl : l < 27) (h : getLL CS.TR k = getLL CS.TR l) :
    k = l := by
  rw [getLL_eq, getLL_eq, List.getD_eq_getElem _ _ (by rw [TR_length]; exact hk),
    List.getD_eq_getElem _ _ (by rw [TR_length]; exact hl)] at h
  exact (TR_nodup.getElem_inj_iff).1 h

theorem mdlQ_inj (H : QHyp ι f) (he : ∀ v < 729, ∀ w < 729, eQ f v = eQ f w → v = w) {x y : Nat}
    (hx : x < 729 * 27) (hy : y < 729 * 27) (h : mdlQ f x = mdlQ f y) : x = y := by
  have hk : x / 729 < 27 := Nat.div_lt_of_lt_mul hx
  have hl : y / 729 < 27 := Nat.div_lt_of_lt_mul hy
  unfold mdlQ at h
  set z := eQ f (y % 729) * (eQ f (x % 729))⁻¹
  have hz : f (12 + x / 729) = f (12 + y / 729) * z := by
    rw [← mul_assoc, ← h]
    group
  have hzc : ∀ a, z⁻¹ * eQ f a * z = eQ f a := fun a => by
    have c1 : Commute (eQ f a) z := (eQ_comm H a _).mul_right (eQ_comm H a _).inv_right
    rw [mul_assoc, c1.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hact : ∀ u < 729, actK 3 6 (getLL CS.TR (x / 729)) u 0 = actK 3 6 (getLL CS.TR (y / 729)) u 0 := by
    intro u hu
    have h1 := actK_lt (n := 6) (show 0 < 3 by norm_num) (getLL CS.TR (x / 729)) u 0 (by norm_num)
    have h2 := actK_lt (n := 6) (show 0 < 3 by norm_num) (getLL CS.TR (y / 729)) u 0 (by norm_num)
    norm_num at h1 h2
    refine he _ h1 _ h2 ?_
    rw [← t_conj H hk, ← t_conj H hl, hz, mul_inv_rev]
    calc z⁻¹ * (f (12 + y / 729))⁻¹ * eQ f u * (f (12 + y / 729) * z)
        = z⁻¹ * ((f (12 + y / 729))⁻¹ * eQ f u * f (12 + y / 729)) * z := by group
      _ = (f (12 + y / 729))⁻¹ * eQ f u * f (12 + y / 729) := by
        rw [t_conj H hl, hzc]
  have hrows : getLL CS.TR (x / 729) = getLL CS.TR (y / 729) := by
    refine List.ext_getElem (by rw [TR_len _ hk, TR_len _ hl]) fun j h1 h2 => ?_
    have hj : j < 6 := by rw [TR_len _ hk] at h1; exact h1
    have := hact (3 ^ j) (by interval_cases j <;> norm_num)
    rw [TR_unit _ hk _ hj, TR_unit _ hl _ hj, List.getD_eq_getElem _ _ h1,
      List.getD_eq_getElem _ _ h2] at this
    exact this
  have hkl := TR_inj hk hl hrows
  rw [hkl, mul_right_inj] at h
  have hvw := he _ (Nat.mod_lt x (by norm_num)) _ (Nat.mod_lt y (by norm_num)) h
  rw [← Nat.div_add_mod x 729, ← Nat.div_add_mod y 729, hkl, hvw]

theorem mdlQ_zero (H : QHyp ι f) : mdlQ f 0 = 1 := by
  rw [mdlQ, Nat.zero_div, Nat.zero_mod, Nat.add_zero, f_twelve H, eQ_zero, mul_one]

theorem mdlQ_eq_one (H : QHyp ι f) (he : ∀ v < 729, ∀ w < 729, eQ f v = eQ f w → v = w) {x : Nat}
    (hx : x < 729 * 27) (h : mdlQ f x = 1) : x = 0 :=
  mdlQ_inj H he hx (by norm_num) (by rw [h, mdlQ_zero H])

open Classical in
@[expose] noncomputable def codeSet (f : Nat → M) : Set M :=
  ((Finset.range (729 * 27)).image (mdlQ f) : Set M)

theorem mem_codeSet {g : M} : g ∈ codeSet f ↔ ∃ c < 729 * 27, mdlQ f c = g := by
  classical
  rw [codeSet, Finset.coe_image, Set.mem_image]
  simp only [Finset.coe_range, Set.mem_Iio]

theorem codeSet_mul (H : QHyp ι f) {g h : M} (hg : g ∈ codeSet f) (hh : h ∈ codeSet f) :
    g * h ∈ codeSet f := by
  obtain ⟨x, hx, rfl⟩ := mem_codeSet.1 hg
  obtain ⟨y, hy, rfl⟩ := mem_codeSet.1 hh
  obtain ⟨h1, h2⟩ := mdlQ_mul H hx hy
  exact mem_codeSet.2 ⟨_, h1, h2⟩

theorem codeSet_one (H : QHyp ι f) : (1 : M) ∈ codeSet f :=
  mem_codeSet.2 ⟨0, by norm_num, mdlQ_zero H⟩

theorem codeSet_pow (H : QHyp ι f) {g : M} (hg : g ∈ codeSet f) : ∀ n : Nat, g ^ n ∈ codeSet f
  | 0 => by rw [pow_zero]; exact codeSet_one H
  | n + 1 => by rw [pow_succ]; exact codeSet_mul H (codeSet_pow H hg n) hg

theorem codeSet_inv (H : QHyp ι f) {g : M} (hg : g ∈ codeSet f) : g⁻¹ ∈ codeSet f := by
  obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => g ^ n)
    (codeSet_pow H hg) (by rw [codeSet]; exact Finset.finite_toSet _)
  have hb : g ^ b = g ^ a * g ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
  have h1 : g ^ (b - a) = 1 := by
    have e : g ^ a * g ^ (b - a) = g ^ a * 1 := by rw [mul_one, ← hb]; exact he.symm
    exact mul_left_cancel e
  have h2 : g * g ^ (b - a - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.sub_pos_of_lt hab), h1]
  rw [inv_eq_of_mul_eq_one_right h2]
  exact codeSet_pow H hg _

@[expose] noncomputable def codeSub (H : QHyp ι f) : Subgroup M where
  carrier := codeSet f
  mul_mem' := codeSet_mul H
  one_mem' := codeSet_one H
  inv_mem' := codeSet_inv H

theorem card_codeSub (H : QHyp ι f) (he : ∀ v < 729, ∀ w < 729, eQ f v = eQ f w → v = w) :
    Nat.card (codeSub H) = 3 ^ 9 := by
  have e : Nat.card (codeSub H) = (codeSet f).ncard := Nat.card_coe_set_eq (codeSet f)
  classical
  rw [e, codeSet, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  · norm_num
  intro x hx y hy hxy
  exact mdlQ_inj H he (Finset.mem_range.1 hx) (Finset.mem_range.1 hy) hxy

theorem eQ_mem_codeSet (H : QHyp ι f) {v : Nat} (hv : v < 729) : eQ f v ∈ codeSet f := by
  refine mem_codeSet.2 ⟨v, by omega, ?_⟩
  rw [mdlQ, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hv, Nat.add_zero, f_twelve H, one_mul]

theorem t_mem_codeSet (H : QHyp ι f) {k : Nat} (hk : k < 27) : f (12 + k) ∈ codeSet f := by
  refine mem_codeSet.2 ⟨729 * k, by omega, ?_⟩
  rw [mdlQ, Nat.mul_div_cancel_left k (by norm_num), Nat.mul_mod_right, eQ_zero, mul_one]

theorem q_mem_codeSet (H : QHyp ι f) {j : Nat} (hj : j < 2) : f (9 + j) ∈ codeSet f := by
  obtain ⟨hr, e⟩ := q_rel H (k := 0) (by norm_num) hj
  rw [Nat.add_zero, f_twelve H, one_mul, Nat.mul_zero, Nat.zero_add] at e
  rw [Nat.mul_zero, Nat.zero_add] at hr
  rw [e]
  refine codeSet_mul H (eQ_mem_codeSet H (Nat.mod_lt _ (by norm_num))) (t_mem_codeSet H ?_)
  exact Nat.div_lt_of_lt_mul hr

theorem a_mem_codeSet (H : QHyp ι f) {i : Nat} (hi : i < 6) : f i ∈ codeSet f := by
  have e : eQ f (3 ^ i) = f i := by
    interval_cases i <;> simp [eQ, epM]
  rw [← e]
  exact eQ_mem_codeSet H (by interval_cases i <;> norm_num)

theorem closure_le_codeSub (H : QHyp ι f) :
    Subgroup.closure ({f 0, f 1, f 2, f 3, f 4, f 5, f 9, f 10} : Set M) ≤ codeSub H := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a_mem_codeSet H (i := 0) (by norm_num)
  · exact a_mem_codeSet H (i := 1) (by norm_num)
  · exact a_mem_codeSet H (i := 2) (by norm_num)
  · exact a_mem_codeSet H (i := 3) (by norm_num)
  · exact a_mem_codeSet H (i := 4) (by norm_num)
  · exact a_mem_codeSet H (i := 5) (by norm_num)
  · exact q_mem_codeSet H (j := 0) (by norm_num)
  · exact q_mem_codeSet H (j := 1) (by norm_num)

theorem eQ_mem_closure {K : Subgroup M} (hK : ∀ i < 6, f i ∈ K) (v : Nat) : eQ f v ∈ K := by
  have key : ∀ (G : List Nat), (∀ x ∈ G, f x ∈ K) → ∀ (v : Nat) (acc : M),
      acc ∈ K → epM f 3 G v acc ∈ K := by
    intro G
    induction G with
    | nil => intro _ v acc h; exact h
    | cons g G ih =>
      intro hG v acc h
      exact ih (fun x hx => hG x (List.mem_cons_of_mem g hx)) _ _
        (K.mul_mem h (K.pow_mem (hG g List.mem_cons_self) _))
  refine key _ (fun x hx => hK x ?_) v 1 K.one_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem t_mem_closure (H : QHyp ι f) {K : Subgroup M} (h9 : f 9 ∈ K) (h10 : f 10 ∈ K) :
    ∀ l < 27, f (12 + l) ∈ K := by
  have hT := kQTab
  simp only [Bool.and_eq_true] at hT
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hl
    rcases (tabQK_spec hT.2 (k := 0) (by norm_num) hl).2 with ⟨rfl, -⟩ | ⟨-, h0, h3, hi, hj, -⟩
    · rw [Nat.add_zero, f_twelve H]
      exact K.one_mem
    · rw [t_prog H hl h0 h3 hi hj]
      refine K.mul_mem (ih _ hi (by omega)) ?_
      generalize Nat.shiftRight (getL 0 CS.W l) 21 = j at hj ⊢
      interval_cases j
      · exact h9
      · exact h10

theorem codeSub_le_closure (H : QHyp ι f) :
    codeSub H ≤ Subgroup.closure ({f 0, f 1, f 2, f 3, f 4, f 5, f 9, f 10} : Set M) := by
  set K := Subgroup.closure ({f 0, f 1, f 2, f 3, f 4, f 5, f 9, f 10} : Set M)
  have hK : ∀ x ∈ ({f 0, f 1, f 2, f 3, f 4, f 5, f 9, f 10} : Set M), x ∈ K := fun x hx =>
    Subgroup.subset_closure hx
  have ha : ∀ i < 6, f i ∈ K := by
    intro i hi
    apply hK
    interval_cases i <;> simp
  intro g hg
  have hg' : g ∈ codeSet f := hg
  obtain ⟨c, hc, rfl⟩ := mem_codeSet.1 hg'
  refine K.mul_mem (t_mem_closure H (hK _ (by simp)) (hK _ (by simp)) _
    (Nat.div_lt_of_lt_mul hc)) (eQ_mem_closure ha _)

theorem card_closure (H : QHyp ι f) (he : ∀ v < 729, ∀ w < 729, eQ f v = eQ f w → v = w) :
    Nat.card (Subgroup.closure ({f 0, f 1, f 2, f 3, f 4, f 5, f 9, f 10} : Set M)) = 3 ^ 9 := by
  rw [le_antisymm (closure_le_codeSub H) (codeSub_le_closure H)]
  exact card_codeSub H he

end CertificateChecks.KernelCo1ThreeK

end
