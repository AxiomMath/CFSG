module

public import Certificates.Kernel.BabyMonster.CTIB.HistSum
public import Certificates.Kernel.BabyMonster.CTIB.HistN

public section

namespace CertificateChecks.KernelBM.CTIB.Hist

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.KC.Bfs CertificateChecks.KernelBM.CTIB
  CertificateChecks.KernelBM.CTIB.CosetQ CertificateChecks.KernelBM.CTIB.QK
  CertificateChecks.KernelBM.CTIB.Inner

open Classical

attribute [local irreducible] S cnt

theorem fold_hist (key : ℕ → ℕ) (hk : ∀ n, key n < 10) : ∀ N,
    Nat.fold N (fun n _ h => h.modify (key n) (· + 1)) (Array.replicate 10 0) =
      Array.ofFn (fun j : Fin 10 => ((Finset.range N).filter fun n => key n = j.1).card)
  | 0 => by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp
  | N + 1 => by
    rw [Nat.fold_succ, fold_hist key hk N]
    apply Array.ext
    · simp
    · intro i h1 h2
      have hi : i < 10 := by simpa using h2
      rw [Array.getElem_modify, Array.getElem_ofFn, Array.getElem_ofFn, Finset.range_add_one,
        Finset.filter_insert]
      by_cases e : key N = i
      · rw [ite_eq_left e, ite_eq_left e, Finset.card_insert_of_notMem (by simp)]
      · rw [ite_eq_right e, ite_eq_right e]

theorem key_lt (t : Array ℕ) (n : ℕ) : innerKey t n < 10 := by
  unfold innerKey innerPairIdx
  split_ifs <;> omega

theorem comm_iff (a b : ℕ) : qmul gArr a b = qmul gArr b a ↔ bt a b = false := by
  constructor
  · intro h
    have h22 := congrArg (fun x => x.testBit 22) h
    simp only [qmul_bit22] at h22
    rw [bt]
    cases ha : a.testBit 22 <;> cases hb : b.testBit 22 <;> rw [ha, hb] at h22 <;>
      simp_all
  · intro h
    refine code_ext (qmul_lt _ _ _) (qmul_lt _ _ _) (fun i hi => ?_) ?_
    · rw [qmul_bit _ _ _ hi, qmul_bit _ _ _ hi, Bool.xor_comm]
    · rw [qmul_bit22, qmul_bit22, Bool.xor_comm (a.testBit 22)]
      rw [bt] at h
      cases h1 : corr gArr a b <;> cases h2 : corr gArr b a <;> rw [h1, h2] at h <;> simp_all

theorem bt_mod (a b : ℕ) : bt (a % 2 ^ 22) b = bt a b := by
  have hc : ∀ j < 22, (a % 2 ^ 22).testBit j = a.testBit j := fun j hj => by
    rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
  rw [bt, bt, corr_congr _ hc fun _ _ => rfl, corr_congr _ (fun _ _ => rfl) hc]

theorem key_eq {v : ℕ} (hv2 : 2 ≤ v) (hv : v < 2 ^ 22) {n : ℕ} (hn : n % 2 ^ 22 = v) :
    innerKey innerTab n = K v := by
  have hv0 : v ≠ 0 := by omega
  have hq : qmul gArr 1 n % 2 ^ 22 = v ^^^ 1 := by
    rw [qmul_mod]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← hn]
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hi : i < 22
    · simp [hi, Bool.xor_comm]
    · have : i ≠ 0 := by omega
      simp only [hi, decide_false, Bool.false_and]
      rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow this)]
      rfl
  have hq0 : v ^^^ 1 ≠ 0 := fun h => by
    have := Nat.eq_of_xor_eq_zero h
    omega
  have hb : bt n 1 = bt v 1 := by rw [← hn, bt_mod]
  unfold innerKey K
  by_cases hc : qmul gArr n 1 = qmul gArr 1 n
  · have hbf : bt v 1 = false := hb ▸ (comm_iff n 1).1 hc
    simp only [hc, hbf, innerTy, hn, hq, hv0, hq0, ↓reduceIte]
    rfl
  · have hbt : bt v 1 = true := by
      rw [← hb]
      cases h : bt n 1
      · exact absurd ((comm_iff n 1).2 h) hc
      · rfl
    simp only [hc, hbt, ↓reduceIte]

theorem q_lits : qmul gArr 0 1 = 1 ∧ qmul gArr 1 0 = 1 ∧ qmul gArr 1 1 = 0 ∧
    qmul gArr 4194304 1 = 4194305 ∧ qmul gArr 1 4194304 = 4194305 ∧
    qmul gArr 4194305 1 = 4194304 ∧ qmul gArr 1 4194305 = 4194304 := by
  simp only [← mulQ_eq]
  decide +kernel

theorem keys_special (hC : CensusLists) : innerKey innerTab 0 = 7 ∧ innerKey innerTab 1 = 8 ∧
    innerKey innerTab 4194304 = 1 ∧ innerKey innerTab 4194305 = 2 := by
  have t1 : innerTab[1]! = 1 := tab_S hC (by omega) (one_mem hC)
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := q_lits
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [innerKey, innerTy, q1, q2, q3, q4, q5, q6, q7, t1] <;> decide

@[expose] def Nn (b c : ℕ) : ℕ := (Ntab.getD b []).getD c 0

@[expose] def Tn (b : ℕ) : ℕ :=
  Inner.sizeOf b - (if b = 0 then 1 else 0) - ∑ c ∈ Finset.range 5, Nn b c

@[expose] def Cn (j : ℕ) : ℕ :=
  (if 7 = j then 1 else 0) + (if 8 = j then 1 else 0) + (if 1 = j then 1 else 0) +
    (if 2 = j then 1 else 0) + 2 * ∑ b ∈ Finset.range 5,
      ((if j = 0 then Tn b else 0) + ∑ c ∈ Finset.range 5, (if pi b c = j then Nn b c else 0))

theorem Cn_vals : ∀ j < 10, Cn j =
    [4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0].getD j 0 := by
  decide

section Census

variable (hC : CensusLists)
include hC

theorem T_eq {b : ℕ} (hb : b < 5) : T b = Tn b := by
  have h := size_split hC hb
  rw [Finset.sum_congr rfl fun c hc => N_eq hC hb (Finset.mem_range.1 hc)] at h
  rw [Tn]
  change _ = _ - _ - ∑ c ∈ Finset.range 5, (Ntab.getD b []).getD c 0
  omega

theorem orbit_keys {b j : ℕ} (hb : b < 5) {f : ℕ → ℕ} (hf : ∀ v, 2 ≤ v → v < 2 ^ 22 → f v = K v) :
    ((S b).filter fun v => f v = j).card = (if b = 0 ∧ f 1 = j then 1 else 0) +
      ((S b).filter fun v => v ≠ 1 ∧ K v = j).card := by
  have pt : ∀ v ∈ S b, (if f v = j then 1 else 0) =
      (if v = 1 then (if b = 0 ∧ f 1 = j then 1 else 0) else 0) +
        (if v ≠ 1 ∧ K v = j then 1 else 0) := by
    intro v hv
    have hvv := S_valid hC hb hv
    by_cases h1 : v = 1
    · subst h1
      have hb0 : b = 0 := S_disj hC hb (by omega) hv (one_mem hC)
      simp [hb0]
    · rw [ite_eq_right h1, hf v (by omega) hvv.2]
      simp [h1]
  rw [Finset.card_filter, Finset.sum_congr rfl pt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.card_filter]
  congr 1
  by_cases hb0 : b = 0
  · subst hb0
    rw [ite_eq_left (one_mem hC)]
  · rw [ite_eq_right fun h => hb0 (S_disj hC hb (by omega) h (one_mem hC))]
    simp [hb0]

theorem count_eq (j : ℕ) :
    ((Finset.range (2 ^ 23)).filter fun n => innerKey innerTab n = j).card = Cn j := by
  obtain ⟨k0, k1, kx, kx1⟩ := keys_special hC
  have hsplit : ((Finset.range (2 ^ 23)).filter fun n => innerKey innerTab n = j).card =
      ((Finset.range (2 ^ 22)).filter fun v => innerKey innerTab v = j).card +
        ((Finset.range (2 ^ 22)).filter fun v => innerKey innerTab (2 ^ 22 + v) = j).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
      show 2 ^ 23 = 2 ^ 22 + 2 ^ 22 by norm_num, Finset.sum_range_add]
  have half : ∀ {f : ℕ → ℕ}, (∀ v, 2 ≤ v → v < 2 ^ 22 → f v = K v) →
      ((Finset.range (2 ^ 22)).filter fun v => f v = j).card = (if f 0 = j then 1 else 0) +
        (if f 1 = j then 1 else 0) + ∑ b ∈ Finset.range 5,
          ((if j = 0 then Tn b else 0) + ∑ c ∈ Finset.range 5, (if pi b c = j then Nn b c else 0)) := by
    intro f hf
    rw [range_split hC, Finset.sum_congr rfl fun b hb => orbit_keys hC (Finset.mem_range.1 hb) hf,
      Finset.sum_add_distrib, Finset.sum_congr rfl fun b hb => countK hC (Finset.mem_range.1 hb)]
    have e1 : ∑ b ∈ Finset.range 5, (if b = 0 ∧ f 1 = j then 1 else 0) = if f 1 = j then 1 else 0 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      by_cases h : f 1 = j <;> simp [h]
    have hB : ∑ b ∈ Finset.range 5, ((if j = 0 then T b else 0) + ∑ c ∈ Finset.range 5,
        (if pi b c = j then cnt (Rc c) b 1 else 0)) = ∑ b ∈ Finset.range 5,
          ((if j = 0 then Tn b else 0) + ∑ c ∈ Finset.range 5, (if pi b c = j then Nn b c else 0)) :=
      Finset.sum_congr rfl fun b hb => by
        rw [T_eq hC (Finset.mem_range.1 hb), Finset.sum_congr rfl fun c hc => by
          rw [N_eq hC (Finset.mem_range.1 hb) (Finset.mem_range.1 hc)]]
        rfl
    rw [e1, hB, Nat.add_assoc]
  rw [hsplit, half fun v h2 h => key_eq h2 h (Nat.mod_eq_of_lt h),
    half fun v h2 h => key_eq h2 h (by rw [Nat.add_mod_left, Nat.mod_eq_of_lt h]), Cn]
  have kx' : innerKey innerTab (2 ^ 22 + 0) = 1 := kx
  have kx1' : innerKey innerTab (2 ^ 22 + 1) = 2 := kx1
  simp only [k0, k1, kx', kx1']
  omega

theorem hist :
    innerHist innerTab = #[4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0] := by
  rw [innerHist, fold_hist _ (key_lt innerTab)]
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < 10 := by simpa using h1
    rw [Array.getElem_ofFn, count_eq hC, Cn_vals i hi]
    interval_cases i <;> rfl

end Census

theorem tabOK (hC : CensusLists) : innerTabOK innerTab = true := by
  rw [innerTabOK, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [Array.all_eq_true]
  intro i hi
  have hm : (natBfs censusAct 2 (rootOf k) (Inner.sizeOf k + 1)).1[i] ∈
      (natBfs censusAct 2 (rootOf k) (Inner.sizeOf k + 1)).1 := Array.getElem_mem hi
  rw [beq_iff_eq]
  exact (innerTab_facts hC).2.1 k hk _ (((natBfs_census hC hk).1 _).1 hm)

theorem orbOK (hC : CensusLists) : innerOrbOK () = true := by
  rw [innerOrbOK, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  obtain ⟨S', hS, hcard, hv, -⟩ := census_orbit hC hk
  exact orbitOK_of_reach S' hS (fun x hx => (hv x hx).1) hcard (fun x hx => (hv x hx).2)

@[expose] def RW : List ℕ :=
  [15357125328898, 193508409348, 3286019080224, 51501456179200, 59006912315392, 4194307,
   104827841413125, 4424156326133793, 6187427265789953, 59006950064129, 487595360387078,
   417117128114208, 557105145462816, 246254672805888, 8388615, 192933503149555745,
   48250818797518881, 1078284274736300033, 276373155626090528, 60435720473149473, 1]

theorem RW_ok : walksOK RW = true := by quickRfl

theorem ty_of (hC : CensusLists) {e n : ℕ} (he : e ∈ RW) (h : n % 2 ^ 22 = eV e ∧ eV e ≠ 0) :
    innerTy innerTab n = eRec e + 1 :=
  innerTy_walk hC (walksOK_mem RW_ok e he) h.1 h.2

theorem q1_lits : qmul gArr 1 2 = 3 ∧ qmul gArr 1 4 = 5 ∧ qmul gArr 1 32 = 33 ∧
    qmul gArr 1 16384 = 16385 ∧ qmul gArr 1 802816 = 802817 ∧ qmul gArr 1 6 = 7 ∧
    qmul gArr 1 16416 = 16417 ∧ qmul gArr 1 802848 = 802849 ∧ qmul gArr 1 786432 = 786433 ∧
    qmul gArr 1 786464 = 786465 ∧ qmul gArr 1 (2 ^ 22) = 4194305 := by
  simp only [← mulQ_eq]
  decide +kernel

theorem repsOK (hC : CensusLists) : innerRepsOK innerTab = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := q1_lits
  have t2 : innerTy innerTab 2 = 1 := (ty_of hC (e := 15357125328898) (by simp [RW]) (by decide)).trans (by decide)
  have t4 : innerTy innerTab 4 = 1 := (ty_of hC (e := 193508409348) (by simp [RW]) (by decide)).trans (by decide)
  have t32 : innerTy innerTab 32 = 1 := (ty_of hC (e := 3286019080224) (by simp [RW]) (by decide)).trans (by decide)
  have t16384 : innerTy innerTab 16384 = 1 := (ty_of hC (e := 51501456179200) (by simp [RW]) (by decide)).trans (by decide)
  have t802816 : innerTy innerTab 802816 = 1 := (ty_of hC (e := 59006912315392) (by simp [RW]) (by decide)).trans (by decide)
  have t3 : innerTy innerTab 3 = 2 := (ty_of hC (e := 4194307) (by simp [RW]) (by decide)).trans (by decide)
  have t5 : innerTy innerTab 5 = 2 := (ty_of hC (e := 104827841413125) (by simp [RW]) (by decide)).trans (by decide)
  have t33 : innerTy innerTab 33 = 2 := (ty_of hC (e := 4424156326133793) (by simp [RW]) (by decide)).trans (by decide)
  have t16385 : innerTy innerTab 16385 = 2 := (ty_of hC (e := 6187427265789953) (by simp [RW]) (by decide)).trans (by decide)
  have t802817 : innerTy innerTab 802817 = 2 := (ty_of hC (e := 59006950064129) (by simp [RW]) (by decide)).trans (by decide)
  have t6 : innerTy innerTab 6 = 2 := (ty_of hC (e := 487595360387078) (by simp [RW]) (by decide)).trans (by decide)
  have t16416 : innerTy innerTab 16416 = 2 := (ty_of hC (e := 417117128114208) (by simp [RW]) (by decide)).trans (by decide)
  have t802848 : innerTy innerTab 802848 = 2 := (ty_of hC (e := 557105145462816) (by simp [RW]) (by decide)).trans (by decide)
  have t786432 : innerTy innerTab 786432 = 2 := (ty_of hC (e := 246254672805888) (by simp [RW]) (by decide)).trans (by decide)
  have t7 : innerTy innerTab 7 = 3 := (ty_of hC (e := 8388615) (by simp [RW]) (by decide)).trans (by decide)
  have t16417 : innerTy innerTab 16417 = 3 := (ty_of hC (e := 192933503149555745) (by simp [RW]) (by decide)).trans (by decide)
  have t802849 : innerTy innerTab 802849 = 3 := (ty_of hC (e := 48250818797518881) (by simp [RW]) (by decide)).trans (by decide)
  have t786433 : innerTy innerTab 786433 = 3 := (ty_of hC (e := 1078284274736300033) (by simp [RW]) (by decide)).trans (by decide)
  have t786464 : innerTy innerTab 786464 = 3 := (ty_of hC (e := 276373155626090528) (by simp [RW]) (by decide)).trans (by decide)
  have t786465 : innerTy innerTab 786465 = 3 := (ty_of hC (e := 60435720473149473) (by simp [RW]) (by decide)).trans (by decide)
  have t4194305 : innerTy innerTab 4194305 = 1 := (ty_of hC (e := 1) (by simp [RW]) (by decide)).trans (by decide)
  have tx : innerTy innerTab (2 ^ 22) = 6 := by simp [innerTy]
  simp only [innerRepsOK, List.all_cons, List.all_nil, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, t2, t4, t32, t16384, t802816, t3, t5, t33, t16385, t802817, t6, t16416, t802848, t786432,
    t7, t16417, t802849, t786433, t786464, t786465, t4194305, tx]
  simp only [← mulQ_eq]
  decide +kernel

end CertificateChecks.KernelBM.CTIB.Hist

end
