module

public import CFSG.Monster.B.GSide.HInnerFusionCertInputs
public import Certificates.Kernel.BabyMonster.CTIB.CosetQCount
public import Certificates.Kernel.BabyMonster.CTIB.CosetQ6
public import Certificates.Kernel.BabyMonster.CTIB.CosetQ8
public import Certificates.Kernel.BabyMonster.CTIB.CosetQ10

public section

namespace CertificateChecks.KernelBM.CTIB.CosetSq

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.KC.BM
  CFSG.KC.BM.CosetQ CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ
  CertificateChecks.KernelBM.CTIB.QK CertificateChecks.KernelBM.CTIB.Inner

@[expose] noncomputable def tbK (T k : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => Nat.ble (Nat.pow 2 k) (xorFields T (eV e)) && ih) L

theorem tbK_sound {T k : ℕ} : ∀ {L : List ℕ}, tbK T k L = true →
    ∀ e ∈ L, 2 ^ k ≤ xorFields T (eV e)
  | [], _, _, he => absurd he List.not_mem_nil
  | a :: L, h, e, he => by
    change (Nat.ble (Nat.pow 2 k) (xorFields T (eV a)) && tbK T k L) = true at h
    rw [Bool.and_eq_true, Nat.ble_eq] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact tbK_sound h.2 e he

@[expose] noncomputable def tb3 (L : List ℕ) : Bool := tbK T6 6 L && tbK T8 8 L && tbK T10 10 L

theorem tb_0 : tb3 o0w0 = true := by quickRfl
theorem tb_1 : tb3 o0w1 = true := by quickRfl
theorem tb_2 : tb3 o0w2 = true := by quickRfl
theorem tb_3 : tb3 o0w3 = true := by quickRfl
theorem tb_4 : tb3 o0w4 = true := by quickRfl
theorem tb_5 : tb3 o0w5 = true := by quickRfl
theorem tb_6 : tb3 o0w6 = true := by quickRfl
theorem tb_7 : tb3 o0w7 = true := by quickRfl

theorem tb_neg : tbK T6 6 [xorFields Bs6 1] = false := by decide +kernel

theorem tb_ok : ∀ e ∈ o0w, 2 ^ 6 ≤ xorFields T6 (eV e) ∧ 2 ^ 8 ≤ xorFields T8 (eV e) ∧
    2 ^ 10 ≤ xorFields T10 (eV e) := by
  have h3 : ∀ {L : List ℕ}, tb3 L = true → ∀ e ∈ L, 2 ^ 6 ≤ xorFields T6 (eV e) ∧
      2 ^ 8 ≤ xorFields T8 (eV e) ∧ 2 ^ 10 ≤ xorFields T10 (eV e) := fun h e he => by
    simp only [tb3, Bool.and_eq_true] at h
    exact ⟨tbK_sound h.1.1 e he, tbK_sound h.1.2 e he, tbK_sound h.2 e he⟩
  intro e he
  simp only [o0w, List.mem_append] at he
  rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he
  · exact h3 tb_0 e he
  · exact h3 tb_1 e he
  · exact h3 tb_2 e he
  · exact h3 tb_3 e he
  · exact h3 tb_4 e he
  · exact h3 tb_5 e he
  · exact h3 tb_6 e he
  · exact h3 tb_7 e he

theorem sq_not_one (hC : CensusLists) {AP k Bs T : ℕ} (hS : Setup (gArr ()) AP k Bs T)
    (hk : k ≤ 22) {w : ℕ} (hw : w = 0 ∨ w = 2 ^ 22)
    (hT : ∀ e ∈ o0w, 2 ^ k ≤ xorFields T (eV e)) (n : ℕ) :
    innerTy innerTab (qmul (gArr ()) w (qmul (gArr ()) (autApply (gArr ()) (arrOf AP) n) n)) ≠
      1 := by
  intro h
  have hu := o0_of_ty hC h
  have hv : n % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by decide)
  have hw0 : w % 2 ^ 22 = 0 := by rcases hw with rfl | rfl <;> rfl
  have e1 : qmul (gArr ()) w (qmul (gArr ()) (autApply (gArr ()) (arrOf AP) n) n) % 2 ^ 22 =
      mv (gArr ()) (arrOf AP) (n % 2 ^ 22) ^^^ n % 2 ^ 22 := by
    rw [qmul_mod, xor_mod, hw0, Nat.zero_xor, qmul_mod, xor_mod, mv_mod]
    rfl
  rw [e1, hS.nm _ hv] at hu
  have hc : xorFields T (n % 2 ^ 22) >>> (22 - k) < 2 ^ k := by
    have h1 := T_lt hS hv
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← Nat.pow_add, Nat.sub_add_cancel hk]
    exact h1
  obtain ⟨e, he, hev⟩ := List.mem_map.1 hu
  have h2 := hT e he
  rw [hev, hS.tb _ (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hk))] at h2
  omega

theorem lift6' : (liftImgsN 6).toArray = arrOf AH6 := by decide +kernel
theorem lift8' : (liftImgsN 8).toArray = arrOf AH8 := by decide +kernel
theorem lift10' : (liftImgsN 10).toArray = arrOf AH10 := by decide +kernel

theorem setup6 : Setup (gArr ()) AH6 6 Bs6 T6 := setup_of symG (by rw [← lo_eq]; exact cq6_setup)
theorem setup8 : Setup (gArr ()) AH8 8 Bs8 T8 := setup_of symG (by rw [← lo_eq]; exact cq8_setup)
theorem setup10 : Setup (gArr ()) AH10 10 Bs10 T10 :=
  setup_of symG (by rw [← lo_eq]; exact cq10_setup)

theorem all_of {AP k Bs T w : ℕ} (hC : CensusLists) (hS : Setup (gArr ()) AP k Bs T) (hk : k ≤ 22)
    (hw : w = 0 ∨ w = 2 ^ 22) (hT : ∀ e ∈ o0w, 2 ^ k ≤ xorFields T (eV e)) :
    Nat.all (2 ^ 23) (fun n _ => innerTy innerTab
      (qmul gArr w (qmul gArr (autApply gArr (arrOf AP) n) n)) != 1) = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨n, -⟩ -
  change (innerTy innerTab (qmul gArr w (qmul gArr (autApply gArr (arrOf AP) n) n)) != 1) = true
  rw [bne_iff_ne]
  exact sq_not_one hC hS hk hw hT n

theorem cosetSq (hC : CensusLists) : cosetSqOK innerTab = true := by
  simp only [cosetSqOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [lift6']
    exact all_of hC setup6 (by omega) (Or.inr rfl) fun e he => (tb_ok e he).1
  · rw [lift8']
    exact all_of hC setup8 (by omega) (Or.inl rfl) fun e he => (tb_ok e he).2.1
  · rw [lift10']
    exact all_of hC setup10 (by omega) (Or.inr rfl) fun e he => (tb_ok e he).2.2

@[expose] def fw : List ℕ :=
  [925867442304, 12917555815628, 195549060891108428, 485222172425660403, 3058683144775539]

theorem fw_ok : walksOK fw = true := by quickRfl

theorem fw_ty (hC : CensusLists) : innerTy innerTab 128 = 1 ∧ innerTy innerTab 1270988 = 2 ∧
    innerTy innerTab 5465164 = 3 ∧ innerTy innerTab 1255411 = 3 ∧
    innerTy innerTab 5449587 = 2 := by
  have h := walksOK_mem fw_ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact innerTy_walk hC (e := 925867442304) (h _ (by simp [fw])) (by decide) (by decide)
  · exact innerTy_walk hC (e := 12917555815628) (h _ (by simp [fw])) (by decide) (by decide)
  · exact innerTy_walk hC (e := 195549060891108428) (h _ (by simp [fw])) (by decide) (by decide)
  · exact innerTy_walk hC (e := 485222172425660403) (h _ (by simp [fw])) (by decide) (by decide)
  · exact innerTy_walk hC (e := 3058683144775539) (h _ (by simp [fw])) (by decide) (by decide)

theorem fw_q : qmul gArr 128 1270988 = 5465164 ∧ qmul gArr 128 1255411 = 5449587 := by
  decide +kernel

theorem fusionWitness (hC : CensusLists) : fusionWitnessOK innerTab = true := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := fw_ty hC
  obtain ⟨q1, q2⟩ := fw_q
  simp only [fusionWitnessOK, q1, q2, t1, t2, t3, t4, t5]
  decide +kernel

end CertificateChecks.KernelBM.CTIB.CosetSq

end
