module

public import Certificates.Kernel.BabyMonster.RangeChain
public import Certificates.Data.CFSGNative.CTIB.Census
public import CFSG.Certificates.Kernel.BabyMonster.Census.All
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check11
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check12
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check13
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check14
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check15
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check16
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check17
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check18
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check19
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check20
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check21
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check22
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check23
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check24
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check25
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Census.Check9
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelBM

open CFSG.KC.BM CFSG.Monster.B.CTIB.Native CFSG.Monster.B.CTIB.Kernel CFSG.Monster.B.Max2.Native

theorem reach_congr {act act' : Nat → Nat → Nat} {ngen : Nat} {valid : Nat → Bool}
    {root p : Nat} (h : Reach act ngen valid root p)
    (he : ∀ k < ngen, ∀ v, valid v = true → act k v = act' k v) :
    Reach act' ngen valid root p := by
  induction h with
  | root => exact .root
  | step k hk ha hb _ hab ih =>
    refine .step k hk ha hb ih ?_
    rw [← he k hk _ ha, ← he k hk _ hb]
    exact hab

theorem actPair_eq {M0 M1 : Nat} (h0 : rowsEq22 M0 r1Rows.toList = true)
    (h1 : rowsEq22 M1 r2Rows.toList = true) :
    ∀ k < 2, ∀ v, censusValid22 v = true → actPair M0 M1 k v = censusAct k v := by
  intro k hk v hv
  have hv' : v < 2 ^ 22 := by
    simp only [censusValid22, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.2
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [actPair, ite_eq_left rfl, vm32_eq_act22 h0 v hv', censusAct, ite_eq_left rfl]
  · rw [actPair, ite_eq_right Nat.one_ne_zero, vm32_eq_act22 h1 v hv', censusAct,
      ite_eq_right Nat.one_ne_zero]

theorem census_rec {LB DT : List (List Nat)} {Ts reps cs : List Nat} {M0 M1 M2 M3 : Nat}
    (t00 : byteTabOK M0 0 (nthN Ts 0) = true) (t01 : byteTabOK M0 1 (nthN Ts 1) = true)
    (t02 : byteTabOK M0 2 (nthN Ts 2) = true) (t10 : byteTabOK M1 0 (nthN Ts 3) = true)
    (t11 : byteTabOK M1 1 (nthN Ts 4) = true) (t12 : byteTabOK M1 2 (nthN Ts 5) = true)
    (t20 : byteTabOK M2 0 (nthN Ts 6) = true) (t21 : byteTabOK M2 1 (nthN Ts 7) = true)
    (t22 : byteTabOK M2 2 (nthN Ts 8) = true) (t30 : byteTabOK M3 0 (nthN Ts 9) = true)
    (t31 : byteTabOK M3 1 (nthN Ts 10) = true) (t32 : byteTabOK M3 2 (nthN Ts 11) = true)
    (hinv : andB (Nat.beq (mm32 (nat_lit 22) M0 M2) (id32 (nat_lit 22)))
      (Nat.beq (mm32 (nat_lit 22) M1 M3) (id32 (nat_lit 22))) = true)
    (hwf : andB (wf32 (nat_lit 22) M0) (andB (wf32 (nat_lit 22) M1)
      (andB (wf32 (nat_lit 22) M2) (wf32 (nat_lit 22) M3))) = true)
    (hr : AllRanges LB DT Ts reps 4096 0 cs 0 4194304) (hcs : noFailL cs = true) {a root size : Nat}
    (hc : censusRecOK LB reps cs a root size = true)
    (hlab : andB (censusValid22 root) (Nat.beq (lookLB LB root) a) = true)
    (h0 : rowsEq22 M0 r1Rows.toList = true) (h1 : rowsEq22 M1 r2Rows.toList = true) :
    OrbitList censusAct 2 (fun v => decide (0 < v) && decide (v < 2 ^ 22)) root size := by
  obtain ⟨ha, ha', hrt, hsz, hmin⟩ := censusRecOK_sound hc
  obtain ⟨pts, hlen, hnd, hroot, hval, hcl, hreach⟩ :=
    census_sound t00 t01 t02 t10 t11 t12 t20 t21 t22 t30 t31 t32 hinv hwf hr hcs ha ha'
      (by rw [hrt]; exact hlab)
  rw [hrt] at hroot hreach
  have he := actPair_eq h0 h1
  refine ⟨pts, hlen.trans hsz, hnd, hroot, fun p hp => ⟨(hval p hp).1, ?_⟩, fun p hp k hk => ?_,
    fun p hp => reach_congr (hreach p hp) he⟩
  · exact Nat.le_of_not_lt fun hlt => hmin p hlt (hval p hp).2
  · rw [← he k hk p (hval p hp).1]
    exact hcl p hp k hk

theorem census_orbitLists : ∀ r ∈ censusRecs,
    OrbitList censusAct 2 (fun v => decide (0 < v) && decide (v < 2 ^ 22)) r.1 r.2 := by
  bm_ranges hr CFSG.KC.BM.Census.r 1024
  intro r hr'
  simp only [censusRecs, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl
  · exact census_rec Census.tab0_0 Census.tab0_1 Census.tab0_2 Census.tab1_0 Census.tab1_1
      Census.tab1_2 Census.tab2_0 Census.tab2_1 Census.tab2_2 Census.tab3_0 Census.tab3_1
      Census.tab3_2 Census.inv (by quickRfl) hr (by quickRfl) (a := 1)
        (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
  · exact census_rec Census.tab0_0 Census.tab0_1 Census.tab0_2 Census.tab1_0 Census.tab1_1
      Census.tab1_2 Census.tab2_0 Census.tab2_1 Census.tab2_2 Census.tab3_0 Census.tab3_1
      Census.tab3_2 Census.inv (by quickRfl) hr (by quickRfl) (a := 2)
        (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
  · exact census_rec Census.tab0_0 Census.tab0_1 Census.tab0_2 Census.tab1_0 Census.tab1_1
      Census.tab1_2 Census.tab2_0 Census.tab2_1 Census.tab2_2 Census.tab3_0 Census.tab3_1
      Census.tab3_2 Census.inv (by quickRfl) hr (by quickRfl) (a := 3)
        (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
  · exact census_rec Census.tab0_0 Census.tab0_1 Census.tab0_2 Census.tab1_0 Census.tab1_1
      Census.tab1_2 Census.tab2_0 Census.tab2_1 Census.tab2_2 Census.tab3_0 Census.tab3_1
      Census.tab3_2 Census.inv (by quickRfl) hr (by quickRfl) (a := 4)
        (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
  · exact census_rec Census.tab0_0 Census.tab0_1 Census.tab0_2 Census.tab1_0 Census.tab1_1
      Census.tab1_2 Census.tab2_0 Census.tab2_1 Census.tab2_2 Census.tab3_0 Census.tab3_1
      Census.tab3_2 Census.inv (by quickRfl) hr (by quickRfl) (a := 5)
        (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

end CertificateChecks.KernelBM

end
