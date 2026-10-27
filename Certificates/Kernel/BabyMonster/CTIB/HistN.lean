module

public import Certificates.Kernel.BabyMonster.CTIB.Hist
public import Certificates.Kernel.BabyMonster.CTIB.HistData
public import Certificates.Kernel.BabyMonster.CTIB.Orbit0

public section

namespace CertificateChecks.KernelBM.CTIB.Hist

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.KC.Bfs CertificateChecks.KernelBM.CTIB.Inner

open Classical

@[expose] def hwA (a : ℕ) : List ℕ :=
  if a = 0 then hw0_0 ++ hw0_1 ++ hw0_2 ++ hw0_3 ++ hw0_4 ++ hw0_5 ++ hw0_6 ++ hw0_7
  else if a = 1 then hw1_0 ++ hw1_1 ++ hw1_2 ++ hw1_3 ++ hw1_4 ++ hw1_5 ++ hw1_6 ++ hw1_7
  else if a = 2 then hw2_0 ++ hw2_1 ++ hw2_2 ++ hw2_3 ++ hw2_4 ++ hw2_5 ++ hw2_6 ++ hw2_7
  else if a = 3 then hw3_0 ++ hw3_1 ++ hw3_2 ++ hw3_3 ++ hw3_4 ++ hw3_5 ++ hw3_6 ++ hw3_7
  else hw4_0 ++ hw4_1 ++ hw4_2 ++ hw4_3 ++ hw4_4 ++ hw4_5 ++ hw4_6 ++ hw4_7

theorem za_0 : zall 1 o0w (hwA 0) = true := by decide +kernel
theorem za_1 : zall 3 o0w (hwA 1) = true := by decide +kernel
theorem za_2 : zall 7 o0w (hwA 2) = true := by decide +kernel
theorem za_3 : zall 17 o0w (hwA 3) = true := by decide +kernel
theorem za_4 : zall 19 o0w (hwA 4) = true := by decide +kernel

theorem za_neg : zall 1 o0w (hwA 1) = false := by decide +kernel

@[expose] def Gtab : List (List ℕ) :=
  [[0, 891, 0, 0, 0], [44, 0, 1232, 0, 0], [0, 28, 1120, 0, 0], [0, 0, 0, 840, 324],
    [0, 0, 0, 1100, 0]]

theorem gc_ok : ∀ a < 5, ∀ c < 5, zcnt c o0w (hwA a) = (Gtab.getD a []).getD c 0 := by
  decide +kernel

theorem za_ok : ∀ a < 5, zall (rootOf a) o0w (hwA a) = true := by
  intro a ha
  interval_cases a
  · exact za_0
  · exact za_1
  · exact za_2
  · exact za_3
  · exact za_4

theorem S0_eq (hC : CensusLists) : S 0 = (o0w.map eV).toFinset := by
  obtain ⟨r, -, -⟩ := incK_sound o0w 0 o0_inc
  ext x
  rw [mem_S hC (by omega), List.mem_toFinset]
  refine ⟨o0_mem hC, fun h => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  have hw := o0_walks e he
  simp only [walkOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
  rw [← hw.2, eWalk, r e he, rootsL_eq 0 (by omega)]
  exact reach_walk _ _ _

theorem o0_nodup : (o0w.map eV).Nodup := by
  obtain ⟨-, p, -⟩ := incK_sound o0w 0 o0_inc
  exact p.imp fun h => Nat.ne_of_lt h

theorem cnt0_eq (hC : CensusLists) {a c : ℕ} (ha : a < 5) (hc : c < 5) :
    cnt (Rc c) 0 (rootOf a) = (Gtab.getD a []).getD c 0 := by
  rw [← gc_ok a ha c hc, zcnt_eq hC hc _ _ (za_ok a ha), cnt, S0_eq hC,
    card_filter_map _ _ o0_nodup]

@[expose] def Ntab : List (List ℕ) :=
  [[0, 891, 0, 0, 0], [891, 0, 24948, 0, 0], [0, 24948, 997920, 0, 0],
    [0, 0, 0, 591360, 228096], [0, 0, 0, 228096, 0]]

theorem N_arith : ∀ b < 5, ∀ c < 5, 2300 * (Ntab.getD b []).getD c 0 =
    Inner.sizeOf b * (Gtab.getD b []).getD c 0 := by decide

theorem N_eq (hC : CensusLists) {b c : ℕ} (hb : b < 5) (hc : c < 5) :
    cnt (Rc c) b 1 = (Ntab.getD b []).getD c 0 := by
  have h := double hC (Rc_inv hC hc) (Rc_sym c) (x := 0) (y := b) (by omega) hb
  rw [cnt0_eq hC hb hc] at h
  have h2 := N_arith b hb c hc
  have e0 : Inner.sizeOf 0 = 2300 := rfl
  have r0 : rootOf 0 = 1 := rfl
  rw [e0, r0] at h
  omega

end CertificateChecks.KernelBM.CTIB.Hist

end
