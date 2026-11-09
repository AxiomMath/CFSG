module

public import Certificates.Kernel.Misc.Coset.Q3Act.Tz
public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Misc.Coset.PGCube

public section

namespace CFSG.KBRoute.F291372c

open CFSG.KC.MiscCoset CFSG.KAct.Q3

@[expose] def rels : List (List (Nat × Bool)) :=
  (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)).map
    fun w => w.map fun l => (l.1.val, l.2)

end CFSG.KBRoute.F291372c

#kc_blocked CFSG.KBData.F291372c.F include_bytes "data/F291372c.F.bin" 12 6 18446744073709551615
  3708096 13976176719979646309
#kc_blocked CFSG.KBData.F291372c.D include_bytes "data/F291372c.D.bin" 12 4 65535
  166052 17175636126895881513
#kc_items CFSG.KBData.F291372c.Wd include_bytes "data/F291372c.Wd.items" 17764 2290844009907685668
#kc_items CFSG.KBData.F291372c.Wd2 include_bytes "data/F291372c.Wd2.items" 28441 5478023187777758647
#kc_items CFSG.KBData.F291372c.R include_bytes "data/F291372c.R.items" 4021 9065635621908820789
#kc_items CFSG.KBData.F291372c.S include_bytes "data/F291372c.S.items" 78 3416561410313632813
#kc_items CFSG.KBData.F291372c.wl include_bytes "data/F291372c.wl.items" 7235557
  6449601298402527294

#kb_table CFSG.KBRoute.F291372c T1 F291372c include_bytes "data/F291372c.meta" 47823
  10256762159228429224 3727165692135864801209549313 CFSG.KBRoute.F291372c.rels
  "1 2 3 4 5 6 7 8 10 11"

namespace CFSG.KBCube.F291372c

open CFSG.Certificates CFSG.KC.MiscCoset CFSG.KBData.F291372c CFSG.KBRoute.F291372c

@[expose] def inv : Nat := 151192090555688230391240540579447798763628265986242910552065

@[expose] noncomputable def st (j : Nat) : Nat :=
  Bool.rec 463512 (Nat.add 83025 (Nat.mul 24 j)) (Nat.ble (Nat.add 83025 (Nat.mul 24 j)) 463512)

@[expose] noncomputable def wk (j : Nat) : Bool :=
  Nat.beq (KB.wElem F Wd2 20 1048575 83026 1021 (wl j) (st j)) (st (Nat.succ j))

#kc_each CFSG.KBCube.F291372c.wk 0 2000
#kc_each CFSG.KBCube.F291372c.wk 2000 4000
#kc_each CFSG.KBCube.F291372c.wk 4000 6000
#kc_each CFSG.KBCube.F291372c.wk 6000 8000
#kc_each CFSG.KBCube.F291372c.wk 8000 10000
#kc_each CFSG.KBCube.F291372c.wk 10000 12000
#kc_each CFSG.KBCube.F291372c.wk 12000 14000
#kc_each CFSG.KBCube.F291372c.wk 14000 15854

#kc_forall_tree wk_all (fun k => wk k = true) 15854 CFSG.KBCube.F291372c.wk

theorem top : KB.topOk T1.amap 12 = true := by decide +kernel

theorem lens_rels : KB.lensLt rels 256 = true := by decide +kernel

theorem lens_words : KB.lensLt T1.words 256 = true := by decide +kernel

theorem words : KB.wordsOkB Wd R S inv 24 246 10 1021 = true := by decide +kernel

theorem pairs : KB.words2Ok Wd Wd2 inv 1021 = true := by decide +kernel

theorem tree : KB.treeRange F D 24 83026 0 83025 = true := by decide +kernel

@[expose] noncomputable def walk : List Nat := (List.range 15854).map wl

theorem walk_all : KB.wWalkList F Wd2 20 1048575 83026 1021 walk 83025 = 463512 := by
  have h0 : st 0 = 83025 := by decide +kernel
  have hn : st 15854 = 463512 := by decide +kernel
  rw [← h0, ← hn]
  exact wWalkList_range F Wd2 20 1048575 83026 1021 wl st 15854
    fun j hj => Nat.eq_of_beq_eq_true (wk_all j hj)

theorem step1 : stepB F 463512 22 0 2 1 = true := by decide +kernel
theorem step2 : stepB F 463512 22 2 3 463511 = true := by decide +kernel
theorem step3 : stepB F 463512 22 3 0 2 = true := by decide +kernel

open CFSG.CosetTable CFSG.KAct.Q3 CFSG.Sporadic.Recognition.Fi24PrimeMultiplier in
theorem cube_mem :
    PresentedGroup.of (11 : Fin 12) ^ 3 ∈
      genSub {r : FreeGroup (Fin 12) | r ∈ (tzRels (tzGen CFSG.KD.OrdFi24p.rels)
        (wsQN CFSG.KD.OrdFi24p.rels)).map FreeGroup.mk} (subsetOf 12 S0) :=
  pow_three_mem_of_facts _ rfl (by norm_num) top (subsetOf 12 S0) (by decide +kernel)
    (inv := inv) (L := 24) (eps := 24) (nLab := 83026) (nT := 83025) (RW := 20) (RM := 1048575)
    (nR := 246) (nS := 10) (nW := 1021) (nF := 463512) (F := F) (D := D) (Wd := Wd) (Wd2 := Wd2)
    (R := R) (S := S) (walk := walk)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) lens_rels lens_words T1.hdr_ok T1.rels_ok T1.subs_ok
    words pairs tree walk_all 11 (by decide +kernel) step1 step2 step3

end CFSG.KBCube.F291372c

end
