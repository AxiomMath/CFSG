module

public import Certificates.Kernel.BabyMonster.Chain2
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.All
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check73
public import CFSG.Monster.B.Dyadic.BridgeK
public import CFSG.Monster.B.Dyadic.CTIBK
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check11
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check12
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check13
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check14
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Check9

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.Monster.B.Dyadic

set_option maxRecDepth 100000

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem brm1 {A W C : List Nat} (hW : wfMat W = true) (hA : wfMat A = true)
    (h : AllStrips [W] A C) : stripMat A * stripMat W = stripMat C := by
  have e := stripMat_mul_of_allStrips (Ws := [W]) (fun X hX => by
    rw [List.mem_singleton.1 hX]
    exact hW) hA h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e

theorem br_foldl {M : Type*} [Monoid M] (a : M) (l : List M) :
    l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => rw [List.foldl_nil, List.prod_nil, mul_one]
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

@[expose] noncomputable def blockK (b : List Bool) : MatB :=
  (b.map fun l => if l then cK else dK).prod

theorem wordCD_flatten (L : List (List Bool)) : wordCD L.flatten = (L.map blockK).prod := by
  rw [wordCD, List.map_flatten, List.prod_flatten, List.map_map]
  rfl

section Blocks

variable {M : Type*} [Monoid M] (c d : M)

theorem blk_ba : ([false, true].map fun l => if l then c else d).prod = d * c := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true,
    Bool.false_eq_true, ite_false, mul_one]

theorem blk_bbb : ([false, false, false].map fun l => if l then c else d).prod = d * (d * d) := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.false_eq_true,
    ite_false, mul_one]

theorem blk_aba : ([true, false, true].map fun l => if l then c else d).prod = c * d * c := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true,
    Bool.false_eq_true, ite_false, mul_one, mul_assoc]

theorem blk_abb : ([true, false, false].map fun l => if l then c else d).prod = c * d * d := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true,
    Bool.false_eq_true, ite_false, mul_one, mul_assoc]

theorem blk_bab : ([false, true, false].map fun l => if l then c else d).prod = d * c * d := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true,
    Bool.false_eq_true, ite_false, mul_one, mul_assoc]

theorem blk_bba : ([false, false, true].map fun l => if l then c else d).prod = d * d * c := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true,
    Bool.false_eq_true, ite_false, mul_one, mul_assoc]

end Blocks

section Letters

variable (hc : cK = stripMat Max2.r11) (hd : dK = stripMat Max2.r4)

include hc hd in
theorem br_ab : cK * dK = stripMat Max2Br.Lab := by
  rw [hc, hd, brm1 Max2.wf_r4 Max2.wf_r11 (by bm_strips CFSG.KC.BM.Max2Br.cLab 69)]

include hc hd in
theorem br_ba : blockK [false, true] = stripMat Max2Br.Lba := by
  rw [blockK, blk_ba, hc, hd,
    brm1 Max2.wf_r11 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2Br.cLba 69)]

include hd in
theorem br_bb : dK * dK = stripMat Max2.r5 := by
  rw [hd, brm1 Max2.wf_r4 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2.cr5 69)]

include hd in
theorem br_bbb : blockK [false, false, false] = stripMat Max2.r6 := by
  rw [blockK, blk_bbb, br_bb hd, hd,
    brm1 Max2.wf_r5 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2.cr6 69)]

include hc hd in
theorem br_aba : blockK [true, false, true] = stripMat Max2Br.Laba := by
  rw [blockK, blk_aba, br_ab hc hd, hc,
    brm1 Max2.wf_r11 Max2Br.wf_Lab (by bm_strips CFSG.KC.BM.Max2Br.cLaba 69)]

include hc hd in
theorem br_abb : blockK [true, false, false] = stripMat Max2Br.Labb := by
  rw [blockK, blk_abb, br_ab hc hd, hd,
    brm1 Max2.wf_r4 Max2Br.wf_Lab (by bm_strips CFSG.KC.BM.Max2Br.cLabb 69)]

include hc hd in
theorem br_bab : blockK [false, true, false] = stripMat Max2Br.Lbab := by
  rw [blockK, blk_bab, hc, hd,
    brm1 Max2.wf_r11 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2Br.cLba 69),
    brm1 Max2.wf_r4 Max2Br.wf_Lba (by bm_strips CFSG.KC.BM.Max2Br.cLbab 69)]

include hc hd in
theorem br_bba : blockK [false, false, true] = stripMat Max2Br.Lbba := by
  rw [blockK, blk_bba, br_bb hd, hc,
    brm1 Max2.wf_r11 Max2.wf_r5 (by bm_strips CFSG.KC.BM.Max2Br.cLbba 69)]

end Letters

@[expose] def uBlocks : List (List Bool) :=
  [[false, false, true], [false, true, false], [false, false, false], [true, false, false],
    [false, true, false], [true, false, false], [true, false, false], [false, false, false],
    [false, false, false], [false, false, false], [true, false, false]]

@[expose] def vBlocks : List (List Bool) :=
  [[false, false, true], [false, true, false], [false, true, false], [false, false, true],
    [false, true, false], [true, false, true], [false, false, true], [false, false, true],
    [false, true, false], [false, true]]

theorem bridgeU_eq : CFSG.Monster.B.Bin.bridgeU = uBlocks.flatten := rfl

theorem bridgeV_eq : CFSG.Monster.B.Bin.bridgeV = vBlocks.flatten := rfl

@[expose] noncomputable def uL : List (List Nat) :=
  [Max2Br.Lbba, Max2Br.Lbab, Max2.r6, Max2Br.Labb, Max2Br.Lbab, Max2Br.Labb, Max2Br.Labb,
    Max2.r6, Max2.r6, Max2.r6, Max2Br.Labb]

@[expose] noncomputable def vL : List (List Nat) :=
  [Max2Br.Lbba, Max2Br.Lbab, Max2Br.Lbab, Max2Br.Lbba, Max2Br.Lbab, Max2Br.Laba, Max2Br.Lbba,
    Max2Br.Lbba, Max2Br.Lbab, Max2Br.Lba]

@[expose] noncomputable def zL : List (List Nat) :=
  [Max2.E4, Max2.E7, Max2.E9, Max2.E10, Max2.E11, Max2.E15, Max2.E16, Max2.E17, Max2.E20]

theorem uchain : WChain uL.tail Max2Br.Lbba Max2Br.Wu := by
  bm_wchain CFSG.KC.BM.Max2Br.cWu 4 CFSG.KC.BM.Max2Br.wf_

theorem vchain : WChain vL.tail Max2Br.Lbba Max2Br.Wv := by
  bm_wchain CFSG.KC.BM.Max2Br.cWv 4 CFSG.KC.BM.Max2Br.wf_

theorem zchain : WChain zL Max2.Xb Max2Br.Zq := by
  bm_wchain CFSG.KC.BM.Max2Br.cZq 4 CFSG.KC.BM.Max2Br.wf_

theorem wordCD_u (hc : cK = stripMat Max2.r11) (hd : dK = stripMat Max2.r4) :
    wordCD CFSG.Monster.B.Bin.bridgeU = stripMat Max2Br.Wu := by
  have hwf : ∀ W ∈ uL.tail, wfMat W = true := by
    simp only [uL, List.tail_cons, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, Max2Br.wf_Lbab, Max2Br.wf_Labb, Max2.wf_r6, and_self]
  have h := stripMat_wchain uchain hwf Max2Br.wf_Lbba
  have hL : uBlocks.map blockK = uL.map stripMat := by
    simp only [uBlocks, uL, List.map_cons, List.map_nil, br_bba hc hd, br_bab hc hd,
      br_bbb hd, br_abb hc hd]
  have hu : uL.map stripMat = stripMat Max2Br.Lbba :: uL.tail.map stripMat := rfl
  rw [br_foldl] at h
  rw [← h, bridgeU_eq, wordCD_flatten, hL, hu, List.prod_cons]

theorem wordCD_v (hc : cK = stripMat Max2.r11) (hd : dK = stripMat Max2.r4) :
    wordCD CFSG.Monster.B.Bin.bridgeV = stripMat Max2Br.Wv := by
  have hwf : ∀ W ∈ vL.tail, wfMat W = true := by
    simp only [vL, List.tail_cons, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, Max2Br.wf_Lbab, Max2Br.wf_Lbba, Max2Br.wf_Laba, Max2Br.wf_Lba, and_self]
  have h := stripMat_wchain vchain hwf Max2Br.wf_Lbba
  have hL : vBlocks.map blockK = vL.map stripMat := by
    simp only [vBlocks, vL, List.map_cons, List.map_nil, br_bba hc hd, br_bab hc hd,
      br_aba hc hd, br_ba hc hd]
  have hv : vL.map stripMat = stripMat Max2Br.Lbba :: vL.tail.map stripMat := rfl
  rw [br_foldl] at h
  rw [← h, bridgeV_eq, wordCD_flatten, hL, hv, List.prod_cons]

theorem br_prodK_eq (l : List MatB) : prodK l = l.prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [prodK, ih, List.prod_cons]

theorem br_prodK_ite (p : ℕ → Bool) (E : ℕ → MatB) (l : List ℕ) :
    prodK (l.map fun j => if p j then E j else 1) = prodK ((l.filter p).map E) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    by_cases h : p j
    · rw [List.map_cons, List.filter_cons_of_pos h, List.map_cons, prodK, prodK, ih]
      simp only [h, ite_true]
    · rw [List.map_cons, List.filter_cons_of_neg h, prodK, ih]
      simp only [h, Bool.false_eq_true, ite_false, one_mul]

theorem bridgeZ_bits :
    (List.range 22).filter (fun j => CFSG.Monster.B.Bin.bridgeZ.testBit j) =
      [4, 7, 9, 10, 11, 15, 16, 17, 20] := by
  decide

theorem bridgeZ_E : List.map EK [4, 7, 9, 10, 11, 15, 16, 17, 20] = zL.map stripMat := rfl

theorem qK_bridge : qK CFSG.Monster.B.Bin.bridgeZ = stripMat Max2Br.Zq := by
  have hwf : ∀ W ∈ zL, wfMat W = true := by
    simp only [zL, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      Max2.wf_E4, Max2.wf_E7, Max2.wf_E9, Max2.wf_E10, Max2.wf_E11, Max2.wf_E15, Max2.wf_E16,
      Max2.wf_E17, Max2.wf_E20, and_self]
  have h := stripMat_wchain zchain hwf Max2.wf_Xb
  have h22 : CFSG.Monster.B.Bin.bridgeZ.testBit 22 = true := by decide
  rw [br_foldl] at h
  rw [← h, qK, br_prodK_ite (fun j => CFSG.Monster.B.Bin.bridgeZ.testBit j), bridgeZ_bits,
    br_prodK_eq, bridgeZ_E]
  simp only [h22, ite_true]
  rfl

theorem bridgeZE_map : bridgeZE.map EK = zL.map stripMat := rfl

theorem zq_prod : ZqK = XK * (bridgeZE.map EK).prod := by
  have hwf : ∀ W ∈ zL, wfMat W = true := by
    simp only [zL, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      Max2.wf_E4, Max2.wf_E7, Max2.wf_E9, Max2.wf_E10, Max2.wf_E11, Max2.wf_E15, Max2.wf_E16,
      Max2.wf_E17, Max2.wf_E20, and_self]
  have h := stripMat_wchain zchain hwf Max2.wf_Xb
  rw [br_foldl] at h
  rw [ZqK, XK, bridgeZE_map]
  exact h.symm

end CertificateChecks.KernelBM.Pair

end
