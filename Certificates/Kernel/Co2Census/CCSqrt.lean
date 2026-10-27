module

public import Certificates.Kernel.Co2Census.CCCls
public import Certificates.Kernel.Co2Census.CCK0
public import Certificates.Kernel.Co2Census.CCK1
public import Certificates.Kernel.Co2Census.CCK3
public import Certificates.Kernel.Co2Census.CCK4
public import Certificates.Kernel.Co2Census.CCK6
public import Certificates.Kernel.Co2Census.CCK8
public import Certificates.Kernel.Co2Census.CCRep
public import Certificates.Kernel.Co2Census.S0C26805K

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem cent_26805 :
    {y | ∃ i < 23040, repK y (C26805Pt i)} = centS0 (sElt 26805) :=
  cent_pts (j := 1) (by norm_num) (by norm_num) rfl C26805_tree C26805_clos C26805_root
    C26805_misc (by decide) (by norm_num)

theorem sqrtCnt_eq_ccPred (c r : Cz) : sqrtCnt c r = Nat.card {y : Cz // ccPred r c true y} := by
  unfold sqrtCnt ccPred
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)

theorem zCz_comm' (g : Cz) : g * zCz = zCz * g :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

theorem cc_sqrtZ {G GR GI Pt IX RT Zc : ℕ → ℕ} {er nr N hi nroots : ℕ} (her : er < 512)
    (hgen : (List.range 6).all (genOKC QKt G GR GI er nr) = true)
    (htree : ∀ i < N, treeK (conjStep GR GI) 6 N Pt IX i = true)
    (hroot : (List.range nroots).all (rootOKC Pt IX RT N) = true)
    (hcov : ∀ i < N, coverRootK IX RT nroots i = true)
    (hpos : ∀ j < 5104, posK (fun x => Nat.beq (mulV x (SK nr)) (mulV (SK nr) x)) LPt Pt Zc N j =
      true) (hN : N ≤ 64 * hi) :
    sqrtCnt zCz (cE er nr) =
      totalC QKt IX RT N hi nroots nr 0 (mulV (SK nr) (QKt er)) (mulV (SK 0) (QKt 256)) true := by
  rw [sqrtCnt_eq_ccPred]
  exact card_cc_query QK_eq her repK_zCz (by rw [piC_zCz, sElt_zero]) true
    (fun w _ => zCz_comm' w) (all_lt hgen) htree (all_lt hroot) hcov (suppZC hpos piC_zCz) hN

theorem cc_sqrtR0 {G GR GI Pt IX RT Zc : ℕ → ℕ} {er N hi nroots : ℕ} (her : er < 512)
    (hgen : (List.range 6).all (genOKC QKt G GR GI er 0) = true)
    (htree : ∀ i < N, treeK (conjStep GR GI) 6 N Pt IX i = true)
    (hroot : (List.range nroots).all (rootOKC Pt IX RT N) = true)
    (hcov : ∀ i < N, coverRootK IX RT nroots i = true)
    (hpos : ∀ j < 5104, posK (fun x => Nat.beq (mulV x (SK 0)) (mulV (SK 0) x)) LPt Pt Zc N j =
      true) (hN : N ≤ 64 * hi) :
    sqrtCnt (cE er 0) (cE er 0) =
      totalC QKt IX RT N hi nroots 0 0 (mulV (SK 0) (QKt er)) (mulV (SK 0) (QKt er)) true := by
  rw [sqrtCnt_eq_ccPred]
  exact card_cc_query QK_eq her (repK_cE QK_eq her 0) (piC_cE er 0) true (fun w h => h)
    (all_lt hgen) htree (all_lt hroot) hcov (suppZC hpos (by rw [piC_cE, sElt_zero])) hN

theorem cc_sqrtR {G GR GI Pt IX RT Rc CP : ℕ → ℕ} {er nr N NC hi nroots : ℕ} (her : er < 512)
    (hcent : {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr))
    (hgen : (List.range 6).all (genOKC QKt G GR GI er nr) = true)
    (htree : ∀ i < N, treeK (conjStep GR GI) 6 N Pt IX i = true)
    (hroot : (List.range nroots).all (rootOKC Pt IX RT N) = true)
    (hcov : ∀ i < N, coverRootK IX RT nroots i = true)
    (hpos : ∀ j < NC, posK (fun x => Nat.beq (mulV x x) (SK nr)) CP Pt Rc N j = true)
    (hN : N ≤ 64 * hi) :
    sqrtCnt (cE er nr) (cE er nr) =
      totalC QKt IX RT N hi nroots nr nr (mulV (SK nr) (QKt er)) (mulV (SK nr) (QKt er)) true := by
  rw [sqrtCnt_eq_ccPred]
  exact card_cc_query QK_eq her (repK_cE QK_eq her nr) (piC_cE er nr) true (fun w h => h)
    (all_lt hgen) htree (all_lt hroot) hcov (suppRC hcent hpos true) hN

theorem cc_sqrt_none {CP : ℕ → ℕ} {er nr NC : ℕ}
    (hcent : {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr))
    (h : ∀ j < NC, (!Nat.beq (mulV (CP j) (CP j)) (SK nr)) = true) :
    sqrtCnt (cE er nr) (cE er nr) = 0 := by
  unfold sqrtCnt
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨y, _, hy⟩ => ?_⟩
  have h2 := congrArg piC hy
  rw [map_mul, piC_cE] at h2
  have hc : piC y ∈ centS0 (sElt nr) := ⟨piC_mem y, by rw [← h2, ← mul_assoc]⟩
  rw [← hcent] at hc
  obtain ⟨j, hj, hrep⟩ := hc
  have ht := h j hj
  rw [Bool.not_eq_true'] at ht
  exact Nat.ne_of_beq_eq_false ht (repK_unique (h2 ▸ repK_mul hrep hrep) (repK_sElt nr))

theorem cc_sqrt0 : sqrtCnt zCz (cE 1 0) = 1792 ∧ sqrtCnt (cE 1 0) (cE 1 0) = 5376 :=
  ⟨(cc_sqrtZ (hi := 80) (by norm_num) K0_gens K0Z_tree K0Z_roots K0Z_cover K0Z_pos
    (by norm_num)).trans K0Z_total,
   (cc_sqrtR0 (hi := 80) (by norm_num) K0_gens K0Z_tree K0Z_roots K0Z_cover K0Z_pos
    (by norm_num)).trans K0R_total⟩

theorem cc_sqrt1 : sqrtCnt zCz (cE 0 26805) = 0 ∧ sqrtCnt (cE 0 26805) (cE 0 26805) = 0 :=
  ⟨(cc_sqrtZ (hi := 12) (by norm_num) K1_gens K1Z_tree K1Z_roots K1Z_cover K1Z_pos
    (by norm_num)).trans K1Z_total, cc_sqrt_none cent_26805 C26805_noroot⟩

theorem cc_sqrt2 : sqrtCnt zCz (cE 32 26805) = 0 ∧ sqrtCnt (cE 32 26805) (cE 32 26805) = 0 :=
  ⟨(cc_sqrtZ (hi := 12) (by norm_num) K2_gens K2Z_tree K2Z_roots K2Z_cover K2Z_pos
    (by norm_num)).trans K2Z_total, cc_sqrt_none cent_26805 C26805_noroot⟩

theorem cc_sqrt3 : sqrtCnt zCz (cE 0 2331) = 384 ∧ sqrtCnt (cE 0 2331) (cE 0 2331) = 1152 :=
  ⟨(cc_sqrtZ (hi := 6) (by norm_num) K3_gens K3Z_tree K3Z_roots K3Z_cover K3Z_pos
    (by norm_num)).trans K3Z_total,
   (cc_sqrtR (hi := 1) (by norm_num) cent_2331 K3_gens K3R_tree K3R_roots K3R_cover K3R_pos
    (by norm_num)).trans K3R_total⟩

theorem cc_sqrt4 : sqrtCnt zCz (cE 2 2331) = 192 ∧ sqrtCnt (cE 2 2331) (cE 2 2331) = 128 :=
  ⟨(cc_sqrtZ (hi := 6) (by norm_num) K4_gens K4Z_tree K4Z_roots K4Z_cover K4Z_pos
    (by norm_num)).trans K4Z_total,
   (cc_sqrtR (hi := 1) (by norm_num) cent_2331 K4_gens K4R_tree K4R_roots K4R_cover K4R_pos
    (by norm_num)).trans K4R_total⟩

theorem cc_sqrt5 : sqrtCnt zCz (cE 80 2331) = 384 ∧ sqrtCnt (cE 80 2331) (cE 80 2331) = 384 :=
  ⟨(cc_sqrtZ (hi := 6) (by norm_num) K5_gens K5Z_tree K5Z_roots K5Z_cover K5Z_pos
    (by norm_num)).trans K5Z_total,
   (cc_sqrtR (hi := 1) (by norm_num) cent_2331 K5_gens K5R_tree K5R_roots K5R_cover K5R_pos
    (by norm_num)).trans K5R_total⟩

theorem cc_sqrt6 : sqrtCnt zCz (cE 0 1082) = 0 ∧ sqrtCnt (cE 0 1082) (cE 0 1082) = 512 :=
  ⟨(cc_sqrtZ (hi := 4) (by norm_num) K6_gens K6Z_tree K6Z_roots K6Z_cover K6Z_pos
    (by norm_num)).trans K6Z_total,
   (cc_sqrtR (hi := 1) (by norm_num) cent_1082 K6_gens K6R_tree K6R_roots K6R_cover K6R_pos
    (by norm_num)).trans K6R_total⟩

theorem cc_sqrt7 : sqrtCnt zCz (cE 13 1082) = 0 ∧ sqrtCnt (cE 13 1082) (cE 13 1082) = 0 :=
  ⟨(cc_sqrtZ (hi := 4) (by norm_num) K7_gens K7Z_tree K7Z_roots K7Z_cover K7Z_pos
    (by norm_num)).trans K7Z_total,
   (cc_sqrtR (hi := 1) (by norm_num) cent_1082 K7_gens K7R_tree K7R_roots K7R_cover K7R_pos
    (by norm_num)).trans K7R_total⟩

theorem cc_sqrt8 : sqrtCnt zCz (cE 0 144) = 0 ∧ sqrtCnt (cE 0 144) (cE 0 144) = 0 :=
  ⟨(cc_sqrtZ (hi := 2) (by norm_num) K8_gens K8Z_tree K8Z_roots K8Z_cover K8Z_pos
    (by norm_num)).trans K8Z_total, cc_sqrt_none cent_144 C144_noroot⟩

theorem s0Rep_eq {slot nr : ℕ} (h : slot ≠ 0) (h' : s0Reps.getD (slot - 1) 0 = nr) :
    s0Rep slot = sElt nr := by
  rw [s0Rep, if_neg h, h']

theorem cc_cls0 : 270 ≤ (conjSet (cE 1 0)).ncard :=
  cc_cls_le QK_eq (nf := 270) (slot := 0) (by norm_num) (by norm_num) (by norm_num)
    (by rw [s0Rep, if_pos rfl, sElt_zero]) K0_fib

theorem cc_cls1 : 1008 ≤ (conjSet (cE 0 26805)).ncard :=
  cc_cls_le QK_eq (nf := 16) (slot := 1) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K1_fib

theorem cc_cls2 : 1008 ≤ (conjSet (cE 32 26805)).ncard :=
  cc_cls_le QK_eq (nf := 16) (slot := 1) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K2_fib

theorem cc_cls3 : 1260 ≤ (conjSet (cE 0 2331)).ncard :=
  cc_cls_le QK_eq (nf := 4) (slot := 2) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K3_fib

theorem cc_cls4 : 22680 ≤ (conjSet (cE 2 2331)).ncard :=
  cc_cls_le QK_eq (nf := 72) (slot := 2) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K4_fib

theorem cc_cls5 : 1260 ≤ (conjSet (cE 80 2331)).ncard :=
  cc_cls_le QK_eq (nf := 4) (slot := 2) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K5_fib

theorem cc_cls6 : 15120 ≤ (conjSet (cE 0 1082)).ncard :=
  cc_cls_le QK_eq (nf := 16) (slot := 3) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K6_fib

theorem cc_cls7 : 15120 ≤ (conjSet (cE 13 1082)).ncard :=
  cc_cls_le QK_eq (nf := 16) (slot := 3) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K7_fib

theorem cc_cls8 : 120960 ≤ (conjSet (cE 0 144)).ncard :=
  cc_cls_le QK_eq (nf := 32) (slot := 4) (by norm_num) (by norm_num) (by norm_num)
    (s0Rep_eq (by norm_num) rfl) K8_fib

end CC

end CertificateChecks.KernelCo2Census

end
