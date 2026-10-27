
module

public import CFSG.Monster.B.TwoA.Unitary.WStabBase
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

theorem qL_v0 : qL v0 = 0 := Griess.qL_classOf_minVecs vMinus_zero_one_mem

abbrev qWv : QuadraticForm (ZMod 2) (Wv v0) := qW v0 qL_v0

abbrev bW : LinearMap.BilinForm (ZMod 2) (Wv v0) := QuadraticMap.polarBilin qWv

@[expose] def sigmaPerp :
    Submodule (ZMod 2) (Wv v0) := LinearMap.ker (bW sigmaW)

theorem bW_comm (x y : Wv v0) : bW x y = bW y x := QuadraticMap.polar_comm _ x y

theorem qL_kOp (k : OLq) (x : L2) : qL (kOp k x) = qL x := by
  induction k using QuotientGroup.induction_on with
  | H g => exact qL_modTwoEnd g x

theorem qWv_wAct (k : Kstab v0) (x : Wv v0) : qWv (wAct v0 k x) = qWv x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [wAct_mk, qW_mk, qW_mk]
    exact qL_kOp _ _

theorem bW_wAct (k : Kstab v0) (x y : Wv v0) : bW (wAct v0 k x) (wAct v0 k y) = bW x y := by
  change QuadraticMap.polar qWv _ _ = QuadraticMap.polar qWv _ _
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, qWv_wAct, qWv_wAct, qWv_wAct]

theorem qWv_sigmaW :
    qWv sigmaW = 0 :=
  Griess.qL_classOf_minVecs (pairVec_mem (by decide) 0)

theorem hInt_sigma_twoΩ : hInt (pairVec 0 2 0) Visible.twoΩ = 0 := by decide +kernel

theorem bW_sigmaW_wFr :
    bW sigmaW wFr = 0 := by
  rw [sigmaW, wFr, polarBilin_qW_mk]
  change bL (pairCls 0 2 0) twoΩCls = 0
  rw [pairCls, Griess.classOf_eq_cls (pairVec_mem (by decide) 0).1, twoΩCls, bL_apply]
  change QuadraticMap.polarBilin qL _ _ = 0
  rw [bL_cls, hInt_sigma_twoΩ]
  rfl

theorem sigmaCls_ne_zero : sigmaCls ≠ 0 :=
  Griess.classOf_ne_zero_of_mem_minVecs (pairVec_mem (by decide) 0)

theorem sigmaW_ne_zero :
    sigmaW ≠ 0 := by
  rw [sigmaW, Ne, mk_eq_zero_iff]
  rintro (h | h)
  · exact sigmaCls_ne_zero h
  · have := (pairCls_eq_iff (by decide : (0 : Fin 24) ≠ 2) (by decide : (0 : Fin 24) ≠ 1) 0 0).1
      (h.trans v0_eq_pairCls)
    rcases this.1 with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)

theorem bW_nondegenerate : bW.Nondegenerate :=
  polarBilin_qW_nondegenerate v0_ne_zero qL_v0

theorem exists_bW_sigmaW_eq_one :
    ∃ z, bW sigmaW z = 1 := by
  by_contra h
  push Not at h
  apply sigmaW_ne_zero
  refine bW_nondegenerate.1 sigmaW fun y => ?_
  rcases zmod2_cases' (bW sigmaW y) with h0 | h1
  · exact h0
  · exact absurd h1 (h y)

theorem finrank_sigmaPerp :
    Module.finrank (ZMod 2) sigmaPerp = 21 := by
  obtain ⟨z, hz⟩ := exists_bW_sigmaW_eq_one
  have hrange : LinearMap.range (bW sigmaW) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • z, by rw [map_smul, hz, smul_eq_mul, mul_one]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (bW sigmaW)
  rw [hrange, finrank_top, Module.finrank_self, finrank_W] at h
  change Module.finrank (ZMod 2) (LinearMap.ker (bW sigmaW)) = 21
  omega

@[expose] def spanDual : List ℕ :=
  [4639, 4183471, 3126715, 35503, 3011771, 4193969, 1114644, 1311252, 1050915, 528175, 3149603,
    4192562, 1049088, 664, 4193184, 532, 512, 1280, 1408, 4192256, 256]

theorem spanDual_check : ∀ i j : Fin 21,
    bvec 22 (spanDual.getD j 0) ⬝ᵥ bvec 22 n6SpanArr[(i : ℕ)]! = if i = j then 1 else 0 := by
  decide +kernel

theorem wAct_eq_one_of_fix
    (u : Kstab v0) (hfix : ∀ x ∈ sigmaPerp, wAct v0 u x = x) :
    wAct v0 u = 1 := by
  obtain ⟨z₀, hz₀⟩ := exists_bW_sigmaW_eq_one
  refine LinearMap.ext fun z => ?_
  rw [Module.End.one_apply]
  set d := wAct v0 u z - z with hd
  have horth : ∀ y ∈ sigmaPerp, bW d y = 0 := by
    intro y hy
    rw [hd, map_sub, LinearMap.sub_apply, ← hfix y hy, bW_wAct, hfix y hy, sub_self]
  set c := bW d z₀ with hc
  have hdc : d = c • sigmaW := by
    rw [← sub_eq_zero]
    refine bW_nondegenerate.1 _ fun y => ?_
    have hy : y - bW sigmaW y • z₀ ∈ sigmaPerp := by
      change bW sigmaW (y - bW sigmaW y • z₀) = 0
      rw [map_sub, map_smul, hz₀, smul_eq_mul, mul_one, sub_self]
    have h1 := horth _ hy
    rw [map_sub, map_smul, smul_eq_mul, ← hc] at h1
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]
    exact h1
  rcases zmod2_cases' c with h0 | h1
  · rw [h0, zero_smul, hd, sub_eq_zero] at hdc
    exact hdc
  · exfalso
    rw [h1, one_smul, hd, sub_eq_iff_eq_add] at hdc
    have hq := qWv_wAct u z
    rw [hdc, QuadraticMap.map_add qWv sigmaW z, qWv_sigmaW, zero_add, add_eq_left] at hq
    have hz : z ∈ sigmaPerp := hq
    rw [hfix z hz, right_eq_add] at hdc
    exact sigmaW_ne_zero hdc

end CFSG.Monster.B.TwoA.Unitary
