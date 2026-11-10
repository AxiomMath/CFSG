
module

public import CFSG.Monster.B.TwoA.Co2Inv.CentOrderBase
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

def zVec (t : Fin 6) : Wv v0 := decW zBasis[(t : ℕ)]!

theorem zBasis_comb_zero : Native.actD 6 zBasis 0 = 0 := by decide +kernel

theorem zBasis_comb_single : ∀ t < 6,
    1 <<< t < 64 ∧ Native.actD 6 zBasis (1 <<< t) = zBasis[t]! := by
  decide +kernel

theorem zBasis_comb_xor : ∀ c < 64, ∀ c' < 64,
    Native.actD 6 zBasis c ^^^ Native.actD 6 zBasis c' = Native.actD 6 zBasis (c ^^^ c') := by
  decide +kernel

theorem zBasis_comb_frame : ∀ c < 64, 0 < c →
    ∃ i < 63, Native.actD 6 zBasis c = frameOrbit[i]! := by
  decide +kernel

theorem frame_zBasis_comb : ∀ i < 63,
    ∃ c < 64, 0 < c ∧ Native.actD 6 zBasis c = frameOrbit[i]! := by
  decide +kernel

theorem frameOrbit_bounds : ∀ i < 63, 0 < frameOrbit[i]! ∧ frameOrbit[i]! < 2 ^ 22 := by
  decide +kernel

theorem sixRows_spec : ∀ k < 21, ∀ c < 64, Native.actD 6 (sixRows[k]!) c < 64 ∧
    Native.actD 22 (cRows k) (Native.actD 6 zBasis c) =
      Native.actD 6 zBasis (Native.actD 6 (sixRows[k]!) c) := by
  decide +kernel

theorem sixRows_single : ∀ k < 21, ∀ t < 6, Native.actD 6 (sixRows[k]!) (1 <<< t) =
    (sixRows[k]!)[t]! := by
  decide +kernel

def gramMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => bvec 6 gramSix[(i : ℕ)]! j

def gramInvRows : Array ℕ := #[56, 44, 42, 39, 1, 15]

def gramInvMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => bvec 6 gramInvRows[(i : ℕ)]! j

theorem gramMat_mul_inv : gramMat * gramInvMat = 1 := by decide +kernel

theorem gramMat_alt : ∀ c < 64, ∑ i, ∑ j, bvec 6 c i * gramMat i j * bvec 6 c j = 0 := by
  decide +kernel

theorem gramMat_invariant : ∀ k < 21, ∀ i j : Fin 6,
    ∑ s : Fin 6, ∑ u : Fin 6, bvec 6 (sixRows[k]!)[(i : ℕ)]! s * bvec 6 gramSix[(s : ℕ)]! u *
      bvec 6 (sixRows[k]!)[(j : ℕ)]! u = bvec 6 gramSix[(i : ℕ)]! j := by
  decide +kernel

def zDual : Array ℕ := #[4097, 8192, 16384, 32768, 3, 61443]

def zDualMat : Matrix (Fin 6) (Fin 22) (ZMod 2) :=
  Matrix.of fun i t => bvec 22 zDual[(i : ℕ)]! t

theorem zDualMat_zBasis : ∀ j : Fin 6,
    zDualMat.mulVec (bvec 22 zBasis[(j : ℕ)]!) = Pi.single j 1 := by
  decide +kernel

attribute [local instance] wLeftAction

def dec6 (n : ℕ) : Fin 6 → Wv v0 := fun t => decW (rowOf n t)

theorem dec6_injective {a b : ℕ} (ha : valid6 a = true) (hb : valid6 b = true)
    (h : dec6 a = dec6 b) : a = b := by
  have hrow : ∀ t < 6, rowOf a t = rowOf b t := fun t ht =>
    decW_injective (rowOf_lt _ _) (rowOf_lt _ _) (congrFun h ⟨t, ht⟩)
  have hrows : rows6 a = rows6 b := by
    rw [rows6, rows6]
    exact List.map_congr_left fun t ht => hrow t (List.mem_range.1 ht)
  rw [valid6, beq_iff_eq] at ha hb
  rw [ha, hb, hrows]

end CFSG.Monster.B.TwoA.Co2Inv
