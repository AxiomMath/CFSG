
module

public import CFSG.Monster.B.TwoA.Co2Inv.SixCertBase

public import CFSG.Monster.B.TwoA.Co2Inv.CentOrder
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import Certificates.Certificate3056
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem sixCheck_eq_true : sixCheck = true :=
  Certificates.certificate3056

theorem sixCheck_parts : natCertOK act6 20 valid6 root6 sixCert =
    true ∧
    sixCert.pts.size = 23040 ∧ ∀ t < 6, rowOf root6 t = zBasis[t]! := by
  have h := sixCheck_eq_true
  simp only [sixCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

attribute [local instance] wLeftAction

theorem dec6_act6
    {k : ℕ} (hk : k < 20) (a : ℕ) : dec6 (act6 k a) = gensFrame k •
    dec6 a := by
  funext t
  rw [Pi.smul_apply]
  change decW (rowOf (act6 k a) (t : ℕ)) = gensFrame k • decW (rowOf a (t : ℕ))
  rw [act6, rowOf_encL, decW_mod, List.getD_eq_getElem _ _ (by simp),
    ← decW_actFrame (show k < 21 by omega)]
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem dec6_root6 : dec6 root6 = zVec := by
  funext t
  change decW (rowOf root6 t) = decW zBasis[(t : ℕ)]!
  rw [sixCheck_parts.2.2 t t.2]

theorem closure_gensFrame_twenty :
    Subgroup.closure (gensFrame '' {k | k < 20}) = M20 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 21 := by
      have : k < 20 := hk
      omega
    rw [gensFrame, dite_eq_left hk']
    exact Subgroup.inv_mem _ (cGen_mem_M20 (show k < 20 from hk))
  · rw [M20, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have h : gensFrame k ∈ Subgroup.closure (gensFrame '' {k | k < 20}) :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    have := Subgroup.inv_mem _ h
    rwa [gensFrame, dite_eq_left k.2, inv_inv] at this

theorem ncard_orbit_zVec :
    (MulAction.orbit Mr zVec).ncard
    = 23040 :=
    by
  have h := ncard_orbit_of_natCertOK (G := Kstab v0) sixCheck_parts.1
    (fun k hk a _ => dec6_act6 hk a) (fun a b ha hb e => dec6_injective ha hb e)
  rw [sixCheck_parts.2.1, dec6_root6, closure_gensFrame_twenty, M20_eq_Mr.1] at h
  exact h

end CFSG.Monster.B.TwoA.Co2Inv
