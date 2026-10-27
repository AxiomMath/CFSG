
module

public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertBase

public import CFSG.Monster.B.TwoA.Co2Inv.Rows
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import Certificates.Certificate3055
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
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

theorem frameCheck_eq_true : frameCheck = true :=
  Certificates.certificate3055.1

theorem frameCheck_parts : natCertOK actFrame 21 validW 31 frameCert
    = true ∧
    frameCert.pts = frameOrbit := by
  have h := frameCheck_eq_true
  simp only [frameCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

attribute [local instance] wLeftAction

@[expose] def gensFrame
    (k : ℕ) : Kstab v0 := if h : k < 21 then (cGen ⟨k, h⟩)⁻¹ else 1

theorem decW_actFrame
    {k : ℕ} (hk : k < 21) (c : ℕ) :
    decW (actFrame k c) = gensFrame k • decW c := by
  rw [gensFrame, dite_eq_left hk, smul_def, inv_inv, wAct_cGen, rowsEnd_decW]
  rfl

@[expose] def G21 :
    Subgroup (Kstab v0) := Subgroup.closure
    (gensFrame '' {k | k < 21})

theorem G21_eq :
    G21 = Subgroup.closure (Set.range cGen) := by
  apply le_antisymm
  · rw [G21, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [gensFrame, dite_eq_left (show k < 21 from hk)]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have h : gensFrame k ∈ G21 := Subgroup.subset_closure ⟨k, k.2, rfl⟩
    have := Subgroup.inv_mem _ h
    rwa [gensFrame, dite_eq_left k.2, inv_inv] at this

theorem cGen_mem_G21
    (k : Fin 21) : cGen k ∈ G21 := by
  rw [G21_eq]
  exact Subgroup.subset_closure ⟨k, rfl⟩

theorem orbit_G21_wFr :
    MulAction.orbit G21 wFr =
    (fun i => decW frameOrbit[i]!) '' {i | i < frameOrbit.size} := by
  have h := orbit_of_natCertOK (G := Kstab v0) frameCheck_parts.1
    (fun k hk a _ => decW_actFrame hk a)
  rw [frameCheck_parts.2, ← wFr_eq_decW] at h
  exact h

theorem ncard_orbit_G21_wFr :
    (MulAction.orbit G21 wFr).ncard
    = 63 :=
    by
  have h := ncard_orbit_of_natCertOK (G := Kstab v0) frameCheck_parts.1
    (fun k hk a _ => decW_actFrame hk a) (fun a b ha hb e => decW_inj_valid ha hb e)
  rw [frameCheck_parts.2, ← wFr_eq_decW] at h
  rw [G21, h]
  rfl

theorem fCheck_eq_true : fCheck = true :=
  Certificates.certificate3055.2

theorem fCheck_parts : certOK amul fPerms idArr fCert = true ∧
    fCert.pts.size = 11520 ∧
    ((fCert.pts.toList.filter fixJ).map akey).mergeSort (fun a b => decide (a ≤ b)) =
      (octPerms.toList.map akey).mergeSort (fun a b => decide (a ≤ b)) := by
  have h := fCheck_eq_true
  simp only [fCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem F9_facts :
    Nat.card F9 = 11520 ∧
    ∀ x : Equiv.Perm (Fin 24), x ∈ F9 ↔ ∃ i < 11520, pt fCert i = x := by
  have h := card_closure_of_certOK (fun k hk => fPerms_PermArr k hk) decode_idArr fCheck_parts.1
  rw [fCheck_parts.2.1] at h
  exact h

theorem natCard_F9 :
    Nat.card F9 = 11520 := F9_facts.1

end CFSG.Monster.B.TwoA.Co2Inv
