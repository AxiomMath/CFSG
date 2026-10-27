
module

public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.Co2.Data

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA.Census

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16022

private theorem supp_dC_0 :
    supp ((dC : C) : Fin 24 → ZMod 2) = Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8 := by
  decide +kernel

private theorem kind_twelve_1 : (genRecord 12).kind = .codeSign := by
  decide +kernel

private theorem word_twelve_2 : (genRecord 12).word = [4, 3] := by
  decide +kernel

private theorem kind_twentythree_3 : (genRecord 23).kind = .xiSign := by
  decide +kernel

private theorem word_twentythree_4 : (genRecord 23).word = [0, 3] := by
  decide +kernel

private theorem fPerms_PermArr_5 : ∀ k < 9, PermArr fPerms[k]! = true := by
  decide +kernel

private theorem fPerms_AutArr_6 : ∀ k < 9, AutArr fPerms[k]! := by
  decide +kernel

private theorem fPerms_fix01_7 : ∀ k < 9, (fPerms[k]!)[0]! = 0 ∧ (fPerms[k]!)[1]! = 1 ∨
    (fPerms[k]!)[0]! = 1 ∧ (fPerms[k]!)[1]! = 0 := by
  decide +kernel

private theorem fPerms_octad_8 : ∀ k < 9, ∀ i < 24, (i < 8 ↔ (fPerms[k]!)[i]! < 8) := by
  decide +kernel

private theorem fRows24_ok_9 : ∀ k < 9, permRowsOK fPerms[k]! fRows24[k]! = true := by
  decide +kernel

private theorem fRows22_ok_10 : ∀ k < 9, quotRowsOK fRows24[k]! fRows22[k]! = true := by
  decide +kernel

end CertificateChecks.Batch16022

namespace Certificates

end Certificates
