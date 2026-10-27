
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase

public import Certificates.Certificate16022
public import CFSG.Monster.B.Co2.MatrixW

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem wAct_alpha
    (i : Fin 24) : wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ = rowsEnd (genQuotMatrix i) :=
  eq_rowsEnd_of (wAct_alpha_qbW i)

theorem supp_dC :
    supp ((dC : C) : Fin 24 → ZMod 2) = Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8 :=
  Certificates.certificate16022.1

theorem kind_twelve : (genRecord 12).kind = .codeSign :=
  Certificates.certificate16022.2.1

theorem word_twelve : (genRecord 12).word = [4, 3] :=
  Certificates.certificate16022.2.2.1

theorem kind_twentythree : (genRecord 23).kind = .xiSign :=
  Certificates.certificate16022.2.2.2.1

theorem word_twentythree : (genRecord 23).word = [0, 3] :=
  Certificates.certificate16022.2.2.2.2.1

theorem alpha12_eq : alpha 12 = QuotientGroup.mk (gO dC) := by
  unfold alpha
  rw [kind_twelve]
  change frameWordQ (genRecord 12).word = _
  rw [word_twelve]
  change frameQ (4 : ℤ).toNat * (frameQ (3 : ℤ).toNat * 1) = _
  rw [show (4 : ℤ).toNat = 4 from rfl, show (3 : ℤ).toNat = 3 from rfl, mul_one,
    frameQ_sign (by norm_num) (by norm_num), frameQ_sign (by norm_num) (by norm_num),
    ← QuotientGroup.mk_mul, ← gO_add, dC, add_comm]
  rfl

theorem alpha23_eq :
    alpha 23 = QuotientGroup.mk (xiO * gO (bC 0)) := by
  unfold alpha
  rw [kind_twentythree]
  change frameWordQ (genRecord 23).word = _
  rw [word_twentythree]
  change frameQ (0 : ℤ).toNat * (frameQ (3 : ℤ).toNat * 1) = _
  rw [show (0 : ℤ).toNat = 0 from rfl, show (3 : ℤ).toNat = 3 from rfl, mul_one,
    frameQ_eq (by norm_num : 0 < 15), frameGen_of_eq_zero (g := ⟨0, by norm_num⟩) rfl,
    frameQ_sign (by norm_num) (by norm_num), ← QuotientGroup.mk_mul]
  rfl

@[expose] def rK :
    Kstab v0 := ⟨alpha 12, alpha_mem_Kv 12⟩

@[expose] def aK :
    Kstab v0 := ⟨alpha 23, alpha_mem_Kv 23⟩

theorem wAct_rK :
    wAct v0 rK = rowsEnd (genQuotMatrix 12) := wAct_alpha 12

theorem fPerms_PermArr : ∀ k < 9, PermArr fPerms[k]! = true :=
  Certificates.certificate16022.2.2.2.2.2.1

theorem fPerms_AutArr : ∀ k < 9, AutArr fPerms[k]! :=
  Certificates.certificate16022.2.2.2.2.2.2.1

theorem fPerms_fix01 :
    ∀ k < 9, (fPerms[k]!)[0]! = 0 ∧ (fPerms[k]!)[1]! = 1 ∨
      (fPerms[k]!)[0]! = 1 ∧ (fPerms[k]!)[1]! = 0 :=
  Certificates.certificate16022.2.2.2.2.2.2.2.1

theorem fPerms_octad :
    ∀ k < 9, ∀ i < 24, (i < 8 ↔ (fPerms[k]!)[i]! < 8) :=
  Certificates.certificate16022.2.2.2.2.2.2.2.2.1

theorem fRows24_ok :
    ∀ k < 9, permRowsOK fPerms[k]! fRows24[k]! = true :=
  Certificates.certificate16022.2.2.2.2.2.2.2.2.2.1

theorem fRows22_ok :
    ∀ k < 9, quotRowsOK fRows24[k]! fRows22[k]! = true :=
  Certificates.certificate16022.2.2.2.2.2.2.2.2.2.2

@[expose] def fAut (k : Fin 9) : AutPerm :=
  ⟨decode fPerms[(k : ℕ)]!, mem_AutPerm_of_arr (fPerms_PermArr k k.2) (fPerms_AutArr k k.2)⟩

theorem coe_fAut (k : Fin 9) :
    ((fAut k : AutPerm) : Equiv.Perm (Fin 24)) = decode fPerms[(k : ℕ)]! := rfl

theorem fAut_apply (k : Fin 9) (i : Fin 24) :
    (((fAut k : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) = (fPerms[(k : ℕ)]!)[(i : ℕ)]! :=
  decode_apply (fPerms_PermArr k k.2) i

theorem fAut_mem_Ppair (k : Fin 9) : fAut k ∈ Ppair := by
  rw [mem_Ppair_iff]
  rcases fPerms_fix01 k k.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left
    exact ⟨Fin.ext ((fAut_apply k 0).trans h0), Fin.ext ((fAut_apply k 1).trans h1)⟩
  · right
    exact ⟨Fin.ext ((fAut_apply k 0).trans h0), Fin.ext ((fAut_apply k 1).trans h1)⟩

@[expose] def fK
    (k : Fin 9) : Kstab v0 := permK (fAut_mem_Ppair k)

theorem wAct_fK
    (k : Fin 9) : wAct v0 (fK k) = rowsEnd fRows22[(k : ℕ)]! :=
  wAct_of_rows _ (kOp_permK_dec (fPerms_PermArr k k.2) (coe_fAut k) (fAut_mem_Ppair k)
    (fRows24_ok k k.2)) (fRows22_ok k k.2)

@[expose] def cGen
    (k : Fin 21) : Kstab v0 :=
  if h : (k : ℕ) < 9 then fK ⟨k, h⟩ else ⟨alpha ⟨k + 3, by omega⟩, alpha_mem_Kv _⟩

theorem cGen_of_lt
    {k : Fin 21} (h : (k : ℕ) < 9) : cGen k = fK ⟨k, h⟩ := dite_eq_left h

theorem cGen_of_ge
    {k : Fin 21} (h : 9 ≤ (k : ℕ)) :
    cGen k = ⟨alpha ⟨k + 3, by omega⟩, alpha_mem_Kv _⟩ := dite_eq_right (by omega)

theorem wAct_cGen
    (k : Fin 21) : wAct v0 (cGen k) = rowsEnd (cRows k) := by
  by_cases h : (k : ℕ) < 9
  · rw [cGen_of_lt h, wAct_fK, cRows, ite_eq_left h]
  · rw [cGen_of_ge (by omega), wAct_alpha, cRows, ite_eq_right h]
    rfl

end CFSG.Monster.B.TwoA.Co2Inv
