
module

public import CFSG.Monster.B.TwoA.Sp8.PsiBase

public import CFSG.Monster.B.TwoA.Base.Space34A
public import Certificates.Certificate16028
public import CFSG.Monster.B.TwoA.Sp8.Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

theorem pairW24_eq_decW :
    pairW 2 4 offPair24 0 = decW 20480 :=
  pairW_eq_decW offPair24 (r := 81920) (by exact Certificates.certificate16028.1) (by decide)

theorem pairW25_eq_decW :
    pairW 2 5 offPair25 0 = decW 36864 :=
  pairW_eq_decW offPair25 (r := 147456) (by exact Certificates.certificate16028.2.1) (by decide)

theorem pairW26_eq_decW :
    pairW 2 6 offPair26 0 = decW 69632 :=
  pairW_eq_decW offPair26 (r := 278528) (by exact Certificates.certificate16028.2.2.1) (by decide)

@[expose] def uhatE : Ehat := ⟨uhat, uhat_mem_Ehat⟩

theorem lamX_form_eq :
    (fun k : Fin 24 => if P ((dC : C) : Fin 24 → ZMod 2) = 0 then
      2 * bitLift (((dC : C) : Fin 24 → ZMod 2) k) else
      2 * (1 - bitLift (((dC : C) : Fin 24 → ZMod 2) k))) = fun k : Fin 24 => twoD k :=
  Certificates.certificate16028.2.2.2

theorem lamX_dC : lamX dC = dec 122883 := by
  rw [lamX_eq, cls_congr _ lamX_form_eq]
  exact cls_eq_dec_of_rowCheck _ (by decide +kernel)

theorem phi0_coordOf_XQ_dC :
    phi0 (coordOf (XQ ⟨dC, 0⟩)) = dec 122883 := by
  rw [coordOf_XQ, phi0_apply, lamT, add_assoc, ← two_smul (ZMod 2),
    show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero, lamX_dC]

theorem dec_122883 :
    dec 122883 = dec 118787 + v0 := by
  rw [← dec_v0, ← dec_xor]
  rfl

theorem psiW_uhat :
    psiW uhatE = decW 30721 := by
  have e : uhatE = ehatEquiv ⟨ubar, ubar_mem_Ebar⟩ := rfl
  rw [e, psiW_ehatEquiv]
  have e2 := psiBar_kappa_rho XQ_dC_mem_centralizer
  change wvEquiv hv0 (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv (XQ ⟨dC, 0⟩),
    rhoEquiv_mem_Cgen XQ_dC_mem_centralizer⟩, kappa_rho_mem_Ebar XQ_dC_mem_centralizer⟩)) = _
  rw [e2, toAdd_ofAdd, wvEquiv_mk]
  obtain ⟨hm, he⟩ := decW_eq_mk 30721
  rw [he, Submodule.Quotient.eq]
  have h1 : CFSG.Monster.B.Co2.Native.actD 22 CFSG.Monster.B.Co2.Native.quotientBasis 30721 =
      118787 := by decide
  change ((phi0 (coordOf (XQ ⟨dC, 0⟩)) -
    dec (CFSG.Monster.B.Co2.Native.actD 22 CFSG.Monster.B.Co2.Native.quotientBasis 30721)) : L2) ∈
      vLineL v0
  rw [h1, phi0_coordOf_XQ_dC, dec_122883, add_sub_cancel_left]
  exact Submodule.subset_span rfl

theorem psiW_d24 :
    psiW (dhatE 2 4) = decW 20480 :=
  (psiW_dhat (by decide) offPair24).trans pairW24_eq_decW

theorem psiW_d25 :
    psiW (dhatE 2 5) = decW 36864 :=
  (psiW_dhat (by decide) offPair25).trans pairW25_eq_decW

theorem psiW_d26 :
    psiW (dhatE 2 6) = decW 69632 :=
  (psiW_dhat (by decide) offPair26).trans pairW26_eq_decW

end CFSG.Monster.B.TwoA.Sp8
