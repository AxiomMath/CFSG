module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TCent
public import CFSG.Sporadic.FischerOddCore.Fi24Block
public import CFSG.Monster.B.TwoA.Par3.Main
public import Certificates.Kernel.J4Count.FixZK
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import Certificates.Kernel.J4Count.FixZKBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Blueprint CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native
  CFSG.Sporadic.FischerOddCore CFSG.Fischer
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] rAction

local notation "bP" => @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

section Fix


theorem jR_fi24z_eq : jR fi24z = bbar 0 * bbar 3 * bbar 13 * bbar 15 := by
  have h0 : (0 : Fin 24) ∉ ({3, 13, 15} : Finset (Fin 24)) := by decide
  have h3 : (3 : Fin 24) ∉ ({13, 15} : Finset (Fin 24)) := by decide
  have h13 : (13 : Fin 24) ∉ ({15} : Finset (Fin 24)) := by decide
  rw [jR_fi24z, bbarProd_insert h0, bbarProd_insert h3, bbarProd_insert h13, bbarProd_singleton]
  simp only [mul_assoc]

theorem card_fix_fi24z :
    Nat.card {k : Fin 306936 // fi24z • k = k} = 504 := by
  have e : ∀ k : Fin 306936, fi24z • k = (bbar 0 * bbar 3 * bbar 13 * bbar 15) • k := fun k => by
    rw [← jR_fi24z_eq, jR_smul]
  simp only [e]
  exact Certificates.certificate10510.fixZ

end Fix

theorem isConj_fi24R2_fi24z :
    IsConj fi24R2 fi24z := by
  have hz2 : fi24z * fi24z = 1 := by
    rw [← sq]
    exact fi24E_sq _ fi24z_mem
  have hz1 : fi24z ≠ 1 := fun h => by
    have e := card_fix_fi24z
    rw [h, Nat.card_congr (Equiv.subtypeUnivEquiv fun k => one_smul J k), Nat.card_eq_fintype_card,
      Fintype.card_fin] at e
    omega
  rcases isConj_tJ_or_r2 CFSG.Fischer.polarFacts CFSG.Sporadic.Fi23.d1_mem_localClass
      CFSG.Sporadic.Fi23.involution_cover hz2 hz1 with h | h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h.symm
    have e := card_fix_conj c tJ
    rw [hc, card_fix_fi24z, card_fix_tJ] at e
    omega
  · exact (h.trans isConj_t2_fi24R2).symm

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
