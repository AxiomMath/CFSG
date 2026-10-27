module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS14
public import CFSG.Quasithin.Vol2.Ch10SecC9Irr
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS13

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isShort2_of_blockU_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hU : blockU L = fsuUL T L I) : IsShort2 L := by
  have hLc := SecE.mem_cComp_L0T hyp
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    SecE.pCoreOf_L_le_centralizer h37 h38 h3228 hyp (Or.inr h2)
  have hVV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hZ : blockZ L = ⊥ := by
    rw [blockZ, hU]
    exact SecF.fsuUL_inf_centralizer_eq_bot h2
  obtain ⟨⟨e⟩, hcU, hA⟩ := h2
  have hirr := SecC.irrG_of_isIrrSec (SecC.isIrrSec_of_altNat5 hA)
  refine ⟨Setup.Offender.noPQuotient_of_perfect Nat.prime_two
    (Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hLc)),
    A4.charTwo_of_subnormal (subnormal_of_mem_cComp hLc) (SecA.charTwo_L0T hyp), ⟨?_, ?_⟩,
    Or.inl (SecD.isQuasisimple_of_mulEquiv_alt5 e), ?_, ?_⟩
  · rw [hU]
    refine le_inf (SecE.fsuUL_le_pCoreOf_L hyp) fun v hv => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun o ho => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hOC ho) v (hVV hv)).symm
  · rw [hU]
    exact fun x hx => (SecA.isElemAbelian_fsuVM hyp).2 x (hVV hx)
  · rw [hZ, hU]
    exact bot_lt_iff_ne_bot.mpr hirr.1
  · rw [hZ, hU]
    intro W _ hWU hLW
    exact hirr.2 W hWU hLW

theorem isA5Block_of_relIndex (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) {q : G} (hqL : q ∈ L) (hq3 : orderOf q = 3)
    (hc16 : (Subgroup.centralizer ({q} : Set G)).relIndex (T ⊓ L) ≤ 16) :
    IsShort2 L ∧ IsAltType L 5 := by
  have hU := blockU_eq_fsuUL_of_relIndex hyp h2 hqL hq3 hc16
  exact ⟨isShort2_of_blockU_eq h37 h38 h3228 hyp h2 hU,
    isAltType_of_blockU_eq h37 h38 h3228 hyp h2 hU⟩

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
