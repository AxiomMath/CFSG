
module

public import CFSG.Quasithin.Background.A3Structure36BCasesBase

public import CFSG.Quasithin.Background.A3Structure36BElem
public import CFSG.Quasithin.Background.A3Structure36BHeis
public import CFSG.Quasithin.Background.A3Structure36BCaseAux

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem case4 (hF : A36CaseBFacts) (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K)
    (h5 : IsSL2 5 (X ⧸ CFSG.fittingSubgroup X)) : A36Case4 X := by
  have hfin : Finite X := h.finite
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  refine ⟨generalizedFitting_eq_fitting h, inferInstance, h5, ?_⟩
  intro p hp hpF
  have hπ := isPi_of_dvd_card_fitting hF h hK hp hpF
  obtain ⟨D, hDK⟩ := hK.prime p hp hπ
  have hDn : D.K.Normal := D.normal_K
  have hmod : p % 5 = 1 ∨ p % 5 = 4 ∨ p = 5 := by
    rcases D.sl2 with hs | ⟨hp5, -⟩
    · have hs' : IsSL2 p (X ⧸ CFSG.fittingSubgroup X) :=
        isSL2_quotient_congr (hDK.trans hKF) hs
      exact Or.inr (Or.inr (eq_of_isSL2 hp (by norm_num) hs' h5))
    · omega
  refine ⟨hmod, ?_⟩
  obtain ⟨t, ht, ht2, htK⟩ := exists_involution h hK
  rcases D.iso with hE | hH
  · right
    obtain ⟨-, -, e, he1, ⟨φ⟩, -⟩ := elem_case h hK hp D hDK hE ht2 htK
    exact ⟨e, he1, ⟨φ⟩⟩
  · left
    have hP : D.P = ⊤ := eq_top_of_isPOnePlusTwo h hK hF.l2mult hp D hDK hH
    exact isPOnePlusTwo_of_mulEquiv
      ((MulEquiv.subgroupCongr hP).trans Subgroup.topEquiv) hH

end CFSG.Quasithin.A36B
