module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEight
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res423Four

theorem census424_of_centCharThree {X P : Type} [Group X] [Finite X] [Group P] [Finite P]
    (e : X ≃* P)
    (hP : ∀ z : P, orderOf z = 3 →
      IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set P))) :
    Census424 X := by
  intro D c d K h
  exfalso
  have hc3 : c ^ 3 = 1 := h.maximal.prop.2 c h.c_mem
  have hco : orderOf (e c) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hc3 h.c_ne_one
  have hHas : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (MulAut.conj c)) := by
    rw [Item424Res2.fixSub_conj_eq_centralizer_singleton]
    exact Sec11.KS11Lie2Proof.hasType424_of_mem h.mem_thetaComponentsIn h.isType424
  have hT := hHas.of_mulEquiv (Sec11.KS11Lie2Proof.fixSubCongr e (MulAut.conj c))
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    Item424Res2.fixSub_conj_eq_centralizer_singleton] at hT
  exact Sec11.KS11Lie3Proof.not_hasType424_of_isCharacteristicP (hP (e c) hco) hT

end Res423Four

open Res423Four

theorem k424Inner46EightRest_holds : K424Inner46EightRest := by
  rintro X _ _ (⟨⟨e⟩⟩ | ⟨⟨φ⟩⟩) - hZ
  · exact census424_of_centCharThree e Sec6.kCentCharThreeL43_holds
  · exact census424_of_centCharThree
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ)
      Sec6.kCentCharThreeU43_holds

theorem k424Inner46Eight_holds :
    K424Inner46Eight :=
  k424Inner46Eight_of k424Inner46EightRest_holds

end CFSG.RankThree.PartTwo.Sec4
