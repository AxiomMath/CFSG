module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
import CFSG.LocalAnalysis.StandardType.ZS.TableMonomial
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableOrth
import CFSG.LocalAnalysis.StandardType.ZS.TableOrthClass
import CFSG.LocalAnalysis.StandardType.ZS.TableExc
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem tableConclusions_of_family (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {J : Subgroup (U ≃ₗ[ZMod p] U)} (hF : Family p J)
    (hT : TableHyp p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (h18 : PropOneEightAt p (Module.finrank (ZMod p) U)) :
    TableConclusions p (Module.finrank (ZMod p) U) J := by
  cases hF with
  | weyl h => exact tableConclusions_of_linWeyl hp h3 h hT hprim
  | slpm hA =>
      exact ((not_transvectionFree_of_mem_iff_det (by omega) hA) hT.transvectionFree).elim
  | orth Q hQ hA => exact tableConclusions_orth hp h3 hQ hA
  | orthClass Q c hQ hc hJ => exact tableConclusions_orthClass hp h3 hQ hc hJ hT
  | gmmn f i₀ i₁ ζ m hi hm hζ hA =>
      rw [Module.finrank_eq_card_basis f, Fintype.card_fin]
      exact tableConclusions_of_monomial f hp
        (by simpa [Module.finrank_eq_card_basis f] using h3) hi (Or.inl hA) hT
  | g2mmn f i₀ i₁ ζ m hi hm hζ hA =>
      rw [Module.finrank_eq_card_basis f, Fintype.card_fin]
      exact tableConclusions_of_monomial f hp
        (by simpa [Module.finrank_eq_card_basis f] using h3) hi (Or.inr hA) hT
  | exc k hadm hdeg hord hcen hd hone hmodel =>
      exact tableConclusions_exc hp k hadm hdeg hcen hd hone hT hprim h18
  | h4 _ hdeg _ hneg hd hone =>
      rw [hdeg]
      exact tableConclusions_of_dMax_four hp hdeg hT hprim hneg hone hd (by norm_num)
        (by simpa [hdeg] using h18)

theorem tableConclusions_of_useInputAt (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) (hU : UseInputAt (Module.finrank (ZMod p) U))
    (h18 : PropOneEightAt p (Module.finrank (ZMod p) U)) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hT : TableHyp p J) : TableConclusions p (Module.finrank (ZMod p) U) J := by
  have hA : AbsIrred p J := absIrred_of_reflGen hT.reflGen hT.irreducible
  by_cases himp : Quasithin.SimsG4.IsImprimitiveOnV J
  · obtain ⟨b, i₀, i₁, ζ, hi, hJ⟩ := exists_basis_eq_gmmn_or_g2mmn hp rfl h3 hT.reflGen hA himp
    exact tableConclusions_of_monomial b hp h3 hi hJ hT
  · exact tableConclusions_of_family hp h3 (hU p U J hp rfl hT.reflGen hA) hT himp h18

theorem tableFactsAt_of_useInputAt (hp : p ≠ 2) {m : ℕ} (hm : 3 ≤ m) (hU : UseInputAt m)
    (h18 : PropOneEightAt p m) : TableFactsAt p m := by
  refine tableFactsAt_of_forall fun U _ _ _ J hdim hT => ?_
  rw [← hdim]
  exact tableConclusions_of_useInputAt hp (hdim.symm ▸ hm) (hdim.symm ▸ hU) (hdim.symm ▸ h18) hT

end CFSG.StandardType.ZS
