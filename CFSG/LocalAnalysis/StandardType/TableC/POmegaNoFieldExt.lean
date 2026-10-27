module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmModel
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.RankThree.PartOne.S11d.OrthCaseH

public section

namespace CFSG.StandardType.TableC

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec66T (centerQuotientEquivSelf)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

section NoFieldExt

theorem not_fieldExtCase_of_mulEquiv_orthDerived
    {X : Type} [Group X] {J : Subgroup X} {t : StatedLieTag} {f : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {R : QuadraticForm F W} (hR : (polarBilin R).Nondegenerate)
    (h8 : 8 ≤ finrank F W) (e : ↥J ≃* ↥(orthDerived R)) :
    ¬ GGSixLSevenFieldExtCase J t f := by
  rintro ⟨t', m', f', hff, hL', -⟩
  have hf : 1 ≤ f := by
    have h1 := Finite.one_lt_card (α := F)
    rw [hF] at h1
    by_contra h
    have : f = 0 := by omega
    subst this
    simp at h1
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨m, hm⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
  have hm4 : 4 ≤ m := by omega
  have hdim : finrank F W = 2 * m := by omega
  have hZG := OmNonsplit.center_eq_bot_of_mulEquiv hR (exists_threeSingular_of_dim R hR hm4 hdim) e
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega) hdim
    with he | ⟨b, c, hirr, he⟩
  · obtain ⟨e'⟩ := he
    have hLM := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (centerQuotientEquivSelf hZG).symm
      (lieModel_of_orthDerived_plus hm4 hf hF e' e)
    obtain ⟨-, -, hf'⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (Or.inl rfl)
      hLM hL'
    omega
  · obtain ⟨e'⟩ := he
    have hLM := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (centerQuotientEquivSelf hZG).symm
      (lieModel_of_orthDerived_minus hm4 hf hF hirr e' e)
    obtain ⟨-, -, hf'⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (Or.inr rfl)
      hLM hL'
    omega

end NoFieldExt

end CFSG.StandardType.TableC

end
