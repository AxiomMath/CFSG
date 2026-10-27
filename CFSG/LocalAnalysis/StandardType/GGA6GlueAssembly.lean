module

public import CFSG.LocalAnalysis.StandardType.GGA6GlueDefs
public import CFSG.LocalAnalysis.StandardType.GGA6GlueReduce
public import CFSG.LocalAnalysis.StandardType.GGA6GlueToral
public import CFSG.LocalAnalysis.StandardType.GGA6GlueCoreSL
public import CFSG.LocalAnalysis.StandardType.GGA6GlueCoreF4
public import CFSG.LocalAnalysis.StandardType.GGA6GlueCoreNT
public import CFSG.LocalAnalysis.StandardType.GGA6GlueNoA6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RC0Input
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open scoped commutatorElement
open CFSG.StandardType.LieCore
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem ggA6QuotNoJAt_of_rc0
    (hRC0 : CFSG.StandardType.TableCRes.LangNontoralCompField)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) : GGA6QuotNoJAt t := by
  have hExc : GGExcFive t := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [GGExcFive]
  intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDn hdiag hEA hDc hJ hA6
  obtain ⟨hf, A, K, hAle, hAel, hAcard, hK, ⟨e⟩⟩ :=
    a6glue_reduce hExc hr hk hLie hp hp2 hDn hdiag hEA hDc hJ
  obtain ⟨e6⟩ := hA6
  have hKA6 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) := ⟨e.symm.trans e6⟩
  by_cases hT : IsToralSubgroup (langTag t) GGL A
  · obtain ⟨s, -, hfield⟩ := a6core_toral_SL ht hf hp hp2 hAle hAel hAcard hT hK
    exact a6glue_not_quotA6_of_fieldAt hfield.toAt hKA6
  · rcases a6glue_toral_or_nontoral hExc hf hp hp2 hAle hAel hAcard with hT' | ⟨hτ, hp3, hA9⟩
    · exact absurd hT' hT
    · have ht' : t = .E6 ∨ t = .twistedE6 := by
        rcases ht with rfl | rfl | rfl | rfl <;> simp_all [langTag]
      subst hp3
      rcases a6core_nontoral_E6 hRC0 ht' hf hAle hAel hA9 hT hK with hfield | ⟨-, h6048, hq6048⟩
      · exact a6glue_not_quotA6_of_fieldAt hfield hKA6
      · exact a6glue_not_quotA6_of_card (by omega) hKA6

theorem ggA6QuotF4f_holds :
    GGA6QuotF4f := by
  intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDn hdiag hEA hDc hJ hA6
  have hExc : GGExcFive .F4 := Or.inl rfl
  obtain ⟨hf, A, K, hAle, hAel, hAcard, hK, ⟨e⟩⟩ :=
    a6glue_reduce hExc hr hk hLie hp hp2 hDn hdiag hEA hDc hJ
  obtain ⟨e6⟩ := hA6
  have hKA6 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) := ⟨e.symm.trans e6⟩
  have hT : IsToralSubgroup (langTag .F4) GGL A := by
    rcases a6glue_toral_or_nontoral hExc hf hp hp2 hAle hAel hAcard with hT | ⟨hτ, -, -⟩
    · exact hT
    · exact absurd hτ (by simp [langTag])
  obtain ⟨s, -, hfield⟩ := a6core_toral_F4 rfl hf hp hp2 hAle hAel hAcard hT hK
  rcases hfield with hfield | ⟨hf1, -, -, -⟩
  · exact absurd hKA6 (a6glue_not_quotA6_of_fieldAt hfield)
  · exact hf1

end CFSG.StandardType.A6Red
