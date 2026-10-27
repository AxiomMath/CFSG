module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Defs
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.FilterData
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSmallLie.CatalogOrders
  CFSG.EvenSmallLie.Child3


theorem elevenSimpleCases_of_catalog {S : Type} [Group S] [IsSimpleGroup S]
    (hcat : Catalog S) (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hord : Nat.card S ∣ twE6Ord) (hlt : Nat.card S < twE6Ord)
    (h11 : 11 ∣ Nat.card S) :
    ¬ 3 ^ 6 ∣ Nat.card S ∨ Nat.card S = 9196830720 ∨
      Nat.card S = 25015379558400 ∨ Nonempty (S ≃* Carrier .Suz) ∨
      Nonempty (S ≃* Carrier .Fi22) := by
  rcases catalog_model_cases hcat hnonab with ⟨n, hn, ⟨e⟩⟩ |
    ⟨t, n, p, f, ht, hp, hf, hnmin, hn0, hnB, hadm, hc, -⟩ |
    ⟨p, f, hree⟩ | ⟨p, f, htits⟩ | ⟨s, ⟨e⟩⟩
  ·
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hcard : Nat.card S = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    left
    rw [hcard]
    exact filterE_alt hn (hcard ▸ hord)
  ·
    rw [hc] at hord hlt h11 ⊢
    have hC := lieSearchV_sound primes_twE6Ord lieSearch_twE6 ht hp hf hnmin hn0 hnB hadm hord
    simp only [filterCheckE, decide_eq_true_eq] at hC
    rcases hC h11 hlt with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  ·
    exact (false_of_reeTitsModel_twistedF4 hree hord not_two_pow_sixtySeven_dvd
      not_thirtySeven_dvd not_fortyOne_dvd).elim
  ·
    exact absurd (h11.trans (card_dvd_of_reeTitsModel_Tits htits)) not_eleven_dvd_tits
  ·
    have hM : s ≠ .M := by
      rintro rfl
      exact not_twentyNine_dvd ((twentynine_dvd_of_mulEquiv_M e).trans hord)
    have hTh : s ≠ .Th := by
      rintro rfl
      have hc : Nat.card S = 90745943887872000 := by
        rw [Nat.card_congr e.toEquiv]
        simpa only [Carrier] using CFSG.RankThree.PartOne.CTP.card_Th
      exact not_card_Th_dvd (hc ▸ hord)
    have hc : Nat.card S = sporadicCard s :=
      (Nat.card_congr e.toEquiv).trans (card_carrier s hTh hM)
    rw [hc] at hord h11 ⊢
    have hs := sporadicCheckE_true s
    simp only [sporadicCheckE, decide_eq_true_eq] at hs
    rcases hs hTh hM hord h11 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · subst h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    · subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))

theorem elevenSimpleCases_holds : ElevenSimpleCases := by
  intro S _ _ _ hS hnonab hord hlt h11
  exact elevenSimpleCases_of_catalog
    (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge S hnonab hS) hnonab hord hlt h11

end CFSG.StandardType.TwE6MaxEleven
