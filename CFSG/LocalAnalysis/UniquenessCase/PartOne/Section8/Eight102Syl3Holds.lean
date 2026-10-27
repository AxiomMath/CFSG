module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Transport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U5Torus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U5Fix
import CFSG.Quasithin.H13.U4ParModel
import CFSG.LocalAnalysis.EvenBN.U5.Setting
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Syl3

theorem kU45Syl3_holds : KU45Syl3 := by
  intro X _ _ n hX S hS hSi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  suffices OmegaNine X S ∧ FixOmega X S from this
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.LocalAnalysis.EvenBN.U5.exists_hypPSU_equiv one_le_two hU5
    have : Finite (hypPSU h 2 1) := Finite.of_equiv X e.toEquiv
    obtain ⟨hp, hi, hE, hc⟩ := sylow_three_hypPSU_two_one h
    obtain ⟨φ, hφ⟩ := CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq e
      (hp.toSylow hi) (hS.toSylow hSi)
    simp only [IsPGroup.toSylow_coe] at hφ
    subst hφ
    have := hE.1
    exact ⟨OmegaNine.map φ ⟨(torusPow h 2 1 3).map (hypProj h 2 1), le_rfl, hE, hc,
      fun s hs _ => hs⟩, fixOmega_of_lieModel_PSU_five hU5 hS hSi inferInstance⟩
  · obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU4
    have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
    obtain ⟨hp, hi, hO, hF⟩ := sylow_three_hypSU_two_zero h hn
    obtain ⟨φ, hφ⟩ := CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq e.symm
      (hp.toSylow hi) (hS.toSylow hSi)
    simp only [IsPGroup.toSylow_coe] at hφ
    subst hφ
    exact ⟨hO.map φ, hF.map φ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
