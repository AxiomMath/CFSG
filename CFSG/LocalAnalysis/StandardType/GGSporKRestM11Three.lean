module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestFStarNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSporKRestOverP
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTransport
public import Certificates.Certificate1023006
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Blueprint CFSG.Sporadic.Mathieu

private theorem ggSporKRestM11_exists :
    ∃ S₀ : Sylow 3 ↥NativeSporadic.M11,
      (∀ Y : Subgroup ↥NativeSporadic.M11,
        Subgroup.normalizer ((S₀ : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ≤ Y →
          Y = Subgroup.normalizer ((S₀ : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ∨
            Y = ⊤) ∧
      IsPGroup 3 ↥(CFSG.generalizedFitting
        ↥(Subgroup.normalizer ((S₀ : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11))) :=
  Certificates.certificate1023006

noncomputable def m11S0 :
    Sylow 3 ↥NativeSporadic.M11 :=
  Classical.choose ggSporKRestM11_exists

theorem sporKRest_M11_normalizer_maximal :
    ∀ Y : Subgroup ↥NativeSporadic.M11,
      Subgroup.normalizer ((m11S0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ≤ Y →
        Y = Subgroup.normalizer ((m11S0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ∨
          Y = ⊤ :=
  (Classical.choose_spec ggSporKRestM11_exists).1

theorem sporKRest_M11_fstar_normalizer :
    IsPGroup 3 ↥(CFSG.generalizedFitting
      ↥(Subgroup.normalizer ((m11S0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11))) :=
  (Classical.choose_spec ggSporKRestM11_exists).2

theorem sporKRest_coverOrUnmarked_M11_3_carrier :
    SporKRestCoverOrUnmarked 3 ↥NativeSporadic.M11 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ggSporKRest_coverOrUnmarked_of_fstar_isPGroup (by norm_num)
    (sporKRest_fstar_of_normalizer_maximal m11S0 sporKRest_M11_normalizer_maximal
      sporKRest_M11_fstar_normalizer)

theorem sporKRest_coverOrUnmarked_M11_3 :
    SporKRestCoverOrUnmarked 3 (TauCeti.CFSGIndex.sporadic .M11).Group := by
  letI : Mul TauCeti.SporadicName.M11.Group := Monoid.toMul
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  show SporKRestCoverOrUnmarked 3 TauCeti.SporadicName.M11.Group
  exact SporKRestCoverOrUnmarked.of_mulEquiv e sporKRest_coverOrUnmarked_M11_3_carrier

end CFSG.StandardType.SporadicShape
