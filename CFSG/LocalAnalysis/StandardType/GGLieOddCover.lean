module

public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverLift
public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverModel
public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverSplit
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.Timmesfeld.RankTwo.Presentation
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.StandardType.LieOddCover

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem ggLieOddCover_holds :
    GGLieOddCover := by
  haveI hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_⟩
  · intro t n f ht hadm Jb hJbG hJbFin hperf hodd hJ
    haveI hfinU : Finite (ggU t n f).K :=
      CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (t := t) ht hadm
    obtain ⟨q, hq, hqk⟩ := exists_ggU_central_cover_of_lieModel ht hadm hJ
    exact ggOddCover_lift (oddCentralSplit_ggU_pos ht hadm) hperf hodd hq hqk
  · intro g hg Jb hJbG hJbFin hperf hodd hJ
    let F : Type := GaloisField 2 (3 * g)
    let σ : F →+* F := iterateFrobenius F 2 g
    have hFcard : Nat.card F = (2 ^ g) ^ 3 := by
      show Nat.card (GaloisField 2 (3 * g)) = (2 ^ g) ^ 3
      rw [GaloisField.card 2 (3 * g) (by omega), ← pow_mul, mul_comm 3 g]
    have hσq : ∀ c : F, σ c = c ^ (2 ^ g) := by
      intro c
      show iterateFrobenius (GaloisField 2 (3 * g)) 2 g c = c ^ (2 ^ g)
      rw [iterateFrobenius_def]
    have hσ3 : ∀ c : F, σ (σ (σ c)) = c :=
      fun c => CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hFcard hσq c
    refine ⟨F, inferInstance, inferInstance, σ, ⟨hg, hFcard, hσq⟩, ?_⟩
    haveI hfinGL : Finite (CFSG.Blueprint.Chevalley.ModGL
        CFSG.LieType.Steinberg.TwistedD4.d4 F) :=
      CFSG.LieType.Chevalley.finite_modGL
    haveI hfinAdj : Finite (CFSG.Blueprint.Chevalley.adjointGroup
        CFSG.LieType.Steinberg.TwistedD4.d4 F) := Subtype.finite
    haveI hfinU : Finite (triD4Universal F σ).K := Subtype.finite
    have hsplit : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (triD4Universal F σ).K := by
      intro E hEG hEfin π hπ hker hodd
      obtain ⟨s, hs, -, -⟩ :=
        CFSG.SectionRank.triality_even_central_odd_extension_splitting (σ := σ) hσ3 hπ hker hodd
      exact ⟨s, hs⟩
    have hmodel : LieModel
        ((triD4Universal F σ).K ⧸ Subgroup.center (triD4Universal F σ).K) .trialityD4 0 2 g :=
      CFSG.Timmesfeld.lieModel_twistedD4_quotient Nat.prime_two hg hFcard σ hσq
    have hU : ChevalleyExceptionalModel
        ((triD4Universal F σ).K ⧸ Subgroup.center (triD4Universal F σ).K) .trialityD4 2 g :=
      hmodel.chevalleyExceptionalModel (by decide)
    have hJ' : ChevalleyExceptionalModel (Jb ⧸ Subgroup.center Jb) .trialityD4 2 g :=
      hJ.chevalleyExceptionalModel (by decide)
    obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique hU hJ'
    refine ggOddCover_lift hsplit hperf hodd
      (q := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)))
      ?_ ?_
    · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
    · intro k hk
      have h1 : e (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K) k) = 1 := hk
      rw [map_eq_one_iff _ e.injective] at h1
      exact (QuotientGroup.eq_one_iff k).1 h1

end CFSG.StandardType.LieOddCover
