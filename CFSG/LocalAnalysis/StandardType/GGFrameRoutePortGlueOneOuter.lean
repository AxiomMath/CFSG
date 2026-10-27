module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueOne
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGRawAutRest
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
import CFSG.LocalAnalysis.StandardType.GGOuterThreeRankPlusFour
import CFSG.Mathlib.GroupTheory.CardLeSqOfTower
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.StandardType

theorem ggOuterThreeRank_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGOuterThreeRank R') : GGOuterThreeRank R := by
  intro A hA hAI
  have hcard : Nat.card (A.map (MulAut.congr e).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hAI' : A.map (MulAut.congr e).toMonoidHom ⊓
      (MulAut.conj : R' →* MulAut R').range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxI⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxA
    obtain ⟨r', hx⟩ := MonoidHom.mem_range.mp hxI
    have hconj : MulAut.conj (e.symm r') = a := by
      apply (MulAut.congr e).injective
      rw [CFSG.StandardType.mulAut_congr_conj, MulEquiv.apply_symm_apply]
      exact hx
    have ha1 : a = 1 := by
      have haI : a ∈ A ⊓ (MulAut.conj : R →* MulAut R).range :=
        ⟨ha, ⟨e.symm r', hconj⟩⟩
      simpa [hAI] using haI
    rw [ha1, map_one]
    simp
  rw [← hcard]
  exact h _ (hA.map (MulAut.congr e).toMonoidHom) hAI'

theorem ggOuterThreeRank_of_pCyclic {R : Type} [Group R] {I F : Set (MulAut R)}
    (hpc : GGRawPCyclic 3 R I F) (hO : GGOutdiagCyclic R I) (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : GGOuterThreeRank R := by
  intro A hA hAI
  obtain ⟨J, S, hJI, hJS, hJn, ⟨g, hg, hgen⟩, h3⟩ := hpc hs hna
  obtain ⟨φ₀, hφ₀⟩ := hO
  have hJ : J ≤ (MulAut.conj : R →* MulAut R).range ⊔ Subgroup.zpowers φ₀ := by
    intro x hx
    exact hφ₀ (hJI ▸ hx)
  have hAS : A ≤ S := fun α hα => h3 α ⟨1, by simpa using hA.2 α hα⟩
  have h := CFSG.card_le_sq_of_two_cyclic_layers (p := 3) (by norm_num : 0 < 3)
    (N := (MulAut.conj : R →* MulAut R).range) (J := J) (S := S) (A := A)
    (φ₀ := φ₀) (g := g) hJn hg hgen hJ hAS hA.2 hAI
  simpa using h

theorem ggOuterThreeRank_omegaPlusFour {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGOuterThreeRank (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) :=
  ggOuterThreeRank_of_mulEquiv (RecipeFieldOmega.plusEquiv (K := K) (m := 4) (by norm_num))
    fun A hA hAI => AutOm.card_le_nine_of_plusFour plusFourTrialityInput_holds hA.2 hAI

section Holds


theorem ggOuterThreeRankInput_holds : GGOuterThreeRankInput := by
  intro lab hlab
  by_cases hD : lab.tag = .D ∧ lab.rank = 4
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at hD
    obtain ⟨rfl, rfl⟩ := hD
    exact largeEvenLabelAll_omegaPlus
      (P := LargeEvenSimpleGuard fun R _ _ _ => GGOuterThreeRank R)
      rfl le_rfl fun K _ _ _ _ _ _ => ggOuterThreeRank_omegaPlusFour
  · have hne : GGNotD4Three 3 lab := fun h => hD ⟨h.1, h.2.1⟩
    have hpc : LargeEvenLabelAll lab (GGRawPCyclic 3) := by
      by_cases hdone : GGRawPCyclicDoneLabel lab
      · exact ggRawPCyclicOn_done 3 Nat.prime_three (by norm_num) lab hlab hdone
      by_cases ho : GGOmegaLabel lab
      · exact ggRawPCyclicOn_omega plusFourTrialityInput_holds 3 Nat.prime_three
          (by norm_num) lab hlab ⟨ho, hne⟩
      · exact ggRawPCyclicOn_rest5 3 Nat.prime_three (by norm_num) lab hlab ⟨hne, hdone, ho⟩
    have hout := largeEvenLabelAll_outdiag_simple hlab
    refine (largeEvenLabelAll_and hpc hout).mono ?_
    intro R _ I F h hs hna
    exact ggOuterThreeRank_of_pCyclic h.1 (h.2 hs hna) hs hna

end Holds

end CFSG.StandardType.FrameRoute

end
