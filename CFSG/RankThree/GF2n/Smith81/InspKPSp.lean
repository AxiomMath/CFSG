module

public import CFSG.RankThree.GF2n.Smith81.InspKFacts
public import CFSG.RankThree.GF2n.Smith81.InspKStatements
public import CFSG.RankThree.GF2n.Smith81.InspKPSL
public import CFSG.RankThree.GF2n.Smith81.InspKSigma
public import CFSG.RankThree.GF2n.Smith81.InspKSpBase
public import CFSG.RankThree.GF2n.Smith81.InspKFrame
public import CFSG.RankThree.GF2n.Smith81.InspKSpCard
public import CFSG.RankThree.GF2n.Smith81.InspKSpCount
public import CFSG.RankThree.GF2n.Smith81.InspKPSLCore
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
  CFSG.SeitzReduction.SymplecticPilot CFSG.StandardType CFSG.LargeExtraspecial.A2Mod.Frame
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.RankThree.GF2n.Smith81.Insp.KFact

section CertBound


theorem KFact.exists_frame_psp {Y : Type} [Group Y] {D : Set Y} (hH : Hyp Y D) {m f : ℕ}
    (hf : 2 ≤ f) (hL : LieModel Y .PSp (m + 3) 2 f)
    (hroot : ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Ψ : StatedSp (m + 3) K →* Y),
      Nat.card K = 2 ^ f ∧ Function.Injective Ψ ∧ Function.Surjective Ψ ∧
      ∃ g : StatedSp (m + 3) K, Ψ (g * twoCentralElt (m + 3) 1 2 (0 : K) 1 * g⁻¹) ∈ D := by
  classical
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := by
    obtain ⟨d, hd, -⟩ := hH.nondeg
    exact ⟨d, hd⟩
  have hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d :=
    ⟨d₀, hd₀, KFact.exists_ne_mem_rootSet_of_card hH.root hf hroot hd₀⟩
  obtain ⟨hc, hs, hm⟩ := largeClosures hH hl
  have h := arsHyp_rootClass hH hc hs hm
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have hcardR : ∀ E ∈ rootClass D, Nat.card E = 2 ^ f := by
    rintro E ⟨d, hd, rfl⟩
    exact hroot d hd
  have hne2 : ∀ A ∈ rootClass D, Nat.card A ≠ 2 := by
    intro A hA h2
    have h3 := hcardR A hA
    rw [h2] at h3
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hk : 3 ≤ m + 3 := by omega
  rcases ARS.output_of_hyp Y (rootClass D) h with ⟨m', hm2, A, B, hX, hgen⟩ |
      ⟨m', hm4, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | hns
  · exfalso
    rcases Nat.lt_or_ge m' 3 with hm3 | hm3
    · obtain rfl : m' = 2 := by omega
      obtain ⟨f', hf', -, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
        (by simp)
    · obtain ⟨f', hf', -, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
        (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_D hR hiso hZ hm4 hgen
    exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
      (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E6 hR hiso hZ hgen
    exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
      (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E7 hR hiso hZ hgen
    exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
      (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E8 hR hiso hZ hgen
    exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
      (by simp)
  · obtain ⟨-, hdata⟩ := hns
    rcases hdata with hS | ⟨⟨F⟩⟩
    · exfalso
      rcases KFact.exists_lieModel_of_sigmaEqLambda h hS hne2 with ⟨n', f', hL'⟩ | ⟨f', hL'⟩ |
          ⟨f', hL'⟩
      · exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
          (by simp)
      · exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
          (by simp)
      · exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1
          (by simp)
    · have hmem : Nat.card ((F.D.rootGroup (Pi.single F.i₀ 1)).map F.Ψ) = 2 ^ f :=
        hcardR _ F.mem
      rcases KFact.nslFrame_cases F hZ hf hmem with
        ⟨n, K, _, _, _, Ψ, hn, hK, hLm, hinj, hsurj, i, hi, hmemR⟩ |
        ⟨n, K, _, _, b, c, hirr, Ψ, hn, hK, hLm, -⟩ | ⟨t, n, f', ht1, ht2, -, hL'⟩
      · obtain ⟨-, hnm, -⟩ := CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hLm
        subst hnm
        obtain ⟨d₁, hd₁, hmd⟩ := hmemR
        have hd₁mem : d₁ ∈ Subgroup.map Ψ
            ((Symplectic.rootDatum (m + 3) K).rootGroup (Pi.single i 1)) := by
          rw [hmd]
          exact rootSet_subset_rootGroup D d₁ ⟨hd₁, fun _ _ => Iff.rfl⟩
        obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp hd₁mem
        have hx1 : x ≠ 1 := by
          rintro rfl
          rw [map_one] at hxd
          have := hH.root.1 d₁ hd₁
          rw [← hxd, orderOf_one] at this
          omega
        obtain ⟨g, hg⟩ := KFact.exists_conj_twoCentralElt_of_short hi hx hx1
        exact ⟨K, inferInstance, inferInstance, inferInstance, Ψ, hK, hinj, hsurj, g, by
          rw [← hg, hxd]
          exact hd₁⟩
      · exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hLm).1
          (by simp)
      · exact absurd (CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hL').1 ht1

theorem k2PSp_holds : K2PSpStatement2 := by
  intro Y _ D k f hH hk hf hL hroot d hd
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  obtain ⟨K, _, _, _, Ψ, hK, hinj, hsurj, g, hgD⟩ := KFact.exists_frame_psp hH hf hL hroot
  right
  have hF4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set t : StatedSp (m + 3) K := twoCentralElt (m + 3) 1 2 (0 : K) 1 with ht
  let e : StatedSp (m + 3) K ≃* Y := MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  obtain ⟨d₀, hD⟩ := hH.isClass
  have hconj : IsConj (Ψ (g * t * g⁻¹)) d := by
    rw [hD] at hgD hd
    exact (isConj_comm.mp hgD).trans hd
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨w, rfl⟩ := hsurj c
  have hd0 : d = Ψ (w * g * t * (w * g)⁻¹) := by
    rw [← hc]
    simp only [map_mul, map_inv]
    group
  have hd' : d = e (w * g * t * (w * g)⁻¹) := hd0
  have hconjt : (w * g) * t * (w * g)⁻¹ = (MulAut.conj (w * g)) t := rfl
  have hO : Nat.card (pCoreOf 2 (Subgroup.centralizer ({d} : Set Y))) =
      Nat.card (wRadical K (1 : Fin (m + 3)) 2) := by
    rw [hd', KFact.card_pCoreOf_centralizer_mulEquiv e, hconjt,
      KFact.card_pCoreOf_centralizer_mulEquiv (MulAut.conj (w * g)) t,
      KFact.pCoreOf_centralizer_twoCentralElt_of_four_le hF4]
  have hC : Nat.card (Subgroup.centralizer ({d} : Set Y)) =
      Nat.card (wRadical K (1 : Fin (m + 3)) 2) *
        (Nat.card (StatedSp 1 K) * Nat.card (StatedSp (m + 1) K)) := by
    rw [hd', KFact.card_centralizer_mulEquiv e, hconjt,
      KFact.card_centralizer_mulEquiv (MulAut.conj (w * g)) t,
      KFact.card_centralizer_twoCentralElt]
  have hQ2 : IsPGroup 2 (wRadical K (1 : Fin (m + 3)) 2) := isPGroup_wRadical one_ne_two_fin
  have hQle : Nat.card (wRadical K (1 : Fin (m + 3)) 2) ≤ (2 ^ f) ^ (4 * (m + 3) - 5) := by
    have := KFact.card_wRadical_le (K := K) (n := m + 3) (p := 1) (q := 2) one_ne_two_fin
    rwa [hK] at this
  refine ⟨hO ▸ hQle, ?_⟩
  have hdvd : Nat.card (wRadical K (1 : Fin (m + 3)) 2) ∣ (2 ^ f) ^ (4 * (m + 3) - 5) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hQ2.exists_card_eq
    have hjle : j ≤ f * (4 * (m + 3) - 5) := by
      have h1 : 2 ^ j ≤ 2 ^ (f * (4 * (m + 3) - 5)) := by
        rw [← hj, pow_mul]
        exact hQle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    rw [hj, ← pow_mul]
    exact pow_dvd_pow 2 hjle
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [hC, KFact.card_statedSp_eq_ordBC (by omega) hK 1,
    KFact.card_statedSp_eq_ordBC (by omega) hK (m + 1), e2,
    mul_assoc ((2 ^ f) ^ (4 * (m + 3) - 5))]
  exact mul_dvd_mul hdvd dvd_rfl

end CertBound

end CFSG.RankThree.GF2n.Smith81.Insp
