module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniquePair
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem unitarySwapRowUnique_of_pairExclusion (hP : UnitarySwapPairExclusion h n)
    (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) (hnf : (n, f) ≠ (6, 1))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n)))) :
    UnitarySwapRowUnique e t := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h3 => by
    have := congrArg Prod.fst h3
    simp only at this
    omega
  obtain ⟨G₁, hq, h₁₂, hsup, hδ, hsurj⟩ := exists_swapFactors_iSup_neighbourCore e hn hnf hparam
  exact unique_of_swapFactors_of_factorNormalAt hset e hn ht hKt
    (fun A hqA hoddA hφ g hAB htA htB hnA hnB => false_of_factorNormal_of_pairExclusion hP hset e
      (by omega) hnq ht hKt A hqA hoddA hφ g hAB htA htB hnA hnB) hq h₁₂ hsup hδ hsurj

end Unique

section SeitzFull

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {m : ℕ}

theorem false_of_seitzSetting_unitary_of_uniqueOfParam (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (m + 1 - 2)) (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m)
    (hnf : (m + 1, f) ≠ (6, 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (huniq : (∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin (m + 1))))) → UnitarySwapRowUnique e t) : False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  by_cases hone : ∃ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin (m + 1))))
  · obtain ⟨a, b, hab, hP⟩ := hone
    exact false_of_graphFieldNeighbourParam_unitaryRootTorus_of_nonempty_holds h hset e hm ht hKt
      hab hP
  · have hrow : ∀ (a b : Fin (m + 1)) (hab : a ≠ b), UnitaryRootTorusSwapRow e t hab :=
      fun a b hab => (nonempty_graphFieldNeighbourParam_or_swapRow_unitaryRootTorus h hset hcat e
        (by omega) hnf htC ht hab).resolve_left fun hP => hone ⟨a, b, hab, hP⟩
    have hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
        Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
          ({a, b}ᶜ : Finset (Fin (m + 1)))) := fun a b hab => by
      obtain ⟨htX, hKc⟩ := hrow a b hab
      exact nonempty_swapNeighbourParam_of_swapRow h hset e (by omega) htC ht hab htX hKc
    exact false_of_swapRow_unitaryRootTorus h hset e (by omega) hnf htC ht hrow (huniq hparam)

theorem false_of_seitzSetting_unitary_of_pairExclusion
    (hP : UnitarySwapPairExclusion h (m + 1)) (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (m + 1 - 2)) (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m)
    (hnf : (m + 1, f) ≠ (6, 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False :=
  false_of_seitzSetting_unitary_of_uniqueOfParam h hset hcat e hm hnf ht hKt fun hparam =>
    unitarySwapRowUnique_of_pairExclusion hP hset e (by omega) hnf ht hKt hparam

theorem false_of_seitzSetting_unitary_of_innerTwoPart
    (hI : UnitaryInnerInvolutionTwoPart h (m + 1)) (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (m + 1 - 2)) (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m)
    (hnf : (m + 1, f) ≠ (6, 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False :=
  false_of_seitzSetting_unitary_of_pairExclusion h
    (unitarySwapPairExclusion_of_innerTwoPart h hI (by omega)) hset hcat e hm hnf ht hKt

end SeitzFull

end CFSG.SeitzReduction.UnitaryPilot
