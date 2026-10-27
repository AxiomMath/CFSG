module

public import CFSG.RankThree.PartOne.KC.LinearPlaneStatements
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.LinearSplitInner
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.RankThree.GroupTheory
open scoped Pointwise

theorem linear_nonsplit_inner_actual_component_centralization_of
    (h : LinearNonsplitInnerPlaneProductsTrivial) :
    LinearNonsplitInnerActualComponentCentralization := by
  intro G _ _ p ℓ f n hp hp3 hℓ hℓp hf hn3 hpq E hE hEcard t htE ht1 L hL hmod hEL hSL hCEL
    hinner
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ := exists_projectiveSL_of_statedClassicalModel_PSL hmod
  have hplane : PlaneLocalCoreInner p (projectiveSL n K) (fun _ => True) :=
    fun B hB A hAInn hA hAcard _ t htA ht1 =>
      (h p ℓ f n K hp hp3 hℓ hℓp hf hn3 hK hpq B hB A hAInn hA hAcard).2.2 t htA ht1
  have hplaneL := PlaneLocalCoreInner.of_mulEquiv hp e hplane
  obtain ⟨h1, h2, h3⟩ := component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE ht1
    hL hEL hSL hplaneL (Or.inr ⟨trivial, hinner⟩)
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
  exact ⟨hset, h3.trans (Subgroup.centralizer_le_normalizer _), h1, h2, h3⟩

theorem not_map_le_innSL_of_not_le_inner {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}
    {K : Type} [Field K] (e : (L ⧸ center L) ≃* projectiveSL n K)
    {A : Subgroup (MulAut (L ⧸ center L))}
    (hA : ¬ A ≤ (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range) :
    ¬ A.map (MulAut.congr e).toMonoidHom ≤ innSL n K := by
  intro hle
  apply hA
  have hmapInn : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.map
      (MulAut.congr e).toMonoidHom = innSL n K := map_conj_range_mulAutCongr e
  rw [← hmapInn] at hle
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).mp hle

theorem nonsplit_linear_noninner_actual_component_odd_action_of
    (h : NonsplitLinearNoninnerPlaneLocalCoreOdd) :
    NonsplitLinearNoninnerActualComponentOddAction := by
  intro G _ _ p ℓ f n hp hp3 hℓ hℓp hf hn3 hpq E hE hEcard t htE ht1 L hL hmod hEL hSL hcase
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ := exists_projectiveSL_of_statedClassicalModel_PSL hmod
  have hplane : PlaneLocalCoreOddIf p (projectiveSL n K) (fun A => ¬ A ≤ innSL n K) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h p ℓ f n K hp hp3 hℓ hℓp hf hn3 hK hpq B hB A hAB hA hAcard hPA).2.2.2.2.2.2 t htA
        ht1).2.1
  have hplaneL := PlaneLocalCoreOddIf.of_mulEquiv hp e hplane
  have hP : E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ (actualPlane L E).map (MulAut.congr e).toMonoidHom ≤ innSL n K :=
    hcase.imp_right (not_map_le_innSL_of_not_le_inner e)
  obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp hp2
    hE hEcard htE ht1 hL hEL hSL hplaneL hP
  exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, hnonfaith⟩

theorem linear_below_prime_noninner_or_split_normalized_component_odd_action_of
    (h : LinearBelowPrimeNoninnerPlaneLocalCoreOdd) :
    LinearBelowPrimeNoninnerOrSplitNormalizedComponentOddAction := by
  classical
  intro H _ _ p ℓ f n hp hp3 hℓ hℓp hf hn3 hnp E hE hEcard t htE ht1 L hL hmod hEL hSL hcase
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ := exists_projectiveSL_of_statedClassicalModel_PSL hmod
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := Fintype.ofFinite K
  have : CharP K ℓ :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hodd : PlaneLocalCoreOddIf p (projectiveSL n K) (fun A => ¬ A ≤ innSL n K) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h p ℓ f n K hp hp3 hℓ hℓp hf hn3 hnp hK B hB A hAB hA hAcard hPA).2.2.2.2 t htA ht1).2.1
  have hoddL := PlaneLocalCoreOddIf.of_mulEquiv hp e hodd
  have hsplitInner : PlaneLocalCoreInner p (projectiveSL n K) (fun _ => p ∣ ℓ ^ f - 1) :=
    fun B hB A hAInn hA hAcard hsplit t htA ht1 => by
      have := hA
      exact (linear_split_inner_plane_local_core_products_trivial hp hp3 hℓ hℓp hf hn3 hnp
        (k := K) hK (by rw [hK]; exact hsplit) B hB A hAInn hAcard htA ht1).2.2
  have hsplitInnerL := PlaneLocalCoreInner.of_mulEquiv hp e hsplitInner
  by_cases hC : E ⊓ Subgroup.centralizer (L : Set H) = ⊥
  · by_cases hin : actualPlane L E ≤
        (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range
    ·
      have hsplit : p ∣ ℓ ^ f - 1 := by
        rcases hcase with h1 | h1 | h1
        · exact absurd hC h1
        · exact absurd hin h1
        · exact h1
      have hWC := plane_reduction_inner hp hp2 hE hEcard htE ht1 hL hEL hSL hC hsplitInnerL hsplit
        hin
      have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
      have hWN : (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)),
          E⁆ ⊔ thetaT p E) ≤ Subgroup.normalizer (L : Set H) :=
        hWC.trans (Subgroup.centralizer_le_normalizer _)
      have hrel : ¬ 2 ∣ (Subgroup.centralizer (L : Set H)).relIndex
          (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)), E⁆ ⊔
            thetaT p E) := by
        rw [Subgroup.relIndex_eq_one.mpr hWC]
        omega
      exact ⟨⟨⟨hset, hWN, hrel⟩, twoPrimeResidual_le_centralizer_of_odd_relIndex hWN hrel⟩,
        fun _ => hWC⟩
    ·
      obtain ⟨hset, hWN, hrel, hres, -⟩ := component_local_core_odd_action_of_plane_if hp hp2 hE
        hEcard htE ht1 hL hEL hSL hoddL
        (Or.inr (not_map_le_innSL_of_not_le_inner e hin))
      exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, fun h' =>
        h'.elim (fun h1 => absurd hC h1) (fun h1 => absurd h1 hin)⟩
  ·
    obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp
      hp2 hE hEcard htE ht1 hL hEL hSL hoddL (Or.inl hC)
    exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, fun _ => hnonfaith hC⟩

end CFSG.RankThree.PartOne
