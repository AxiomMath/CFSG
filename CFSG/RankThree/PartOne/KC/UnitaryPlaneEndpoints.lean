module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.KC.UnitaryEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

theorem not_map_le_conjRange_of_not_le {G : Type*} [Group G] {L : Subgroup G} {T' : Type*}
    [Group T'] (e : (L ⧸ center L) ≃* T') {A : Subgroup (MulAut (L ⧸ center L))}
    (hA : ¬ A ≤ (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range) :
    ¬ A.map (MulAut.congr e).toMonoidHom ≤ (MulAut.conj : T' →* MulAut T').range := by
  intro hle
  apply hA
  have hmapInn : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.map
      (MulAut.congr e).toMonoidHom = (MulAut.conj : T' →* MulAut T').range :=
    map_conj_range_mulAutCongr e
  rw [← hmapInn] at hle
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).mp hle

theorem unitary_nonsplit_inner_actual_component_centralization_of
    (h : UnitaryNonsplitInnerPlaneProductsTrivial) :
    UnitaryNonsplitInnerActualComponentCentralization := by
  intro G _ _ p ℓ f n hp hp3 hℓ hℓp hf hn3 hpq E hE hEcard t htE ht1 L hL hmod hEL hSL hCEL
    hinner
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, hne, K, _, hU, ⟨e⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU hmod
  have hplane : PlaneLocalCoreInner p (primeFormP hU (idGram K n)) (fun _ => True) :=
    fun B hB A hAInn hA hAcard _ t htA ht1 =>
      (h ℓ f n p K hU hp hp3 hℓp.symm hpq hn3 hne B hB A hAInn hA hAcard).2 t htA ht1
  have hplaneL := PlaneLocalCoreInner.of_mulEquiv hp e hplane
  obtain ⟨h1, h2, h3⟩ := component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE ht1
    hL hEL hSL hplaneL (Or.inr ⟨trivial, hinner⟩)
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
  exact ⟨hset, h3.trans (Subgroup.centralizer_le_normalizer _), h1, h2, h3⟩

theorem nonsplit_unitary_noninner_actual_component_odd_action_of
    (h : NonsplitUnitaryNoninnerPlaneLocalCoreOdd) :
    NonsplitUnitaryNoninnerActualComponentOddAction := by
  intro G _ _ p ℓ f n hp hp3 hℓ hℓp hf hn3 hpq E hE hEcard t htE ht1 L hL hmod hEL hSL hcase
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, hne, K, _, hU, ⟨e⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU hmod
  have hplane : PlaneLocalCoreOddIf p (primeFormP hU (idGram K n)) (fun A => ¬ A ≤ innU hU n) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h ℓ f n p K hU hp hp3 hℓp.symm hpq hn3 hne B hB A hAB hA hAcard hPA).2.2.2.2.2.2 t htA
        ht1).2.1
  have hplaneL := PlaneLocalCoreOddIf.of_mulEquiv hp e hplane
  have hP : E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ (actualPlane L E).map (MulAut.congr e).toMonoidHom ≤ innU hU n :=
    hcase.imp_right (not_map_le_conjRange_of_not_le e)
  obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp hp2
    hE hEcard htE ht1 hL hEL hSL hplaneL hP
  exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, hnonfaith⟩

theorem higher_unitary_noninner_plane_actual_component_odd_action_of
    (h : HigherUnitaryNoninnerPlaneLocalCoreOdd) :
    ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 ≤ n → n < p → ℓ ≠ p →
      ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f →
      E ≤ Subgroup.normalizer (L : Set G) →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
        Subgroup.normalizer (L : Set G) →
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
        ¬ actualPlane L E ≤
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
      ComponentLocalCoreOddResidual p E t L ∧
        (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤
          Subgroup.centralizer (L : Set G)) := by
  intro G _ _ p ℓ f n hp hn3 hnp hℓp E hE hEcard t htE ht1 L hL hmod hEL hSL hcase
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, hne, K, _, hU, ⟨e⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU hmod
  have hplane : PlaneLocalCoreOddIf p (primeFormP hU (idGram K n)) (fun A => ¬ A ≤ innU hU n) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h ℓ f n p K hU hp hℓp.symm hn3 hnp hne B hB A hAB hA hAcard hPA).2.2.2.2.2.2 t htA ht1).2
  have hplaneL := PlaneLocalCoreOddIf.of_mulEquiv hp e hplane
  have hP : E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ (actualPlane L E).map (MulAut.congr e).toMonoidHom ≤ innU hU n :=
    hcase.imp_right (not_map_le_conjRange_of_not_le e)
  obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp hp2
    hE hEcard htE ht1 hL hEL hSL hplaneL hP
  exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, hnonfaith⟩

theorem higher_unitary_all_plane_actual_component_odd_action_of
    (h6 : HigherUnitaryInnerPlaneProductsTrivial) (h7 : HigherUnitaryNoninnerPlaneLocalCoreOdd) :
    HigherUnitaryAllPlaneActualComponentOddAction := by
  classical
  intro G _ _ p ℓ f n hp hn3 hnp hℓp E hE hEcard t htE ht1 L hL hmod hEL hSL
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, hne, K, _, hU, ⟨e⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU hmod
  have hodd : PlaneLocalCoreOddIf p (primeFormP hU (idGram K n)) (fun A => ¬ A ≤ innU hU n) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h7 ℓ f n p K hU hp hℓp.symm hn3 hnp hne B hB A hAB hA hAcard hPA).2.2.2.2.2.2 t htA ht1).2
  have hoddL := PlaneLocalCoreOddIf.of_mulEquiv hp e hodd
  have hinner : PlaneLocalCoreInner p (primeFormP hU (idGram K n)) (fun _ => True) :=
    fun B hB A hAInn hA hAcard _ t htA ht1 =>
      (h6 ℓ f n p K hU hp hℓp.symm hn3 hnp hne B hB A hAInn hA hAcard).2 t htA ht1
  have hinnerL := PlaneLocalCoreInner.of_mulEquiv hp e hinner
  by_cases hC : E ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · by_cases hin : actualPlane L E ≤
        (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range
    ·
      have hWC := plane_reduction_inner hp hp2 hE hEcard htE ht1 hL hEL hSL hC hinnerL trivial hin
      have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
      have hWN : (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)),
          E⁆ ⊔ thetaT p E) ≤ Subgroup.normalizer (L : Set G) :=
        hWC.trans (Subgroup.centralizer_le_normalizer _)
      have hrel : ¬ 2 ∣ (Subgroup.centralizer (L : Set G)).relIndex
          (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ ⊔
            thetaT p E) := by
        rw [Subgroup.relIndex_eq_one.mpr hWC]
        omega
      exact ⟨⟨hset, hWN, hrel⟩, fun _ => hWC⟩
    ·
      obtain ⟨hset, hWN, hrel, -, -⟩ := component_local_core_odd_action_of_plane_if hp hp2 hE
        hEcard htE ht1 hL hEL hSL hoddL
        (Or.inr (not_map_le_conjRange_of_not_le e hin))
      exact ⟨⟨hset, hWN, hrel⟩, fun h' =>
        h'.elim (fun h1 => absurd hC h1) (fun h1 => absurd h1 hin)⟩
  ·
    obtain ⟨hset, hWN, hrel, -, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp
      hp2 hE hEcard htE ht1 hL hEL hSL hoddL (Or.inl hC)
    exact ⟨⟨hset, hWN, hrel⟩, fun _ => hnonfaith hC⟩

end CFSG.RankThree.PartOne
