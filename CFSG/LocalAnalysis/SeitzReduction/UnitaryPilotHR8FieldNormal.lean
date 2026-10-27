module

import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open Matrix (ProjectiveSpecialLinearGroup)

theorem exists_graphField_normal_form_of_isComponent {m : ℕ} (hm : 4 ≤ m)
    (hdet : SUmEvenTypeDetAt m) {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : LieModel S .PSL m 2 (2 * f)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * f) ∧
      ∃ (eS : S ≃* LinearFlag.projectiveSL m K) (A : GL (Fin m) K) (φ : K ≃+* K), φ ≠ 1 ∧
        MulAut.congr eS σ =
          LinearFlag.conjAut m K A * LinearFlag.fieldAut m K φ * LinearFlag.dualAut m K := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL m 2 (2 * f) :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hS).1
  have hf : 1 ≤ 2 * f := hadm.2.1
  have hDp : IsPComponent 2 D := isPComponent_two_of_isComponent hD
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ :=
    ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hS
  have hβ : orderOf (MulAut.congr eJ σ) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective σ).trans hσ
  have hβ2 : MulAut.congr eJ σ ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hβo : MulAut.congr eJ σ ∉
      ComponentClassification.OuterAutomorphisms.inner
        (ProjectiveSpecialLinearGroup (Fin m) K) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have ψ : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin m) K), MulAut.congr eJ σ = γ →
      fixedSubgroup σ ≃* fixedSubgroup γ := fun γ hγ =>
    (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv eJ σ).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := K) (n := m) (by omega)
  obtain ⟨A, φ, ε, hε, hAφε⟩ :=
    hgen (MulAut.congr (ComponentClassification.CatalogueBLinearHigherB.nativeEquiv m K).symm
      (MulAut.congr eJ σ))
  have hβ' : MulAut.congr eJ σ =
      MulAut.congr (ComponentClassification.CatalogueBLinearHigherB.nativeEquiv m K)
        (LinearFlag.conjAut m K A * LinearFlag.fieldAut m K φ * LinearFlag.dualAut m K ^ ε) := by
    rw [← hAφε]
    ext x
    simp
  interval_cases ε
  ·
    rw [pow_zero, mul_one, ComponentClassification.CatalogueBLinearHigherB.congr_semilinear]
      at hβ'
    by_cases hφ : φ = 1
    · subst hφ
      rw [ComponentClassification.CatalogueBLinearSemilinear.semilinearAction_one_field] at hβ'
      exact absurd (ComponentClassification.CatLeafProof.innerDiagonalAction_mem_inner_of_sq hf hK
        A (hβ' ▸ hβ2)) (hβ' ▸ hβo)
    · exfalso
      set χ := ψ _ hβ'
      obtain ⟨hadm', hmP, -⟩ := LinearPilot.psl_field_pComponents (by omega) hf hK A φ hφ
        (hβ' ▸ hβ2) (D.map χ.toMonoidHom) (isPComponent_map_of_isPComponent 2 χ hDp)
      have hmD : LieModel D .PSL m 2 (2 * f / 2) :=
        LieType.CurtisTits.lieModel_of_mulEquiv
          (D.equivMapOfInjective χ.toMonoidHom χ.injective).symm hmP
      obtain ⟨htt, -, -⟩ := sumTypeDet_of_simple hdet hD.1
        (LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD
      exact absurd htt (by decide)
  · rw [pow_one] at hβ' hAφε
    by_cases hφ : φ = 1
    ·
      exfalso
      subst hφ
      rw [map_one, mul_one, ComponentClassification.CatalogueBLinearHigherB.congr_pureGraph]
        at hβ'
      set χ := ψ _ hβ'
      rcases F4Pilot.psl_graph_cases hf hK (by omega) A (hβ' ▸ hβ) with ⟨r, hr1, -, ⟨Φ⟩⟩ | hch
      · exact no_sum_component_statedSp hdet hm hK hr1 (χ.trans Φ) hD hDm
      · exact ComponentClassification.CatLeafProof.not_isPComponent_of_isCharacteristicP hch
          (D.map χ.toMonoidHom) (isPComponent_map_of_isPComponent 2 χ hDp)
    ·
      refine ⟨K, inferInstance, inferInstance, hK,
        eJ.trans (ComponentClassification.CatalogueBLinearHigherB.nativeEquiv m K).symm, A, φ, hφ,
        ?_⟩
      rw [← hAφε]
      ext x
      simp

theorem exists_graphField_conj_of_isComponent {m : ℕ} (hm : 4 ≤ m)
    (hdet : SUmEvenTypeDetAt m) {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : LieModel S .PSL m 2 (2 * f)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * f) ∧
      ∃ (eS : S ≃* LinearFlag.projectiveSL m K) (φ : K ≃+* K), (∀ x, φ x = x ^ 2 ^ f) ∧
        MulAut.congr eS σ = LinearFlag.fieldAut m K φ * LinearFlag.dualAut m K := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL m 2 (2 * f) :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hS).1
  have hf : 1 ≤ 2 * f := hadm.2.1
  obtain ⟨K, _, _, hK, eS, A, φ, hφ, hσ'⟩ :=
    exists_graphField_normal_form_of_isComponent hm hdet hS hσ hout hD hDm
  have hα : (LinearFlag.conjAut m K A * LinearFlag.fieldAut m K φ *
      LinearFlag.dualAut m K) ^ 2 = 1 := by
    rw [← hσ', ← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  obtain ⟨-, hφx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK (by omega) A φ hφ hα
  refine ⟨K, inferInstance, inferInstance, hK,
    MulEquiv.trans eS (LinearFlag.conjAut m K H)⁻¹, φ, fun x => by
      rw [hφx, show 2 * f / 2 = f by omega], ?_⟩
  have hc : MulAut.congr (MulEquiv.trans eS (LinearFlag.conjAut m K H)⁻¹) σ =
      (LinearFlag.conjAut m K H)⁻¹ * MulAut.congr eS σ * (LinearFlag.conjAut m K H) := by
    ext x
    rfl
  rw [hc, hσ', hH]
  group

theorem SUmNeighbourAlternative.graphField {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ} (hm : 4 ≤ m)
    (hmf : (m, f) ≠ (4, 1)) (hdet : SUmEvenTypeDetAt m)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) {Kc : Subgroup Y} (hKc : IsComponent Kc)
    (h : SUmNeighbourAlternative s D Kc m f) (hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc) :
    ∃ hsN : s ∈ normalizer (Kc : Set Y), ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ (2 * f) ∧
      ∃ (eK : Kc ≃* LinearFlag.projectiveSL m K) (φ : K ≃+* K), (∀ x, φ x = x ^ 2 ^ f) ∧
        MulAut.congr eK (Kc.normalizerMonoidHom ⟨s, hsN⟩) =
          LinearFlag.fieldAut m K φ * LinearFlag.dualAut m K := by
  obtain ⟨-, ⟨-, hDK, -, ⟨hsN, hout⟩, -, hmodel⟩ | ⟨hKt', -⟩⟩ := h.exact hO hKc hmf
  · have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
    have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
      (isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    obtain ⟨hD'c, hD'm, -, -⟩ :=
      isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK.le hDs hDcomp hDm
    have hτ2 : orderOf (Kc.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2) fun h1 => ?_
      apply hout
      rw [h1]
      exact one_mem _
    exact ⟨hsN, exists_graphField_conj_of_isComponent hm hdet hmodel hτ2 hout hD'c hD'm⟩
  · exact absurd hKt hKt'

section Seitz


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ}

open CFSG.ClassicalGroups.UnitaryFlag in
theorem graphField_neighbour_unitaryRootTorus (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (n - 2)) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype)
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (hKc : IsComponent Kc)
    (hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom = Kc) :
    ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
        normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))),
      ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ (2 * f) ∧
        ∃ (eK : Kc ≃* LinearFlag.projectiveSL (n - 2) K') (φ : K' ≃+* K'),
          (∀ x, φ x = x ^ 2 ^ f) ∧
          MulAut.congr eK (Kc.normalizerMonoidHom ⟨_, hsN⟩) =
            LinearFlag.fieldAut (n - 2) K' φ * LinearFlag.dualAut (n - 2) K' := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := card_compl_pair hab
  have hmf : (n - 2, f) ≠ (4, 1) := by
    intro h'
    apply hnf
    rw [Prod.mk.injEq] at h' ⊢
    omega
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC ht hab hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, -, -, -, -⟩ :=
    neighbour_data_unitaryRootTorus h e hn hab htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSU h e (by omega) (by omega)
  have hDm : LieModel (D ⧸ center D) .PSU (n - 2) 2 f :=
    hDe ▸ lieModel_quotient_center_map_blockSU_compl_pair h e hn hab
  have hDm' := lieModel_quotient_center_map_oddCore_of_isQuasisimple (hDC.trans inf_le_left) hDq
    hDm (ne_bot_of_isQuasisimple hcomp.2.2)
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact ((neighbour_overgroup_unitaryRootTorus h hset hcat e hn hnf htC ht hab hX htX hDe).2 Kc
    hKc hDK).graphField (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _)
    (orderOf_mk_oddCore ht') hcomp (by omega) hmf (sumEvenTypeDetAt (by omega)) hDm' hKc hKt

end Seitz

end CFSG.SeitzReduction.UnitaryPilot
