module

import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.PartTwo.Sec21.PairExistence

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem map_centralizer_mulEquiv (φ : G ≃* G') (S : Set G) :
    (Subgroup.centralizer S).map φ.toMonoidHom = Subgroup.centralizer (φ '' S) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    have := congrArg φ (h s hs)
    simpa using this
  · intro h s hs
    apply φ.injective
    simpa using h (φ s) ⟨s, hs, rfl⟩

theorem map_lThreeV (φ : G ≃* G') (E U : Subgroup G) (c : G) :
    (lThreeV E U c).map φ.toMonoidHom =
      lThreeV (E.map φ.toMonoidHom) (U.map φ.toMonoidHom) (φ c) := by
  rw [lThreeV, lThreeV, Subgroup.map_commutator,
    CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore,
    Subgroup.map_inf_eq _ _ _ φ.injective, map_centralizer_mulEquiv, map_centralizer_mulEquiv,
    Set.image_union, Set.image_singleton]
  rfl

theorem map_mem_lThreeStarPairs [Finite G] [Finite G'] (φ : G ≃* G') {A E U L : Subgroup G}
    {c : G} (h : (c, L) ∈ lThreeStarPairs A E U) :
    (φ c, L.map φ.toMonoidHom) ∈ lThreeStarPairs (A.map φ.toMonoidHom) (E.map φ.toMonoidHom)
      (U.map φ.toMonoidHom) := by
  obtain ⟨hc, hc1, hL, hUN, hVN, hUL, hVL⟩ := h
  have hcE' : φ c ∈ E.map φ.toMonoidHom ⊓ Subgroup.centralizer (U.map φ.toMonoidHom : Set G') := by
    have := Subgroup.mem_map_of_mem φ.toMonoidHom hc
    rwa [Subgroup.map_inf_eq _ _ _ φ.injective, map_centralizer_mulEquiv] at this
  refine ⟨hcE', (map_ne_one_iff φ φ.injective).mpr hc1, map_mem_lZeroStarAt φ hL, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hUN
  · rw [← map_lThreeV, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hVN
  · rw [← Subgroup.map_commutator, hUL]
  · rw [← map_lThreeV, ← Subgroup.map_commutator, hVL]

theorem map_mem_lThreeStar [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G}
    (h : L ∈ lThreeStar A) : L.map φ.toMonoidHom ∈ lThreeStar (A.map φ.toMonoidHom) := by
  obtain ⟨hL, E, hE, U, hU, c, hcL⟩ := h
  exact ⟨map_mem_lZeroStar φ hL, E.map φ.toMonoidHom,
    ⟨map_mem_partTwoE φ hE.1, Subgroup.map_mono hE.2⟩, U.map φ.toMonoidHom,
    map_mem_fourGroups φ hU, φ c, map_mem_lThreeStarPairs φ hcL⟩

theorem layer_map_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (layer X).map e.toMonoidHom = layer Y :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem map_inSubgroup_layer (φ : G ≃* G') (X : Subgroup G) :
    (inSubgroup layer X).map φ.toMonoidHom = inSubgroup layer (X.map φ.toMonoidHom) := by
  rw [inSubgroup, map_map_subtype_mulEquiv, layer_map_mulEquiv', inSubgroup]

theorem oPrimeResidual_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (p : ℕ) (e : X ≃* Y) :
    (CFSG.GH74.GLS.oPrimeResidual p X).map e.toMonoidHom = CFSG.GH74.GLS.oPrimeResidual p Y := by
  unfold CFSG.GH74.GLS.oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    rw [← map_pow, hk, map_one]

theorem map_oPrimeResidualOf (φ : G ≃* G') (p : ℕ) (X : Subgroup G) :
    (CFSG.GH74.GLS.oPrimeResidualOf p X).map φ.toMonoidHom =
      CFSG.GH74.GLS.oPrimeResidualOf p (X.map φ.toMonoidHom) := by
  rw [CFSG.GH74.GLS.oPrimeResidualOf, CFSG.GH74.GLS.oPrimeResidualOf, map_map_subtype_mulEquiv,
    oPrimeResidual_map_mulEquiv]

end Transport

variable {G : Type} [Group G]

@[expose] def wConj (A : Subgroup G) (w : Subgroup.normalizer (A : Set G)) : MulAut A :=
  A.normalizerMonoidHom w

theorem wConj_apply (A : Subgroup G) (w : Subgroup.normalizer (A : Set G)) (a : A) :
    ((wConj A w a : A) : G) = w * a * w⁻¹ := rfl

theorem wConj_mem_wStar (A : Subgroup G) (w : Subgroup.normalizer (A : Set G)) :
    wConj A w ∈ wStar A :=
  ⟨w, rfl⟩

theorem conj_mem_starOf {A X : Subgroup G} (w : Subgroup.normalizer (A : Set G)) {φ : MulAut A}
    (hφ : φ ∈ starOf A X) :
    wConj A w * φ * (wConj A w)⁻¹ ∈ starOf A (X.map (MulAut.conj (w : G)).toMonoidHom) := by
  obtain ⟨x, hx, rfl⟩ := hφ
  rw [SetLike.mem_coe] at hx
  refine ⟨w * x * w⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact ⟨_, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · simp [wConj, map_mul, map_inv]

theorem commOf_conj {P : Type*} [Group P] (ψ φ : MulAut P) :
    commOf (ψ * φ * ψ⁻¹) = (commOf φ).map ψ.toMonoidHom := by
  rw [commOf, commOf, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(ψ⁻¹ a)⁻¹ * φ (ψ⁻¹ a), ⟨ψ⁻¹ a, rfl⟩, ?_⟩
    simp [MulAut.mul_apply]
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨ψ a, ?_⟩
    simp [MulAut.mul_apply]

theorem IsReflectionOn.conj {P : Type*} [Group P] {φ : MulAut P} (h : IsReflectionOn φ)
    (ψ : MulAut P) : IsReflectionOn (ψ * φ * ψ⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [← h.1]
    exact (orderOf_injective (MulAut.conj ψ).toMonoidHom (MulAut.conj ψ).injective φ).trans rfl
  · rw [commOf_conj, Subgroup.card_map_of_injective ψ.injective]
    exact h.2

theorem conj_mem_dStar [Finite G] {A : Subgroup G} (w : Subgroup.normalizer (A : Set G))
    {φ : MulAut A} (hφ : φ ∈ dStar A) : wConj A w * φ * (wConj A w)⁻¹ ∈ dStar A := by
  obtain ⟨hr, X, hX, hφX⟩ := hφ
  refine ⟨hr.conj _, X.map (MulAut.conj (w : G)).toMonoidHom, ?_, conj_mem_starOf w hφX⟩
  have h := map_mem_lThreeStar (MulAut.conj (w : G)) hX
  rwa [map_conj_eq_of_mem_normalizer w.2] at h

theorem fixedSubgroupOf_conj {P : Type*} [Group P] (ψ φ : MulAut P) :
    fixedSubgroupOf (ψ * φ * ψ⁻¹) = (fixedSubgroupOf φ).map ψ.toMonoidHom := by
  ext y
  rw [mem_fixedSubgroupOf, Subgroup.mem_map_equiv, mem_fixedSubgroupOf, MulAut.mul_apply,
    MulAut.mul_apply]
  constructor
  · intro h
    have := congrArg ψ.symm h
    rwa [MulEquiv.symm_apply_apply] at this
  · intro h
    have h' : φ (ψ⁻¹ y) = ψ⁻¹ y := h
    rw [h']
    exact MulEquiv.apply_symm_apply ψ y

theorem fixedInG_conj (A : Subgroup G) (w : Subgroup.normalizer (A : Set G)) (φ : MulAut A) :
    fixedInG A (wConj A w * φ * (wConj A w)⁻¹) =
      (fixedInG A φ).map (MulAut.conj (w : G)).toMonoidHom := by
  rw [fixedInG, fixedInG, fixedSubgroupOf_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem kZero_conj [Finite G] (A : Subgroup G) (w : Subgroup.normalizer (A : Set G))
    (φ : MulAut A) :
    kZero A (wConj A w * φ * (wConj A w)⁻¹) =
      (kZero A φ).map (MulAut.conj (w : G)).toMonoidHom := by
  rw [kZero, kZero, map_oPrimeResidualOf, map_inSubgroup_layer, map_centralizer_mulEquiv,
    fixedInG_conj]
  rfl

@[expose] def KOfWellDefined (A : Subgroup G) : Prop :=
  ∀ φ ∈ dStar A, StatedClassicalModel (kZero A φ) .PSU 3 2 2 →
    ∃! K : Subgroup G, K ≤ kZero A φ ∧ StatedClassicalModel K .PSL 2 2 2 ∧ A ⊓ kZero A φ ≤ K

theorem kOf_prop_conj [Finite G] {A K : Subgroup G} (w : Subgroup.normalizer (A : Set G))
    {φ : MulAut A}
    (hK : K ≤ kZero A φ ∧ StatedClassicalModel K .PSL 2 2 2 ∧ A ⊓ kZero A φ ≤ K) :
    K.map (MulAut.conj (w : G)).toMonoidHom ≤ kZero A (wConj A w * φ * (wConj A w)⁻¹) ∧
      StatedClassicalModel (K.map (MulAut.conj (w : G)).toMonoidHom) .PSL 2 2 2 ∧
      A ⊓ kZero A (wConj A w * φ * (wConj A w)⁻¹) ≤
        K.map (MulAut.conj (w : G)).toMonoidHom := by
  obtain ⟨h1, h2, h3⟩ := hK
  rw [kZero_conj]
  refine ⟨Subgroup.map_mono h1, CFSG.SectionRank.statedClassicalModel_of_mulEquiv
    (K.equivMapOfInjective _ (MulAut.conj (w : G)).injective).symm h2, ?_⟩
  rintro x ⟨hxA, y, hy, rfl⟩
  refine ⟨y, h3 ⟨?_, hy⟩, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ w.2) _).mp hxA
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem kOf_conj_of_unique [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    (w : Subgroup.normalizer (A : Set G)) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    kOf A (wConj A w * φ * (wConj A w)⁻¹) = (kOf A φ).map (MulAut.conj (w : G)).toMonoidHom := by
  have hφ' := conj_mem_dStar w hφ
  have hiff : StatedClassicalModel (kZero A (wConj A w * φ * (wConj A w)⁻¹)) .PSU 3 2 2 ↔
      StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
    rw [kZero_conj]
    exact ⟨CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        ((kZero A φ).equivMapOfInjective _ (MulAut.conj (w : G)).injective),
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        ((kZero A φ).equivMapOfInjective _ (MulAut.conj (w : G)).injective).symm⟩
  by_cases hU : StatedClassicalModel (kZero A φ) .PSU 3 2 2
  · obtain ⟨K, hKp, -⟩ := hK φ hφ hU
    have hspec := kOf_spec hU ⟨K, hKp⟩
    obtain ⟨K', -, huniq'⟩ := hK _ hφ' (hiff.mpr hU)
    have hspec' := kOf_spec (hiff.mpr hU) ⟨_, kOf_prop_conj w hKp⟩
    exact (huniq' _ hspec').trans (huniq' _ (kOf_prop_conj w hspec)).symm
  · rw [kOf_eq_kZero hU, kOf_eq_kZero (fun h => hU (hiff.mp h)), kZero_conj]

theorem normalizer_le_nGroup [Finite G] {A : Subgroup G} (hK : KOfWellDefined A) :
    Subgroup.normalizer (A : Set G) ≤ nGroup A := by
  intro w hw
  set w' : Subgroup.normalizer (A : Set G) := ⟨w, hw⟩
  have hle : (iGroup A).map (MulAut.conj w).toMonoidHom ≤ iGroup A := by
    rw [iGroup, Subgroup.map_iSup]
    refine iSup_le fun φ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hφ => ?_
    rw [← kOf_conj_of_unique hK w' hφ]
    exact kOf_le_iGroup (conj_mem_dStar w' hφ)
  exact mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj w).injective).symm))

end CFSG.RankThree.PartTwo.Sec21
