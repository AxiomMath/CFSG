module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneFixed
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
public import CFSG.Monster.Existence.Compat.Sp8

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.ComponentClassification.PresentationLocal CFSG.ComponentClassification.StandardRecognition
  CFSG.Monster.Existence.Compat
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem derived_of_mulEquiv_sympFour {F : Type*} [Group F] (e : F ≃* sympFour) :
    CFSG.IsQuasisimple ↥(commutator F) ∧
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ w : F, w ^ p = 1 → w ∈ commutator F := by
  have hmap : (commutator F).map e.toMonoidHom = commutator sympFour := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  refine ⟨?_, fun {p} hp hp2 w hw => ?_⟩
  · let e' : ↥(commutator F) ≃* ↥(commutator sympFour) :=
      ((commutator F).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)
    have hs : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
    have hq : CFSG.IsQuasisimple ↥(commutator sympFour) := by
      refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥(commutator sympFour)) ?_).1
      by_contra hc
      push Not at hc
      exact not_isMulCommutative_commutator_sympFour ⟨⟨hc⟩⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hq
  · have hpodd : Odd p := hp.odd_of_ne_two hp2
    have h1 : (omegaPerm (e w)) ^ p = 1 := by
      rw [← map_pow, ← map_pow, hw, map_one, map_one]
    have h2 : Equiv.Perm.sign (omegaPerm (e w)) = 1 := by
      have h3 : Equiv.Perm.sign (omegaPerm (e w)) ^ p = 1 := by
        rw [← map_pow, h1, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (omegaPerm (e w))) with h | h
      · exact h
      · rw [h, hpodd.neg_one_pow] at h3
        exact absurd h3 (by decide)
    have h4 : e w ∈ commutator sympFour := by
      rw [commutator_sympFour]
      exact Equiv.Perm.mem_alternatingGroup.mpr h2
    have h5 : e w ∈ (commutator F).map e.toMonoidHom := by
      rw [hmap]
      exact h4
    obtain ⟨u, hu, hue⟩ := h5
    have : u = w := e.injective hue
    exact this ▸ hu

theorem derived_alt_index_of_mulEquiv_sympFour {F : Type*} [Group F] (e : F ≃* sympFour) :
    Nonempty (↥(commutator F) ≃* alternatingGroup (Fin 6)) ∧ (commutator F).index = 2 := by
  have hmap : (commutator F).map e.toMonoidHom = commutator sympFour := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  refine ⟨⟨(((commutator F).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans commutatorEquivAlternating⟩, ?_⟩
  rw [← Subgroup.index_map_equiv (commutator F) e, show ((e : F ≃* sympFour) : F →* sympFour) =
    e.toMonoidHom from rfl, hmap, commutator_sympFour,
    Subgroup.index_comap_of_surjective _ omegaPerm_surjective, alternatingGroup.index_eq_two]

theorem nonempty_mulEquiv_sympFour {K : Type} [Field K] [Finite K] (hK2 : Nat.card K = 2)
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {B : LinearMap.BilinForm K W} (hB : B.IsAlt) (hn : B.Nondegenerate)
    (hd : finrank K W = 4) : Nonempty (sesqUnitaryGroup B ≃* sympFour) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hs2 : s = 2 := by omega
  subst hs2
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  exact ⟨e.trans ((statedSpEquiv 2 K).trans ((sympMapEquiv
    (FiniteField.ringEquivOfCardEq hcard)).trans
      (MulEquiv.ofBijective symplecticToSympFour symplecticToSympFour_bijective)))⟩

section Fixed

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem spFixed_four_two {ℓ f p : ℕ} (hK2 : Nat.card K = 2) {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hd : spFixedDim x = 4) :
    CFSG.IsQuasisimple ↥⁅spFixedFactor x, spFixedFactor x⁆ ∧
      ∀ {q : ℕ}, q.Prime → q ≠ 2 → ∀ w ∈ spFixedFactor x, w ^ q = 1 →
        w ∈ ⁅spFixedFactor x, spFixedFactor x⁆ := by
  have hmem := X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  obtain ⟨E⟩ := nonempty_mulEquiv_sympFour hK2 hB blocks.fixed_nondegenerate hd
  obtain ⟨hq, hodd⟩ := derived_of_mulEquiv_sympFour (φ.trans E)
  refine ⟨?_, fun {q} hq' hq2 w hw hwq => ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((commutator ↥(spFixedFactor x)).equivMapOfInjective (spFixedFactor x).subtype
        (Subgroup.subtype_injective _)).trans
          (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))) hq
  · have := hodd hq' hq2 ⟨w, hw⟩ (Subtype.ext (by simpa using hwq))
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨⟨w, hw⟩, this, rfl⟩

theorem spFixed_four_two_alt {ℓ f p : ℕ} (hK2 : Nat.card K = 2) {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hd : spFixedDim x = 4) :
    Nonempty (↥⁅spFixedFactor x, spFixedFactor x⁆ ≃* alternatingGroup (Fin 6)) ∧
      ⁅spFixedFactor x, spFixedFactor x⁆.relIndex (spFixedFactor x) = 2 := by
  have hmem := X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  obtain ⟨E⟩ := nonempty_mulEquiv_sympFour hK2 hB blocks.fixed_nondegenerate hd
  obtain ⟨⟨e6⟩, hidx⟩ := derived_alt_index_of_mulEquiv_sympFour (φ.trans E)
  refine ⟨⟨(((commutator ↥(spFixedFactor x)).equivMapOfInjective (spFixedFactor x).subtype
    (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))).symm.trans e6⟩, ?_⟩
  rw [Subgroup.relIndex, ← Subgroup.map_subtype_commutator]
  have h : (Subgroup.map (spFixedFactor x).subtype (commutator ↥(spFixedFactor x))).subgroupOf
      (spFixedFactor x) = commutator ↥(spFixedFactor x) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [h]
  exact hidx

end Fixed

end CFSG.RankThree.PartOne
