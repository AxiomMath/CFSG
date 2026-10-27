module

public import CFSG.RankThree.GF2n.Parrott.Section4G0TheoremA
public import CFSG.RankThree.GF2n.Parrott.Section4HPrimeIndex

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem parrottHypA1_of_inf_eq_commutator
    (h : Tim79a.ParrottHypA z) {G₀ : Subgroup G} (hG₀n : G₀.Normal) (hzG₀ : z ∈ G₀)
    (hJ : J z ≤ ⁅H z, H z⁆) (hHG₀ : H z ⊓ G₀ = ⁅H z, H z⁆) :
    Tim79a.ParrottHypA1 (⟨z, hzG₀⟩ : ↥G₀) := by
  classical
  let w : ↥G₀ := ⟨z, hzG₀⟩
  have hJleG₀ : J z ≤ G₀ := hJ.trans (hHG₀ ▸ inf_le_right)
  have hJinf : J z ⊓ G₀ = J z := inf_eq_left.mpr hJleG₀
  have hJmap : (J w).map G₀.subtype = J z := by
    rw [map_J_G₀ hG₀n hzG₀, hJinf]
  have hHmap : (H w).map G₀.subtype = ⁅H z, H z⁆ := by
    rw [map_H_G₀ hzG₀, hHG₀]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply isExtraspecial2_of_map G₀.subtype G₀.subtype_injective
    rw [hJmap]
    exact h.extraspecial
  · have hcard := h.card_J
    rw [← hJmap, Subgroup.card_map_of_injective G₀.subtype_injective] at hcard
    exact hcard
  · apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_commutator, hJmap, h.commutator, MonoidHom.map_zpowers]
    rfl
  · intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxHz : (x : G) ∈ H z := by
      have h1 := Subgroup.mem_map_of_mem G₀.subtype hxH
      rw [map_H_G₀ hzG₀] at h1
      exact h1.1
    have hxCz : (x : G) ∈ Subgroup.centralizer (J z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hJmap] at hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      have hcomm := Subgroup.mem_centralizer_iff.mp hxC y' hy'
      simpa using congrArg Subtype.val hcomm
    have hxJz := h.centralizer_le (Subgroup.mem_inf.mpr ⟨hxHz, hxCz⟩)
    rw [← Subgroup.mem_map_iff_mem G₀.subtype_injective, hJmap]
    exact hxJz
  · let D := quotientDataA h
    have hHw : ∀ x : ↥(H w), ((x : ↥G₀) : G) ∈ H z := fun x => by
      have h1 := Subgroup.mem_map_of_mem G₀.subtype x.2
      rw [map_H_G₀ hzG₀] at h1
      exact h1.1
    let ι' : ↥(H w) →* ↥(H z) :=
      MonoidHom.codRestrict (G₀.subtype.comp (H w).subtype) (H z) hHw
    let φ : ↥(H w) →* ↥QA45.originalSubgroup := (qH D).comp ι'
    have hJw : ∀ y : ↥G₀, y ∈ J w ↔ (y : G) ∈ J z := by
      intro y
      rw [← Subgroup.mem_map_iff_mem G₀.subtype_injective, hJmap]
      rfl
    have hker : φ.ker = (J w).subgroupOf (H w) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hJw]
      change qH D (ι' x) = 1 ↔ ((x : ↥G₀) : G) ∈ J z
      rw [← J_mem_iff D (ι' x), Subgroup.mem_subgroupOf]
      rfl
    have hcomp : (H z).subtype.comp ι' = G₀.subtype.comp (H w).subtype := by
      ext x
      rfl
    have hrange_ι' : ι'.range = _root_.commutator (↥(H z)) := by
      apply Subgroup.map_injective (H z).subtype_injective
      have h1 : (ι'.range).map (H z).subtype = (H w).map G₀.subtype := by
        rw [MonoidHom.range_eq_map, Subgroup.map_map, hcomp, ← Subgroup.map_map,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [h1, hHmap, Subgroup.map_subtype_commutator]
    have hφrange : φ.range = (_root_.commutator (↥(H z))).map (qH D) := by
      rw [show φ = (qH D).comp ι' from rfl, MonoidHom.range_comp, hrange_ι']
    have hcomm_QA45 : (_root_.commutator (↥(H z))).map (qH D) =
        _root_.commutator (↥QA45.originalSubgroup) := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (qH_surjective D), ← _root_.commutator_def]
    have hQcomm : _root_.commutator (↥QA45.originalSubgroup) =
        QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      apply le_antisymm
      · have hNQ : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
          Subgroup.normal_of_index_eq_two index_QP45
        have hcard : Nat.card (↥QA45.originalSubgroup ⧸
            QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) = 2 := by
          rw [← Subgroup.index_eq_card]
          exact index_QP45
        have : IsCyclic (↥QA45.originalSubgroup ⧸
            QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) :=
          isCyclic_of_prime_card (p := 2) hcard
        exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp inferInstance
      · exact QP45_subgroupOf_le_commutator_QA45
    have hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [hφrange, hcomm_QA45, hQcomm]
    refine ⟨{ X := D.X
              instX := D.instX
              lie := D.lie
              iso := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
                ((QuotientGroup.quotientKerEquivRange φ).trans
                  ((MulEquiv.subgroupCongr hrange).trans
                    ((Subgroup.subgroupOfEquivOfLe QP45_le_QA45).trans
                      (Classical.choice (equiv_of_lieModel D.lie)).symm))) }⟩

end CFSG.RankThree.GF2n.Parrott
