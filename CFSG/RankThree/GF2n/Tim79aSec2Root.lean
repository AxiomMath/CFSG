module

public import CFSG.RankThree.GF2n.Tim79aSec2O2
public import CFSG.RankThree.GF2n.Tim77Prop25
public import CFSG.Timmesfeld.RootInvolutionConj

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem dOf_isRootInvolutionSet : CFSG.Timmesfeld.IsRootInvolutionSet (dOf V H) := by
  rw [dOf_eq_classDIn]
  exact Tim77.tim77_2_5_rel hc.elemAb hc.ti (H_le_normalizer_eOf H) (isMulCommutative_eOf H)
    (by rw [inf_comm]; exact hc.eOf_inf_V_ne_bot)

theorem dbarOf_isRootInvolutionSet : CFSG.Timmesfeld.IsRootInvolutionSet (dbarOf V H) := by
  have h := CFSG.Timmesfeld.isRootInvolutionSet_image_ne_one (piBar V H)
    (CFSG.Timmesfeld.isRootInvolutionSet_subtype (S := H) hc.dOf_isRootInvolutionSet)
  have e : dbarOf V H =
      piBar V H '' {x | x ∈ {x : ↥H | (x : G) ∈ dOf V H} ∧ piBar V H x ≠ 1} := by
    unfold dbarOf
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, ne_eq, piBar_eq_one_iff]
  rw [e]
  exact h

theorem dbarOf_subset_barOf_xOf : dbarOf V H ⊆ (barOf V H (xOf V H) : Set (Hbar V H)) := by
  intro y hy
  obtain ⟨x, ⟨hx1, U, hU, hxU⟩, -, rfl⟩ := mem_dbarOf_iff.mp hy
  exact mem_barOf_iff.mpr ⟨x, le_xOf hU hxU, rfl⟩

theorem closure_dbarOf : Subgroup.closure (dbarOf V H) = barOf V H (xOf V H) := by
  refine le_antisymm ((Subgroup.closure_le _).2 hc.dbarOf_subset_barOf_xOf) fun y hy => ?_
  obtain ⟨x, hxX, rfl⟩ := mem_barOf_iff.mp hy
  let Z : Subgroup G := ((Subgroup.closure (dbarOf V H)).comap (piBar V H)).map H.subtype
  have hXZ : xOf V H ≤ Z := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    intro u hu
    have huH : u ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hh hu
    refine ⟨⟨u, huH⟩, ?_, rfl⟩
    show piBar V H ⟨u, huH⟩ ∈ Subgroup.closure (dbarOf V H)
    by_cases huW : u ∈ wOf V H
    · rw [(piBar_eq_one_iff _).2 huW]; exact Subgroup.one_mem _
    · by_cases hu1 : u = 1
      · subst hu1
        have : (⟨1, huH⟩ : ↥H) = 1 := rfl
        rw [this, map_one]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (mem_dbarOf_iff.mpr ⟨⟨u, huH⟩,
          ⟨hu1, conjSubgroup h V, ⟨h, hh, rfl⟩, hu⟩, huW, rfl⟩)
  obtain ⟨x', hx', hxx⟩ := hXZ hxX
  have : x' = x := Subtype.ext hxx
  exact this ▸ hx'

theorem conj_mem_dbarOf {y x : Hbar V H} (hx : x ∈ dbarOf V H) : y * x * y⁻¹ ∈ dbarOf V H := by
  obtain ⟨d, ⟨hd1, U, hU, hdU⟩, hdW, rfl⟩ := mem_dbarOf_iff.mp hx
  obtain ⟨h, rfl⟩ := piBar_surjective V H y
  have hconj : (h * d * h⁻¹ : ↥H) ∈ ({x : ↥H | (x : G) ∈ dOf V H} : Set ↥H) := by
    refine ⟨?_, conjSubgroup (h : G) U, conjSubgroup_mem_omegaOf_of_mem hU h.2, ?_⟩
    · intro h1
      apply hd1
      have : ((h * d * h⁻¹ : ↥H) : G) = (h : G) * d * (h : G)⁻¹ := by simp
      rw [this] at h1
      calc (d : G) = (h : G)⁻¹ * ((h : G) * d * (h : G)⁻¹) * (h : G) := by group
        _ = 1 := by rw [h1]; group
    · rw [mem_conjSubgroup]
      have e : (h : G)⁻¹ * ((h * d * h⁻¹ : ↥H) : G) * (h : G) = d := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e]
      exact hdU
  refine mem_dbarOf_iff.mpr ⟨h * d * h⁻¹, hconj, ?_, by simp [map_mul, map_inv]⟩
  intro hW
  apply hdW
  have e1 : ((h * d * h⁻¹ : ↥H) : G) = (h : G) * d * (h : G)⁻¹ := by simp
  rw [e1] at hW
  have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (H.inv_mem h.2)) _).mp hW
  have e2 : (h : G)⁻¹ * ((h : G) * d * (h : G)⁻¹) * ((h : G)⁻¹)⁻¹ = d := by group
  rwa [e2] at this

theorem barOf_V_subset_dbarOf {x : Hbar V H} (hx : x ∈ barOf V H V) (hx1 : x ≠ 1) :
    x ∈ dbarOf V H := by
  obtain ⟨v, hv, rfl⟩ := mem_barOf_iff.mp hx
  have hvW : (v : G) ∉ wOf V H := fun h => hx1 ((piBar_eq_one_iff v).2 h)
  have hv1 : (v : G) ≠ 1 := fun h => hvW (h ▸ (wOf V H).one_mem)
  exact mem_dbarOf_iff.mpr ⟨v, ⟨hv1, V, ⟨1, H.one_mem, (conjSubgroup_one V).symm⟩, hv⟩, hvW, rfl⟩

end MinCex

end CFSG.RankThree.GF2n.Tim79a
