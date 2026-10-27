module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.MinusFacts
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Aut
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Frame

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

theorem minusL_eq_commutator : minusL = commutator minusPerm := by
  haveI : IsSimpleGroup minusL := isSimpleGroup_minusL
  have hnc : ¬ IsMulCommutative minusL := by
    intro hcomm
    haveI : IsMulCommutative minusL := hcomm
    have hp : Nat.Prime (Nat.card minusL) :=
      (Group.is_simple_iff_prime_card (α := minusL)).mp inferInstance
    rw [card_minusL] at hp
    norm_num at hp
  haveI : Group.IsPerfect minusL :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  refine le_antisymm ?_ ?_
  · calc minusL = ⁅minusL, minusL⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup minusPerm), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator minusPerm := by rw [commutator_def]
  · have hidx : minusL.index = 2 := index_minusL
    haveI : minusL.Normal := minusL_normal
    rw [commutator_def]
    refine Subgroup.commutator_le.2 ?_
    intro g₁ _ g₂ _
    have hmem_norm : g₁ ∈ Subgroup.normalizer (minusL : Set minusPerm) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g₁
    have hconj : g₁ * g₂ * g₁⁻¹ ∈ minusL ↔ g₂ ∈ minusL :=
      (Subgroup.mem_normalizer_iff.1 hmem_norm g₂).symm
    have hinv : g₂⁻¹ ∈ minusL ↔ g₂ ∈ minusL := minusL.inv_mem_iff
    have hmem := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := g₁ * g₂ * g₁⁻¹) (b := g₂⁻¹)).2 (hconj.trans hinv.symm)
    simpa only [commutatorElement_def] using hmem

theorem ncard_minusClass : minusClass.ncard = 65 := by
  have hrange : minusClass = Set.range (fun i : Fin 65 =>
      (⟨minusRefl i, minusRefl_mem i⟩ : minusPerm)) := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hinj : Function.Injective (fun i : Fin 65 =>
      (⟨minusRefl i, minusRefl_mem i⟩ : minusPerm)) := by
    intro i j h
    exact minusRefl_injective (Subtype.ext_iff.mp h)
  rw [hrange, Set.ncard_range_of_injective hinj]
  simp

section MinusModel

theorem o4MinusFacts_minusPerm : O4MinusFacts minusPerm minusClass :=
  ⟨card_minusPerm, ncard_minusClass, minusClass_noncomm, minusClass_primitive,
    minusL_eq_commutator ▸ index_minusL, minusL_eq_commutator ▸ nonempty_minusL_mulEquiv_psl225,
    minusClass_aut, minusPerm_frame, minusClass_perp⟩

theorem o4MinusFacts_of_isFiveReflectionModel {X : Type} [Group X] {Θ : Set X} {π : Bool}
    (h : IsFiveReflectionModel 3 false π Θ) : O4MinusFacts X Θ := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨e, he⟩ := exists_minusRealize π
  let ψ : X ≃* minusPerm := φ.trans e
  have hφim : φ '' Θ = fiveReflectionImage 3 false π := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).mp hg
    · rintro ⟨k, hk, rfl⟩
      refine ⟨φ.symm (QuotientGroup.mk k), (hφ _).mpr ⟨k, hk, ?_⟩, ?_⟩
      · simp
      · simp
  have hψ : ψ '' Θ = minusClass := by
    change (e ∘ φ) '' Θ = minusClass
    rw [Set.image_comp, hφim, he]
  have he' : ψ.symm '' minusClass = Θ := by
    rw [← hψ, Set.image_image]
    simp
  exact O4MinusFacts.of_mulEquiv ψ.symm he' o4MinusFacts_minusPerm

end MinusModel

end CFSG.OddTranspositions.PartThree
