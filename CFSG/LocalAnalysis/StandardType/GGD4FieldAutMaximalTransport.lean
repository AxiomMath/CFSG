module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.StandardType

open CFSG.Open (IsElemAbelian)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem ggD4FieldAutMaximal_transport {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : ∀ E : Subgroup (MulAut Y), IsElemAbelian 3 E → Nat.card E = 9 → E ⊓ inner Y = ⊥ →
      ∃ e ∈ E, e ≠ 1 ∧ IsCoatom (fixedSubgroup e) ∧ 3 ∣ (fixedSubgroup e).index) :
    ∀ E : Subgroup (MulAut X), IsElemAbelian 3 E → Nat.card E = 9 → E ⊓ inner X = ⊥ →
      ∃ e ∈ E, e ≠ 1 ∧ IsCoatom (fixedSubgroup e) ∧ 3 ∣ (fixedSubgroup e).index := by
  intro E hE hEcard hEinn
  set ψ : MulAut X ≃* MulAut Y := MulAut.congr φ with hψ
  set E' : Subgroup (MulAut Y) := E.map ψ.toMonoidHom with hE'
  have hE'abel : IsElemAbelian 3 E' := by
    rw [hE']
    exact hE.map ψ.toMonoidHom
  have hE'card : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hEcard]
  have hinner : (inner X).map ψ.toMonoidHom = inner Y := by
    rw [hψ]
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ
  have hE'inn : E' ⊓ inner Y = ⊥ := by
    rw [hE', ← hinner, ← Subgroup.map_inf E (inner X) ψ.toMonoidHom ψ.injective, hEinn,
      Subgroup.map_bot]
  obtain ⟨e', he'E', he'1, hcoatom', hidx'⟩ := h E' hE'abel hE'card hE'inn
  rw [hE', Subgroup.mem_map] at he'E'
  obtain ⟨e, he, hee'⟩ := he'E'
  have hee'' : ψ e = e' := hee'
  rw [← hee''] at he'1 hcoatom' hidx'
  have hψe : ∀ y : Y, ψ e y = φ (e (φ.symm y)) := by
    intro y
    rw [hψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hfix : fixedSubgroup (ψ e) = (fixedSubgroup e).comap (φ.symm : Y →* X) := by
    ext y
    rw [Subgroup.mem_comap]
    change ψ e y = y ↔ e (φ.symm y) = φ.symm y
    rw [hψe y]
    constructor
    · intro hh
      simpa using congrArg φ.symm hh
    · intro hh
      rw [hh, φ.apply_symm_apply]
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro h1
    exact he'1 (by rw [h1, map_one])
  · rw [hfix] at hcoatom'
    exact (Subgroup.isCoatom_comap φ.symm).mp hcoatom'
  · rw [hfix, Subgroup.index_comap_of_surjective (fixedSubgroup e) φ.symm.surjective] at hidx'
    exact hidx'

end CFSG.StandardType
