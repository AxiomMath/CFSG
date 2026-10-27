module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWChain
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWCentAux
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL48NonCyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S

theorem ggL48NormalInputS_of_nonCyclic (hNC : GGL48NonCyclicInput) : GGL48NormalInputS := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h hh
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hsS.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  obtain ⟨S, hSL, hSp, hSnc⟩ := hNC G p B Bs x L D J X B₂ d y K U U₁ hS
  set H := Subgroup.centralizer ({x} : Set G) with hH
  have hLH : L ≤ H := hcomp.1
  have hL' : CFSG.IsComponent (L.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLH).1 hcomp
  let e : H ≃* H := MulAut.conj (⟨h, hh⟩ : H)
  have hL'' : CFSG.IsComponent ((L.subgroupOf H).map e.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e hL'
  rcases CFSG.LocalCores.distinct_components_commute hL' hL'' with heq | hcomm
  · refine GGL48TW.Cent.mem_normalizer_of_conj_mem fun y hy => ?_
    have hy' : (⟨y, hLH hy⟩ : H) ∈ L.subgroupOf H := hy
    have hmem : e ⟨y, hLH hy⟩ ∈ (L.subgroupOf H).map e.toMonoidHom := ⟨_, hy', rfl⟩
    rw [← heq] at hmem
    exact hmem
  · exfalso
    have hcommute : ∀ l ∈ L, ∀ l' ∈ L, (h * l' * h⁻¹) * l = l * (h * l' * h⁻¹) := by
      intro l hl l' hl'
      have hA : (⟨l, hLH hl⟩ : H) ∈ L.subgroupOf H := hl
      have hB : e ⟨l', hLH hl'⟩ ∈ (L.subgroupOf H).map e.toMonoidHom := ⟨_, hl', rfl⟩
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hA
      have h2 := Subgroup.mem_centralizer_iff.mp h1 _ hB
      exact congrArg Subtype.val h2
    have hS'C : S.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer (L : Set G) := by
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hcommute l hl s (hSL hs)).symm
    have hS'cyc : IsCyclic (S.map (MulAut.conj h).toMonoidHom) :=
      hcyc _ hS'C (hSp.map _)
    exact hSnc (isCyclic_of_surjective
      (S.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective).symm.toMonoidHom
      (MulEquiv.surjective _))

end CFSG.StandardType
