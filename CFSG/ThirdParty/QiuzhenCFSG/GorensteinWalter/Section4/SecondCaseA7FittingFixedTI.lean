module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7NormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Trivial intersections for the A7 fixed part

If `F ∩ F^g` were nontrivial, applying normalizer-layer control before and
after conjugating the intersection back by `g⁻¹` would give `E^g = E`.
The normalizer of the nontrivial normal component `E ◁ M` is exactly the
maximal subgroup `M`, contradicting `g ∉ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The equation-(4) fixed part has trivial intersection with each conjugate
by an element outside the second-case maximal subgroup. -/
public theorem secondCase_a7_fitting_fixed_TI
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (F : Subgroup G)
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (g : G) (hg : g ∉ w.M) :
    F ⊓ conjugateSubgroup F g = ⊥ := by
  classical
  let X : Subgroup G := F ⊓ conjugateSubgroup F g
  by_contra hXbot
  have hXne : X ≠ ⊥ := by simpa [X] using hXbot
  have hXleF : X ≤ F := inf_le_left
  let Y : Subgroup G := conjugateSubgroup X g⁻¹
  have hYmap : conjugateSubgroup Y g = X := by
    simpa [Y] using conj_inv_then_conj_eq X g
  have hYleF : Y ≤ F := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxConj : x ∈ conjugateSubgroup F g :=
      (inf_le_right : X ≤ conjugateSubgroup F g) hx
    rcases Subgroup.mem_map.mp hxConj with ⟨f, hf, hxf⟩
    have hxf' : x = g * f * g⁻¹ := by
      simpa [conjugateSubgroup, MulAut.conj_apply] using hxf.symm
    have heq : (MulAut.conj g⁻¹).toMonoidHom x = f := by
      rw [hxf']
      simp
      group
    rw [heq]
    exact hf
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    apply hXne
    rw [← hYmap]
    simp [conjugateSubgroup, hYbot]
  have hLayerX : componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E :=
    secondCase_a7_normalizer_layer_eq_component
      hmin c w d hA7 hmodel F X hFleFU hFleM hFcentE hXne hXleF
  have hLayerY : componentLayerOf (Subgroup.normalizer (Y : Set G)) = d.E :=
    secondCase_a7_normalizer_layer_eq_component
      hmin c w d hA7 hmodel F Y hFleFU hFleM hFcentE hYne hYleF
  have hmapN : conjugateSubgroup (Subgroup.normalizer (Y : Set G)) g =
      Subgroup.normalizer (X : Set G) := by
    have hYmap' : Y.map (MulAut.conj g).toMonoidHom = X := by
      simpa [conjugateSubgroup] using hYmap
    change (Subgroup.normalizer (Y : Set G)).map
        (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g).bijective]
    rw [hYmap']
  have hEg : conjugateSubgroup d.E g = d.E := by
    calc
      conjugateSubgroup d.E g =
          conjugateSubgroup
            (componentLayerOf (Subgroup.normalizer (Y : Set G))) g := by
        rw [hLayerY]
      _ = componentLayerOf
          (conjugateSubgroup (Subgroup.normalizer (Y : Set G)) g) := by
        simpa [conjugateSubgroup] using
          (componentLayerOf_conjugateSubgroup
            (Subgroup.normalizer (Y : Set G)) g).symm
      _ = componentLayerOf (Subgroup.normalizer (X : Set G)) := by rw [hmapN]
      _ = d.E := hLayerX
  have hgNE : g ∈ Subgroup.normalizer (d.E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxmap : g * x * g⁻¹ ∈ conjugateSubgroup d.E g :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hEg] at hxmap
    · intro hxconj
      have hxconjMap : g * x * g⁻¹ ∈ conjugateSubgroup d.E g := by
        rwa [hEg]
      rcases Subgroup.mem_map.mp hxconjMap with ⟨y, hy, hyx⟩
      have hyxeq : y = x := by
        apply (MulAut.conj g).injective
        simpa [MulAut.conj_apply] using hyx
      rwa [← hyxeq]
  have hEnormalSub : (d.E.subgroupOf w.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff d.E_component.1]
    intro e m he hm
    exact d.E_normal.2 m hm e he
  have hNE : Subgroup.normalizer (d.E : Set G) = w.M :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) w.M_maximal d.E_component.1
        ((Subgroup.nontrivial_iff_ne_bot d.E).mp d.E_component.2.2.1)
        hEnormalSub
  exact hg (by rwa [← hNE])

end CFSG.GorensteinWalter
