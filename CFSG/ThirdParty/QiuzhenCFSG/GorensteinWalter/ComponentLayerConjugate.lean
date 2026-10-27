module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugation transport for component layers

This is the layer transport used by Gorenstein--Walter Lemma 2.5.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

/-- Conjugating a subgroup conjugates its component layer. -/
public theorem componentLayerOf_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (g : G) :
    componentLayerOf (conjugateSubgroup A g) =
      (componentLayerOf A).map (MulAut.conj g).toMonoidHom := by
  have hquasi : ∀ {X Y : Type u} [Group X] [Group Y]
      (e : X ≃* Y) {Q : Subgroup X}, IsQuasisimple Q →
        IsQuasisimple (Q.map e.toMonoidHom) := by
    intro X Y _ _ e Q hQ
    let eQ : Q ≃* Q.map e.toMonoidHom :=
      Subgroup.equivMapOfInjective Q e.toMonoidHom e.injective
    have hNontriv : Nontrivial (Q.map e.toMonoidHom) := by
      let : Nontrivial Q := hQ.1
      exact eQ.toEquiv.injective.nontrivial
    have hPerf : Group.IsPerfect (Q.map e.toMonoidHom) := by
      let : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ.2.1
      exact Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
    have hCenter : (Subgroup.center Q).map eQ.toMonoidHom =
        Subgroup.center (Q.map e.toMonoidHom) := by
      apply le_antisymm
      · intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact (Subgroup.centerCongr eQ ⟨y, hy⟩).2
      · intro x hx
        refine ⟨eQ.symm x, ?_, ?_⟩
        · exact ((Subgroup.centerCongr eQ).symm ⟨x, hx⟩).2
        · exact eQ.apply_symm_apply x
    have hSimple : IsSimpleGroup
        ((Q.map e.toMonoidHom) ⧸ Subgroup.center (Q.map e.toMonoidHom)) := by
      exact (MulEquiv.isSimpleGroup_congr
        (QuotientGroup.congr (Subgroup.center Q)
          (Subgroup.center (Q.map e.toMonoidHom)) eQ hCenter)).mp hQ.2.2
    exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩
  have hcomponent : ∀ {X Y : Type u} [Group X] [Group Y]
      (e : X ≃* Y) {E H : Subgroup X}, IsComponentOf E H →
        IsComponentOf (E.map e.toMonoidHom) (H.map e.toMonoidHom) := by
    intro X Y _ _ e E H hE
    let eH : H ≃* H.map e.toMonoidHom :=
      Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
    have hsub : ((E.subgroupOf H).map eH.toMonoidHom).IsSubnormal :=
      hE.2.1.map (f := eH.toMonoidHom) eH.surjective
    have heq : (E.subgroupOf H).map eH.toMonoidHom =
        (E.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mp hy
        · exact congrArg Subtype.val hxy
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hyH : y ∈ H := hE.1 hy
        refine Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr hy
        · apply Subtype.ext
          exact hxy
    refine ⟨Subgroup.map_mono hE.1, ?_, hquasi e hE.2.2⟩
    rwa [← heq]
  let e : G ≃* G := MulAut.conj g
  let B : Subgroup G := A.map e.toMonoidHom
  change componentLayerOf B = (componentLayerOf A).map e.toMonoidHom
  apply le_antisymm
  · rw [componentLayerOf]
    refine sSup_le ?_
    intro F hF
    have hFinv : IsComponentOf (F.map e.symm.toMonoidHom)
        (B.map e.symm.toMonoidHom) := hcomponent e.symm hF
    have hBback : B.map e.symm.toMonoidHom = A := by
      ext x
      simp [B]
    rw [hBback] at hFinv
    have hle : F.map e.symm.toMonoidHom ≤ componentLayerOf A :=
      le_sSup (s := {E : Subgroup G | IsComponentOf E A}) hFinv
    have hmapped := Subgroup.map_mono (f := e.toMonoidHom) hle
    have hFback : (F.map e.symm.toMonoidHom).map e.toMonoidHom = F := by
      ext x
      simp
    rwa [hFback] at hmapped
  · refine Subgroup.map_le_iff_le_comap.mpr ?_
    rw [componentLayerOf]
    refine sSup_le ?_
    intro E hE
    have hEmap : IsComponentOf (E.map e.toMonoidHom) B := hcomponent e hE
    exact Subgroup.map_le_iff_le_comap.mp
      (le_sSup (s := {F : Subgroup G | IsComponentOf F B}) hEmap)

end

end CFSG.GorensteinWalter
