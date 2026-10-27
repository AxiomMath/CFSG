module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugation transport for ambient Fitting subgroups

This is the Fitting-subgroup transport used by Gorenstein--Walter Lemma 2.5.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

/-- Conjugating a subgroup conjugates its ambient Fitting subgroup. -/
public theorem fittingSubgroupOf_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (g : G) :
    fittingSubgroupOf (conjugateSubgroup A g) =
      (fittingSubgroupOf A).map (MulAut.conj g).toMonoidHom := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  let B : Subgroup G := A.map f
  let e : A ≃* B :=
    Subgroup.equivMapOfInjective A f (MulAut.conj g).injective
  have hmap_le : ∀ {X Y : Type u} [Group X] [Group Y] [Finite X] [Finite Y]
      (phi : X →* Y), Function.Surjective phi →
        (fittingSubgroup X).map phi ≤ fittingSubgroup Y := by
    intro X Y _ _ _ _ phi hphi
    have hnormal : ((fittingSubgroup X).map phi).Normal :=
      Subgroup.Normal.map (H := fittingSubgroup X) inferInstance phi hphi
    have hnil : Group.IsNilpotent ((fittingSubgroup X).map phi) := by
      have : Group.IsNilpotent (fittingSubgroup X) := by infer_instance
      let psi : fittingSubgroup X →* (fittingSubgroup X).map phi :=
        { toFun := fun x =>
            ⟨phi x, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
          map_one' := by ext; simp
          map_mul' := by intro x y; ext; simp [map_mul] }
      have hpsi : Function.Surjective psi := by
        intro y
        rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        exact hxy
      exact Group.nilpotent_of_surjective psi hpsi
    exact le_sSup ⟨hnormal, hnil⟩
  have hFmap : (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
    apply le_antisymm
    · exact hmap_le e.toMonoidHom e.surjective
    · have hback : (fittingSubgroup B).map e.symm.toMonoidHom ≤
          fittingSubgroup A := hmap_le e.symm.toMonoidHom e.symm.surjective
      have hmapped := Subgroup.map_mono (f := e.toMonoidHom) hback
      have hleft : ((fittingSubgroup B).map e.symm.toMonoidHom).map
          e.toMonoidHom = fittingSubgroup B := by
        rw [Subgroup.map_map]
        have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
          ext x
          simp
        rw [hid, Subgroup.map_id]
      rw [hleft] at hmapped
      exact hmapped
  have hmap : B.subtype.comp e.toMonoidHom = f.comp A.subtype := by
    ext x
    rfl
  calc
    fittingSubgroupOf (conjugateSubgroup A g) =
        (fittingSubgroup B).map B.subtype := rfl
    _ = ((fittingSubgroup A).map e.toMonoidHom).map B.subtype := by rw [hFmap]
    _ = (fittingSubgroup A).map (B.subtype.comp e.toMonoidHom) := by
      rw [Subgroup.map_map]
    _ = (fittingSubgroup A).map (f.comp A.subtype) := by rw [hmap]
    _ = ((fittingSubgroup A).map A.subtype).map f := by rw [Subgroup.map_map]
    _ = (fittingSubgroupOf A).map f := rfl

end

end CFSG.GorensteinWalter
