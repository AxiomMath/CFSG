module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.EquivariantStabilizerSylow

open MulAction

private def stabilizerHom
    {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X]
    (φ:G→*H) (he:∀(g:G)(x:X),φ g • x=g • x) (x:X) :
    stabilizer G x →* stabilizer H x :=
  { toFun := fun g=>⟨φ g,(he g x).trans g.property⟩
    map_one' := Subtype.ext φ.map_one
    map_mul' := fun a b=>Subtype.ext (φ.map_mul a b) }

private theorem stabilizerHom_surjective
    {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X]
    (φ:G→*H) (hφ:Function.Surjective φ) (he:∀(g:G)(x:X),φ g • x=g • x) (x:X) :
    Function.Surjective (stabilizerHom φ he x) := by
  intro h
  obtain ⟨g,hg⟩ := hφ h
  have hfix:g • x=x := by rw [←he,hg]; exact h.property
  exact ⟨⟨g,hfix⟩,Subtype.ext hg⟩

theorem preimage_sylow
    {G H X : Type*} [Group G] [Finite G] [Group H] [MulAction G X] [MulAction H X]
    {p:ℕ} [Fact p.Prime]
    (φ:G→*H) (hφ:Function.Surjective φ) (he:∀(g:G)(x:X),φ g • x=g • x)
    (x:X) (S:Sylow p (stabilizer H x)) :
    ∃R:Sylow p (stabilizer G x),
      (S:Subgroup (stabilizer H x)).map (stabilizer H x).subtype =
      ((R:Subgroup (stabilizer G x)).map (stabilizer G x).subtype).map φ := by
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective (stabilizerHom_surjective φ hφ he x) p S
  refine ⟨R,?_⟩
  rw [←hR]
  change ((R:Subgroup (stabilizer G x)).map (stabilizerHom φ he x)).map (stabilizer H x).subtype = _
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1

end FiveTransitive.EquivariantStabilizerSylow

end CFSG
