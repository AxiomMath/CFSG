module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y R T L N : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}

theorem exists_psiQuot_eq_of_mem_innAutOf (c : QuasiCore R L N)
    {g : MulAut (↥L ⧸ Subgroup.center ↥L)} (hg : g ∈ innAutOf (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (l : LGL 2 V) (hl : l ∈ L), psiQuot R L c.normal ⟨l, c.le hl⟩ = g := by
  rw [← c.imgOf_psiQuot_L] at hg
  obtain ⟨⟨l, hlR⟩, hl, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩

theorem psiQuot_conj_mem_innAutOf (c : QuasiCore R L N) (r : ↥R)
    {x : MulAut (↥L ⧸ Subgroup.center ↥L)} (hx : x ∈ innAutOf (↥L ⧸ Subgroup.center ↥L)) :
    psiQuot R L c.normal r * x * (psiQuot R L c.normal r)⁻¹ ∈
      innAutOf (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨l, hl, rfl⟩ := exists_psiQuot_eq_of_mem_innAutOf c hx
  have hrl : (r : LGL 2 V) * l * (r : LGL 2 V)⁻¹ ∈ L := c.normal (r : LGL 2 V) r.2 l hl
  have hmem := apply_mem_imgOf (psiQuot R L c.normal) hrl
    (R.mul_mem (R.mul_mem r.2 (c.le hl)) (R.inv_mem r.2))
  rw [c.imgOf_psiQuot_L] at hmem
  convert hmem using 1
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem QuasiCore.not_isPGroup (h : QuasiCore R L N) : ¬ IsPGroup 2 ↥R := by
  intro hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 ↥L :=
    hR.of_injective (Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le)
  haveI : Finite ↥L := Subtype.finite
  haveI : Group.IsNilpotent ↥L := hL2.isNilpotent
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := h.quasi.2
  haveI : Nontrivial ↥L :=
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial
  haveI : Group.IsPerfect ↥L := ⟨h.quasi.1⟩
  exact Group.IsPerfect.not_isNilpotent ↥L inferInstance

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
