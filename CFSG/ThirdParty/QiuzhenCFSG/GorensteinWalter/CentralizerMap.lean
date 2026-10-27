module

public import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

/-! # Mapping subgroup centralizers -/

namespace CFSG.GorensteinWalter

universe u

/-- A homomorphism maps a subgroup centralizing another subgroup into the
centralizer of the latter's image. -/
public theorem centralizer_map_le_of_hom
    {G H : Type u} [Group G] [Group H] (f : G →* H)
    (A V : Subgroup G)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    V.map f ≤ Subgroup.centralizer ((A.map f : Subgroup H) : Set H) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
  rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
  have hvcomm : a0 * v = v * a0 :=
    (Subgroup.mem_centralizer_iff.mp (hVleC hv)) a0 ha0
  simpa [map_mul] using congrArg f hvcomm

end CFSG.GorensteinWalter
