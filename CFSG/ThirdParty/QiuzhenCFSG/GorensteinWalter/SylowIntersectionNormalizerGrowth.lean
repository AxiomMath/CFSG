module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow-intersection growth through an ambient normalizer

This is the abstract normalizer-condition step used in Section 4: if a
Sylow subgroup is not contained in `E`, then the normalizer inside that
Sylow subgroup of its intersection with `E` contains an element outside
`E`.  If that inner normalizer lies in `M`, the element lies in
`S ∩ M \ E`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Let `P` be a Sylow `p`-subgroup.  If `P ∩ N_G(P ∩ E) ≤ M` and
`P ≤ E` fails, then `P ∩ M ≤ E` also fails. -/
public theorem sylow_intersection_not_le_of_inner_normalizer_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (E M : Subgroup G)
    (hPnotE : ¬ (P : Subgroup G) ≤ E)
    (hNleM : (P : Subgroup G) ⊓
      Subgroup.normalizer ((((P : Subgroup G) ⊓ E) : Subgroup G) : Set G) ≤ M) :
    ¬ ((P : Subgroup G) ⊓ M) ≤ E := by
  classical
  let I : Subgroup G := (P : Subgroup G) ⊓ E
  let IP : Subgroup P := I.subgroupOf (P : Subgroup G)
  have hIPne : IP ≠ ⊤ := by
    intro htop
    apply hPnotE
    intro x hxP
    have hxIP : (⟨x, hxP⟩ : P) ∈ IP := by
      rw [htop]
      trivial
    exact (Subgroup.mem_subgroupOf.mp hxIP).2
  have hIPlt : IP < ⊤ := lt_of_le_of_ne le_top hIPne
  have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition P :=
    Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt : IP < Subgroup.normalizer (IP : Set P) := hnc IP hIPlt
  obtain ⟨x, hxN, hxnotIP⟩ := SetLike.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (I : Set G) := by
    have hxsub : x ∈
        (Subgroup.normalizer (I : Set G)).subgroupOf (P : Subgroup G) := by
      rw [Subgroup.subgroupOf_normalizer_eq
        (show I ≤ (P : Subgroup G) from inf_le_left)]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  have hxM : (x : G) ∈ M := hNleM ⟨x.2, hxNorm⟩
  have hxnotE : (x : G) ∉ E := by
    intro hxE
    exact hxnotIP (Subgroup.mem_subgroupOf.mpr ⟨x.2, hxE⟩)
  intro hle
  exact hxnotE (hle ⟨x.2, hxM⟩)

end CFSG.GorensteinWalter
