module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Cyclic subgroups have all their subgroups normalized

If a cyclic subgroup `C` of a finite group is normalized by `g`, then every
subgroup `X ≤ C` is also normalized by `g`.  The proof uses the fact that in a
cyclic group every subgroup is fully invariant under every endomorphism, so a
conjugate of `X` inside `C` with the same cardinality must be `X` itself.

(source: plan.md S4-01) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every subgroup of a cyclic group is fully invariant. -/
private theorem subgroup_map_le_of_cyclic {C : Type u} [Group C] [hcyc : IsCyclic C]
    (X : Subgroup C) (f : C →* C) : X.map f ≤ X := by
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := (Subgroup.le_zpowers_iff g X).mp (by intro z hz; exact hg z)
  obtain ⟨r, hr⟩ := MonoidHom.map_cyclic (σ := f)
  have hxmem : x ∈ Subgroup.zpowers (g ^ m) := by
    simpa [hm] using hx
  rcases Subgroup.mem_zpowers_iff.mp hxmem with ⟨k, hk⟩
  have hmz : ((g ^ r) ^ (m : ℤ)) = ((g ^ (m : ℤ)) ^ r) :=
    zpow_comm g r (m : ℤ)
  have hfx : f x = (g ^ m) ^ (r * k) := by
    calc
      f x = f ((g ^ m) ^ k) := by rw [hk]
      _ = (f (g ^ m)) ^ k := by rw [map_zpow]
      _ = (f g ^ m) ^ k := by rw [map_pow]
      _ = ((g ^ r) ^ m) ^ k := by rw [hr]
      _ = ((g ^ m) ^ r) ^ k := by
        rw [← zpow_natCast (g ^ r) m, hmz, zpow_natCast g m]
      _ = (g ^ m) ^ (r * k) := by rw [← zpow_mul]
  have hmem : (g ^ m) ^ (r * k) ∈ Subgroup.zpowers (g ^ m) := by
    exact Subgroup.zpow_mem_zpowers (g ^ m) (r * k)
  simp [hm, hfx]

/-- A conjugate of a subgroup of a cyclic subgroup is the subgroup itself
when the conjugating element normalizes the cyclic subgroup. -/
private theorem conjugateSubgroup_eq_of_normalizer_cyclic {G : Type u} [Group G] [Finite G]
    {C X : Subgroup G} (hcyc : IsCyclic C) (hXC : X ≤ C)
    {g : G} (hgC : g ∈ Subgroup.normalizer (C : Set G)) :
    conjugateSubgroup X g = X := by
  let f : C →* C :=
    { toFun := fun x => ⟨g * (x : G) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgC (x : G)).mp x.2⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change g * ((x : G) * (y : G)) * g⁻¹ =
          g * (x : G) * g⁻¹ * (g * (y : G) * g⁻¹)
        group }
  have hmap : (X.subgroupOf C).map f ≤ X.subgroupOf C :=
    subgroup_map_le_of_cyclic (X.subgroupOf C) f
  have hconj_le_X : conjugateSubgroup X g ≤ X := by
    intro y hy
    rw [conjugateSubgroup, Subgroup.mem_map] at hy
    rcases hy with ⟨x, hxX, hval⟩
    have hxc : x ∈ C := hXC hxX
    let c : C := ⟨x, hxc⟩
    have hcX : c ∈ X.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have hfcX : f c ∈ X.subgroupOf C :=
      hmap (Subgroup.mem_map.mpr ⟨c, hcX, rfl⟩)
    have hyX : (f c : G) ∈ X :=
      Subgroup.mem_subgroupOf.mp hfcX
    have hfc : (f c : G) = y := by
      change g * x * g⁻¹ = y
      simpa [MulAut.conj_apply] using hval
    simpa [hfc] using hyX
  apply Subgroup.eq_of_le_of_card_ge hconj_le_X
  rw [conjugateSubgroup]
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

/-- A subgroup of a finite cyclic subgroup is normalized by every element
normalizing the cyclic subgroup. -/
public theorem normalizer_le_normalizer_of_le_cyclic
    {G : Type u} [Group G] [Finite G]
    {C X : Subgroup G} (hcyc : IsCyclic C) (hXC : X ≤ C) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro g hgC
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact conjugateSubgroup_eq_of_normalizer_cyclic hcyc hXC hgC

end CFSG.GorensteinWalter
