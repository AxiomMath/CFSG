module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral two-subgroups from reflected cyclic subgroups

This module packages the generic subgroup construction used for the split
and nonsplit tori in `PSL₂`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If an external involution inverts an even finite cyclic subgroup, then
the ambient group contains the dihedral group built from the full `2`-part
of that cyclic subgroup. -/
public theorem exists_dihedral_two_subgroup_of_cyclic_reflection
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (w : G)
    (hUcyclic : IsCyclic U) (hUeven : 2 ∣ Nat.card U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ t : G, t ∈ U → w * t * w⁻¹ = t⁻¹) :
    ∃ D : Subgroup G,
      1 ≤ (Nat.card U).factorization 2 ∧
        Nonempty (D ≃* DihedralGroup (2 ^ (Nat.card U).factorization 2)) := by
  obtain ⟨R, hRU, hRcyclic, hRcard⟩ :=
    exists_cyclic_sylow_subgroup_le 2 U hUcyclic
  obtain ⟨r, hrgen⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top R).mp hRcyclic
  let D : Subgroup G := R ⊔ Subgroup.zpowers w
  have hrR : r ∈ R := by
    rw [← hrgen]
    exact Subgroup.mem_zpowers r
  let ρ : D := ⟨r, (le_sup_left : R ≤ D) hrR⟩
  let σ : D :=
    ⟨w, (le_sup_right : Subgroup.zpowers w ≤ D)
      (Subgroup.mem_zpowers w)⟩
  have hgen : (⊤ : Subgroup D) =
      Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply le_antisymm
    · intro x hx
      have hxmap : (x : G) ∈
          (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).map D.subtype := by
        simpa [Subgroup.map_sup, MonoidHom.map_zpowers, ρ, σ, D, hrgen] using x.2
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σ, pow_two] using hwsq
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    exact hwinv r (hRU hrR)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    apply hwU
    apply hRU
    rw [← hrgen]
    rcases (Subgroup.mem_zpowers_iff).mp hmem with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    exact congrArg Subtype.val hk
  have hdih :=
    dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hordρ : orderOf ρ = orderOf r :=
    (orderOf_injective D.subtype D.subtype_injective ρ).symm
  have hordr : orderOf r = Nat.card R := by
    rw [← Nat.card_zpowers, hrgen]
  have hmpos : 1 ≤ (Nat.card U).factorization 2 := by
    exact Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' hUeven
  refine ⟨D, hmpos, ?_⟩
  rw [hordρ, hordr, hRcard] at hdih
  exact hdih

end CFSG.GorensteinWalter
