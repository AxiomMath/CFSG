module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicIndexTwo
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Reflected cyclic subgroups inside an index-two subgroup

When a finite cyclic subgroup crosses an index-two subgroup, its intersection
has half the cyclic subgroup's order.  An involution in the index-two subgroup
which reflects the cyclic subgroup extends that intersection to a dihedral
subgroup of the original cyclic subgroup's order.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Let `H` have index two and let a cyclic subgroup `U` of order `2 * m`
cross `H`.  If an involution in `H \ U` inverts `U`, then the reflected
intersection inside `H` is dihedral of order `Nat.card U`. -/
public theorem exists_dihedral_subgroup_le_index_two_of_reflected_cyclic
    {G : Type u} [Group G] [Finite G]
    (H U : Subgroup G) (hHindex : H.index = 2)
    (hUcyclic : IsCyclic U) (m : ℕ)
    (hUcard : Nat.card U = 2 * m) (hUnot : ¬ U ≤ H)
    (w : G) (hwH : w ∈ H) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) :
    ∃ D : Subgroup G,
      D = (U ⊓ H) ⊔ Subgroup.zpowers w ∧ D ≤ H ∧
        ((U ⊓ H).subgroupOf D).index = 2 ∧
        Nat.card D = Nat.card U ∧ Nonempty (D ≃* DihedralGroup m) := by
  let : IsCyclic U := hUcyclic
  let : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  let R : Subgroup G := U ⊓ H
  let RU : Subgroup U := H.subgroupOf U
  have hRUindex : RU.index = 2 := by
    have hdvd : RU.index ∣ 2 := by
      change H.relIndex U ∣ 2
      simpa [hHindex] using
        (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := U))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exfalso
      have htop : RU = ⊤ := Subgroup.index_eq_one.mp hone
      apply hUnot
      intro x hxU
      have hx : (⟨x, hxU⟩ : U) ∈ RU := by
        rw [htop]
        trivial
      exact hx
    · exact htwo
  have hRUcard : Nat.card RU = m := by
    have hmul := RU.card_mul_index
    rw [hRUindex, hUcard] at hmul
    omega
  let eRU : R ≃* RU :=
    { toFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x, ⟨x.1.property, x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intro x y; rfl }
  have hRcard : Nat.card R = m := by
    rw [Nat.card_congr eRU.toEquiv, hRUcard]
  have hmpos : 0 < m := by
    have hUpos : 0 < Nat.card U := Nat.card_pos
    rw [hUcard] at hUpos
    omega
  have hRcyclic : IsCyclic R :=
    Subgroup.isCyclic_of_le (H := R) (H' := U) (by
      dsimp [R]
      exact inf_le_left)
  obtain ⟨r, hrgen⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top R).mp hRcyclic
  have hrR : r ∈ R := by
    rw [← hrgen]
    exact Subgroup.mem_zpowers r
  let D : Subgroup G := R ⊔ Subgroup.zpowers w
  let ρ : D := ⟨r, (le_sup_left : R ≤ D) hrR⟩
  let σ : D :=
    ⟨w, (le_sup_right : Subgroup.zpowers w ≤ D)
      (Subgroup.mem_zpowers w)⟩
  have hDleH : D ≤ H := by
    apply sup_le
    · exact inf_le_right
    · exact Subgroup.zpowers_le.mpr hwH
  have hgen : (⊤ : Subgroup D) =
      Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply le_antisymm
    · intro x hx
      have hxmap : (x : G) ∈
          (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).map D.subtype := by
        simp [Subgroup.map_sup, MonoidHom.map_zpowers, ρ, σ, D, hrgen, x.2]
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σ, pow_two] using hwsq
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    exact hwinv r (show r ∈ U from hrR.1)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    apply hwU
    rcases (Subgroup.mem_zpowers_iff).mp hmem with ⟨k, hk⟩
    have hkval : w = (r : G) ^ k := congrArg Subtype.val hk.symm
    rw [hkval]
    exact U.zpow_mem (show r ∈ U from hrR.1) k
  have hdih :=
    dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hordρ : orderOf ρ = orderOf r :=
    (orderOf_injective D.subtype D.subtype_injective ρ).symm
  have hordr : orderOf r = Nat.card R := by
    rw [← Nat.card_zpowers, hrgen]
  have hDequiv : Nonempty (D ≃* DihedralGroup m) := by
    rw [hordρ, hordr, hRcard] at hdih
    exact hdih
  have hDcard : Nat.card D = Nat.card U := by
    calc
      Nat.card D = Nat.card (DihedralGroup m) :=
        Nat.card_congr hDequiv.some.toEquiv
      _ = 2 * m := DihedralGroup.nat_card
      _ = Nat.card U := hUcard.symm
  let RD : Subgroup D := R.subgroupOf D
  have hRDcard : Nat.card RD = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show R ≤ D from le_sup_left))
  have hRDindex : RD.index = 2 := by
    have hmul : RD.index * m = 2 * m := by
      calc
        RD.index * m = RD.index * Nat.card RD := by rw [hRDcard, hRcard]
        _ = Nat.card D := RD.index_mul_card
        _ = Nat.card U := hDcard
        _ = 2 * m := hUcard
    exact Nat.eq_of_mul_eq_mul_right hmpos hmul
  exact ⟨D, rfl, hDleH, by simpa [RD, R] using hRDindex,
    hDcard, hDequiv⟩

end CFSG.GorensteinWalter
