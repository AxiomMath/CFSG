module

public import CFSG.Quasithin.Background.A4FourQuot
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_oTwoUpper_sup_pCoreOf_of_perfect {H : Subgroup G}
    (hperf : Group.IsPerfect (oTwoQuot ↥H)) :
    H = oTwoUpper H ⊔ pCoreOf 2 H := by
  classical
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : Group.IsPerfect (oTwoQuot ↥H) := hperf
  have htop : oTwoUpper (⊤ : Subgroup (oTwoQuot ↥H)) = ⊤ :=
    le_antisymm (oTwoUpper_le _) (perfect_le_oTwoUpper le_rfl inferInstance)
  have hmap : (oTwoUpper (⊤ : Subgroup ↥H)).map π = ⊤ := by
    rw [← oTwoUpper_map π (⊤ : Subgroup ↥H), Subgroup.map_top_of_surjective π hπ]
    exact htop
  have hmaps : (oTwoUpper (⊤ : Subgroup ↥H)).map π = (⊤ : Subgroup ↥H).map π := by
    rw [hmap, Subgroup.map_top_of_surjective π hπ]
  have htopH : (oTwoUpper (⊤ : Subgroup ↥H)) ⊔ π.ker = ⊤ := by
    have h := (Subgroup.map_eq_map_iff (f := π)).mp hmaps
    simpa using h
  have hker : π.ker = pCore 2 ↥H := QuotientGroup.ker_mk' _
  have hsub : oTwoUpper (⊤ : Subgroup ↥H) = (oTwoUpper H).subgroupOf H := by
    have h2 := oTwoUpper_map H.subtype (⊤ : Subgroup ↥H)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rw [h2]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) _).symm
  have htopH' : (oTwoUpper H).subgroupOf H ⊔ pCore 2 ↥H = ⊤ := by
    rw [← hsub]
    simpa [hker] using htopH
  have h := congrArg (Subgroup.map H.subtype) htopH'
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le H)] at h
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  exact h.symm

theorem commutator_le_of_le_oTwoUpper_sup {H Z Y Q : Subgroup G}
    (hH : H ≤ oTwoUpper H ⊔ Q)
    (hQN : Q ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hQZ : Q ≤ Subgroup.centralizer (Z : Set G))
    (hO2 : ⁅Z, oTwoUpper H⁆ ≤ Y) :
    ⁅H, Z⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro h hh z hz
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQN).mp (hH hh)
  have hqz : z * q = q * z :=
    (Subgroup.mem_centralizer_iff.mp (hQZ hq)) z hz
  have hqconj : q * z * q⁻¹ = z := by
    rw [← hqz]
    group
  have hpz : ⁅p, z⁆ ∈ Y := by
    have h1 : ⁅z, p⁆ ∈ Y := hO2 (Subgroup.commutator_mem_commutator hz hp)
    have h2 : ⁅z, p⁆⁻¹ ∈ Y := Y.inv_mem h1
    rwa [commutatorElement_inv] at h2
  have hgoal : ⁅p * q, z⁆ = ⁅p, z⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc p * q * z * (p * q)⁻¹ * z⁻¹
        = p * (q * z * q⁻¹) * p⁻¹ * z⁻¹ := by group
      _ = p * z * p⁻¹ * z⁻¹ := by rw [hqconj]
  rw [hgoal]
  exact hpz

end CFSG.Quasithin

end
