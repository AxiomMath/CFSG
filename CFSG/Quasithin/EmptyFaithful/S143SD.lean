module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_into_sylow {H S : Subgroup G} (hS : IsSylowTwoOf S H) {u : G} (hu : u ∈ H)
    (hu2 : u * u = 1) : ∃ s ∈ H, s⁻¹ * u * s ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hS2, hSidx⟩ := hS
  have hK2 : IsPGroup 2 ↥(S.subgroupOf H) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  let K : Sylow 2 ↥H := hK2.toSylow hSidx
  let u' : ↥H := ⟨u, hu⟩
  have hu'2 : u' * u' = 1 := Subtype.ext hu2
  have hord : orderOf u' ∣ 2 ^ 1 := by
    rw [pow_one]; exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu'2)
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers u') := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm'])
  obtain ⟨P', hP'⟩ := hz2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥H) K P'
  have hmem : u' ∈ ((h • K : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [hh]; exact hP' (Subgroup.mem_zpowers u')
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hmem
  obtain ⟨k, hk, hku⟩ := Subgroup.mem_map.mp hmem
  have hkS : (k : G) ∈ S := by
    have : k ∈ (K : Subgroup ↥H) := hk
    have h2 : (K : Subgroup ↥H) = S.subgroupOf H := rfl
    rw [h2] at this
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨(h : G), h.2, ?_⟩
  have e : u = (h : G) * (k : G) * (h : G)⁻¹ := by
    have := congrArg Subtype.val hku
    simpa [MulAut.conj_apply] using this.symm
  rw [e]
  have : (h : G)⁻¹ * ((h : G) * (k : G) * (h : G)⁻¹) * (h : G) = (k : G) := by group
  rw [this]; exact hkS

omit [Finite G] in
theorem fusion_of_zfus {z w : G}
    (hz : ∀ u : G, (∃ s : G, u = s * z * s⁻¹) → u * w = w * u →
      ∃ k : G, k * w = w * k ∧ k * z * k⁻¹ = u)
    {y : G} (hy : z * (y * w * y⁻¹) = (y * w * y⁻¹) * z) :
    ∃ h : G, h * z = z * h ∧ y * w * y⁻¹ = h * w * h⁻¹ := by
  have hu : (y⁻¹ * z * y) * w = w * (y⁻¹ * z * y) := by
    calc (y⁻¹ * z * y) * w = y⁻¹ * (z * (y * w * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * w * y⁻¹) * z) * y := by rw [hy]
      _ = w * (y⁻¹ * z * y) := by group
  obtain ⟨k, hk, hkz⟩ := hz (y⁻¹ * z * y) ⟨y⁻¹, by group⟩ hu
  refine ⟨y * k, ?_, ?_⟩
  · have e : (y * k) * z * (y * k)⁻¹ = z := by
      calc (y * k) * z * (y * k)⁻¹ = y * (k * z * k⁻¹) * y⁻¹ := by group
        _ = z := by rw [hkz]; group
    calc (y * k) * z = ((y * k) * z * (y * k)⁻¹) * (y * k) := by group
      _ = z * (y * k) := by rw [e]
  · have hkw : k * w * k⁻¹ = w := by
      calc k * w * k⁻¹ = (w * k) * k⁻¹ := by rw [hk]
        _ = w := by group
    calc y * w * y⁻¹ = y * (k * w * k⁻¹) * y⁻¹ := by rw [hkw]
      _ = (y * k) * w * (y * k)⁻¹ := by group

end Generic

end S143

end CFSG.Quasithin
