module

public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SteinbergBR
open scoped LinearAlgebra.Projectivization

theorem le_stabilizer_of_transitive_off {G Ω : Type*} [Group G] [MulAction G Ω] (α : Ω)
    {U H : Subgroup G} (hUH : U ≤ H) (hUt : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃ u ∈ U, u • β = γ)
    (hH : ¬ Nat.card Ω ∣ Nat.card H) : H ≤ MulAction.stabilizer G α := by
  intro m hm
  by_contra hmα
  rw [MulAction.mem_stabilizer_iff] at hmα
  have horbit : MulAction.orbit H α = Set.univ := by
    refine Set.eq_univ_of_forall fun β => ?_
    by_cases hβ : β = α
    · rw [hβ]
      exact MulAction.mem_orbit_self α
    · obtain ⟨u, hu, huβ⟩ := hUt (m • α) β hmα hβ
      refine ⟨⟨u * m, H.mul_mem (hUH hu) hm⟩, ?_⟩
      change (u * m) • α = β
      rw [mul_smul, huβ]
  have hidx := MulAction.index_stabilizer H α
  rw [horbit, Set.ncard_univ] at hidx
  exact hH (hidx ▸ Subgroup.index_dvd_card _)

variable {a : ℕ} {K : Type} [Field K]

theorem exists_mem_iff_conj_suzukiU [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {V : Subgroup (suzukiGroup a K)}
    (hV : IsPGroup 2 V) (hVi : ¬ 2 ∣ V.index) :
    ∃ g : suzukiGroup a K, ∀ x, x ∈ V ↔ g⁻¹ * x * g ∈ suzukiU a K := by
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SU : Sylow 2 (suzukiGroup a K) :=
    (isPGroup_suzukiU hK).toSylow (not_two_dvd_index_suzukiU hK)
  let SV : Sylow 2 (suzukiGroup a K) := hV.toSylow hVi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) SU SV
  refine ⟨g, fun x => ?_⟩
  change x ∈ (SV : Subgroup (suzukiGroup a K)) ↔ _
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj g)⁻¹ x ∈ suzukiU a K ↔ _
  rw [MulAut.inv_apply, MulAut.conj_symm_apply]

theorem exists_mem_smul_eq_of_conj_suzukiU [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K} {V : Subgroup (suzukiGroup a K)}
    (hV : ∀ x, x ∈ V ↔ g⁻¹ * x * g ∈ suzukiU a K) {β γ : ℙ K (Fin 4 → K)}
    (hβ : β ∈ suzukiOmega a K) (hγ : γ ∈ suzukiOmega a K) (hβω : β ≠ g • suzukiInfty K)
    (hγω : γ ≠ g • suzukiInfty K) : ∃ u ∈ V, u • β = γ := by
  have hdiff : ∀ {x : ℙ K (Fin 4 → K)}, x ∈ suzukiOmega a K → x ≠ g • suzukiInfty K →
      g⁻¹ • x ∈ suzukiOmega a K \ {suzukiInfty K} := fun hx hxω =>
    ⟨suzuki_smul_mem_suzukiOmega hK g⁻¹ hx, fun h => hxω (by
      rw [Set.mem_singleton_iff] at h
      rw [← h, smul_inv_smul])⟩
  obtain ⟨⟨v, hv⟩, hvβ, -⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ (hdiff hβ hβω) _
    (hdiff hγ hγω)
  refine ⟨g * v * g⁻¹, (hV _).2 (by simpa [mul_assoc] using hv), ?_⟩
  change v • g⁻¹ • β = g⁻¹ • γ at hvβ
  calc (g * v * g⁻¹) • β = g • (v • g⁻¹ • β) := by rw [mul_smul, mul_smul]
    _ = γ := by rw [hvβ, smul_inv_smul]

theorem le_normalizer_of_not_dvd_card [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {V B : Subgroup (suzukiGroup a K)}
    (hV : IsPGroup 2 V) (hVi : ¬ 2 ∣ V.index) (hVB : V ≤ B)
    (hB : ¬ (2 ^ (2 * a + 1)) ^ 2 + 1 ∣ Nat.card B) :
    B ≤ Subgroup.normalizer (V : Set (suzukiGroup a K)) := by
  obtain ⟨g, hg⟩ := exists_mem_iff_conj_suzukiU ha hK hV hVi
  have hcard : Nat.card (suzukiOmegaSub hK) = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2]
    exact Nat.card_coe_set_eq (suzukiOmega a K)
  have hstab := le_stabilizer_of_transitive_off
    (g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK)) hVB
    (fun β γ hβ hγ => by
      obtain ⟨u, hu, huβ⟩ := exists_mem_smul_eq_of_conj_suzukiU hK hg β.2 γ.2
        (fun h => hβ (Subtype.ext h)) (fun h => hγ (Subtype.ext h))
      exact ⟨u, hu, Subtype.ext huβ⟩) (by rwa [hcard])
  intro b hb
  have hbω := (MulAction.mem_stabilizer_iff.1 (hstab hb))
  have hbB : g⁻¹ * b * g ∈ suzukiB a K := by
    rw [← (suzuki_ovoid_stabilizer hK).2, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hbω,
      inv_smul_smul]
  have hbN : g⁻¹ * b * g ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK) hbB
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hg x, hg (b * x * b⁻¹), Subgroup.mem_normalizer_iff.1 hbN (g⁻¹ * x * g),
    show g⁻¹ * b * g * (g⁻¹ * x * g) * (g⁻¹ * b * g)⁻¹ = g⁻¹ * (b * x * b⁻¹) * g by group]

end CFSG.Quasithin.H13.NQCore
