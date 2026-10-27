module

public import CFSG.Quasithin.Background.SmithB45TorTits
public import CFSG.GroupTheory.ElemAbelianPlaneAction

public section

namespace CFSG.Quasithin.B45Tor

open CFSG.Sporadic.Schreier.Tits


theorem index_titsR : titsR.index = 718848 := by
  have h := titsR.card_mul_index
  rw [card_titsR, card_titsD] at h
  omega

theorem exists_conj_mem_titsR {g : titsD} (hg : orderOf g = 5) :
    ∃ c : titsD, c⁻¹ * g * c ∈ titsR := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hR : IsPGroup 5 titsR := IsPGroup.of_card card_titsR
  let S : Sylow 5 titsD := hR.toSylow (by rw [index_titsR]; norm_num)
  have hS : (S : Subgroup titsD) = titsR := IsPGroup.toSylow_coe _ _
  have hp : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨c, hc⟩ := CFSG.LieType.BorelTits.exists_conj_mem_sylow S hp
  refine ⟨c, ?_⟩
  have h := hc g (Subgroup.mem_zpowers g)
  rwa [hS] at h

theorem two_pow_twenty_le_index_fixV {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (σ : titsD →* MulAut V) (hσ : Function.Injective σ) {g : titsD}
    (hg : orderOf g = 5) : 2 ^ 20 ≤ (fixV (Subgroup.zpowers (σ g))).index := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_conj_mem_titsR hg
  have hne : c⁻¹ * g * c ≠ 1 := by
    intro h
    have h1 : g = 1 := by
      have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      rw [e, h, mul_one, mul_inv_cancel]
    rw [h1, orderOf_one] at hg
    norm_num at hg
  obtain ⟨hN, horb⟩ := orbit_data_map σ hσ (closure_le_normalizer titsR_q8)
    (fun K hKR hK => six_le_orbit_of_eq_five rfl titsR_pow card_titsR titsR_q8 hKR hK)
  have h := two_pow_le_index_fixV_of_mem hV (by norm_num : (5 : ℕ) ≠ 2) (titsR.map σ)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, titsR_comm a ha b hb, map_mul])
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_pow, titsR_pow r hr, map_one])
    (by rw [Subgroup.card_map_of_injective hσ, card_titsR]) _ hN horb
    (r := σ (c⁻¹ * g * c)) ⟨_, hc, rfl⟩ (fun h1 => hne (hσ (h1.trans (map_one σ).symm)))
  have hconj : σ (c⁻¹ * g * c) = (σ c)⁻¹ * σ g * ((σ c)⁻¹)⁻¹ := by
    rw [inv_inv, map_mul, map_mul, map_inv]
  rw [hconj, CFSG.QuasithinUnique.Setup.X5.index_fixV_conj,
    CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_five] at h
  simpa using h

end CFSG.Quasithin.B45Tor
