module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sec2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace E9P2.E1

section Normal

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_le {K H G₁ : Subgroup G} (hKH : K ≤ H) (hHG : H ≤ G₁)
    (hn : G₁ ≤ Subgroup.normalizer (K : Set G)) : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 G₁ := by
  have hp : IsPGroup 2 (K ⊓ pCoreOf 2 H : Subgroup G) := (pCoreOf_isPGroup 2 H).to_inf_right
  have hKn : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) h
    have h2 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hk)) h
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  have h1 : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := le_pCoreOf_of_le_normalizer 2 inf_le_left hKn hp
  have h2 : pCoreOf 2 K ≤ pCoreOf 2 G₁ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans (hKH.trans hHG))
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  exact h1.trans h2

theorem inf_pCoreOf_eq_bot {P : Subgroup G} (H : Subgroup G) (hP9 : Nat.card P = 9) :
    P ⊓ pCoreOf 2 H = ⊥ := by
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
  have h1 : Nat.card ↥(P ⊓ pCoreOf 2 H) ∣ 9 := hP9 ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(P ⊓ pCoreOf 2 H) ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))

end Normal

section Action

open E9P2.Sec

variable {G : Type} [Group G] {T H PQ : Subgroup G} {V : Type} [CommGroup V] [Finite V]
  {β : ↥H →* MulAut V}

theorem exists_sigma (hb : BetaData T H PQ β) :
    ∃ σ ∈ T, (∀ t ∈ T, ∃ i : ℕ, t * (σ ^ i)⁻¹ ∈ pCoreOf 2 H) ∧
      ∀ y ∈ PQ, σ ^ 2 * y * (σ ^ 2)⁻¹ * y ∈ pCoreOf 2 H := by
  obtain ⟨g, hg⟩ := hb.str.cyclic_Tb
  obtain ⟨u, hu, hug⟩ := g.2
  have hgo : orderOf g = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hb.str.card_Tb
  have hgo' : orderOf (g : MulAut V) = 4 := by rw [Subgroup.orderOf_coe, hgo]
  refine ⟨(u : G), Subgroup.mem_subgroupOf.mp hu, ?_, ?_⟩
  · intro t ht
    have hmem : β ⟨t, hb.TH ht⟩ ∈ (T.subgroupOf H).map β :=
      ⟨_, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have hgt := (Submonoid.mem_powers_iff _ _).mp
      ((mem_powers_iff_mem_zpowers).mpr (hg ⟨β ⟨t, hb.TH ht⟩, hmem⟩))
    obtain ⟨i, hi⟩ := hgt
    have hi' : (g : MulAut V) ^ i = β ⟨t, hb.TH ht⟩ := congrArg Subtype.val hi
    refine ⟨i, (hb.beta_eq_one_iff (⟨t, hb.TH ht⟩ * (u ^ i)⁻¹)).mp ?_⟩
    rw [map_mul, map_inv, map_pow, hug, hi', mul_inv_cancel]
  · intro y hy
    have hyH : y ∈ H := hb.PQH hy
    have hymem : β ⟨y, hyH⟩ ∈ (PQ.subgroupOf H).map β :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hrange : (g : MulAut V) ^ 2 ∈ β.range := ⟨u ^ 2, by rw [map_pow, hug]⟩
    have hord2 : orderOf ((g : MulAut V) ^ 2) = 2 := by
      rw [orderOf_pow' _ (by norm_num), hgo']
      norm_num
    have hinv := hb.str.inverts_of_involution hrange hord2 _ hymem
    refine (hb.beta_eq_one_iff (u ^ 2 * ⟨y, hyH⟩ * (u ^ 2)⁻¹ * ⟨y, hyH⟩)).mp ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_pow, hug]
    have h2 : (g : MulAut V) ^ 2 * β ⟨y, hyH⟩ * ((g : MulAut V) ^ 2)⁻¹ = (β ⟨y, hyH⟩)⁻¹ := hinv
    rw [h2, inv_mul_cancel]

theorem exists_mem_mul (hb : BetaData T H PQ β) {P : Subgroup G} (hPPQ : P ≤ PQ)
    (hP9 : Nat.card P = 9) (hPQ : P ⊓ pCoreOf 2 H = ⊥) {k : G} (hk : k ∈ PQ) :
    ∃ x ∈ P, x⁻¹ * k ∈ pCoreOf 2 H := by
  have hkmem : β ⟨k, hb.PQH hk⟩ ∈ (PQ.subgroupOf H).map β :=
    ⟨_, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  rw [← hb.map_sylow_eq hPPQ hP9 hPQ] at hkmem
  obtain ⟨u, hu, huk⟩ := hkmem
  refine ⟨(u : G), Subgroup.mem_subgroupOf.mp hu, ?_⟩
  refine (hb.beta_eq_one_iff (u⁻¹ * ⟨k, hb.PQH hk⟩)).mp ?_
  rw [map_mul, map_inv, huk, inv_mul_cancel]

end Action

end E9P2.E1

end CFSG.Quasithin
