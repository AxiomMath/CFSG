module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace TwoComp

variable {G : Type} [Group G] [Finite G] {T H K₁ K₂ : Subgroup G}

theorem sq_dvd_card (tc : TwoComp T H K₁ K₂) (hK₁ : K₁ ∈ cComp H) (hTH : IsSylowTwoOf T H)
    {n : ℕ} (hn : 2 ≤ n) (hL : LieModel (O2Q K₁) .PSL 2 2 n) {B : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B
      (oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G))) :
    (2 ^ n - 1) ^ 2 ∣ Nat.card ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₂ : K₂ ∈ cComp H := tc.cK₂
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hK₁K : K₁ ≤ oTwoUpper H := tc.sup ▸ le_sup_left
  have hK₂K : K₂ ≤ oTwoUpper H := tc.sup ▸ le_sup_right
  have hK₁H : K₁ ≤ H := hK₁K.trans hKH
  have hKN₁ : oTwoUpper H ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [tc.sup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK₁ hK₂)
  have hKN₂ : oTwoUpper H ≤ Subgroup.normalizer (K₂ : Set G) := by
    rw [tc.sup]
    exact sup_le (le_normalizer_of_mem_cComp hK₂ hK₁) Subgroup.le_normalizer
  have hY₁ := tc.borelOf_le hK₁ hTH
  have hY₂ := (tc.symm hK₁).borelOf_le hK₂ hTH
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G,
      Y = oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := ⟨_, rfl⟩
  rw [← hYdef] at hB hY₁ hY₂
  have hYK : Y ≤ oTwoUpper H := by
    rw [hYdef]
    exact inf_le_left
  have hBY : B ≤ Y := hB.1
  have hBK : B ≤ oTwoUpper H := hBY.trans hYK
  have hBO : B ⊓ pCoreOf 2 H = ⊥ := by
    rw [inf_comm]
    exact Vol2.Ch11.SecS.inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hB.2.1
  have hHall : ∀ {Ki : Subgroup G}, Ki ≤ oTwoUpper H →
      oTwoUpper H ≤ Subgroup.normalizer (Ki : Set G) → borelOf Ki T ≤ Y →
      Lin2.IsHallTwoPrimeOf (B ⊓ Ki) (borelOf Ki T) := by
    intro Ki hKiK hKN hYi
    have h2 : Y ⊓ Ki = borelOf Ki T := by
      refine le_antisymm ?_ (le_inf hYi inf_le_left)
      rw [hYdef]
      exact inf_le_borelOf hKiK
    have hYN' : Y ≤ Subgroup.normalizer ((borelOf Ki T : Subgroup G) : Set G) := by
      intro y hy
      have h1 : y ∈ Subgroup.normalizer ((Y ⊓ Ki : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hKN (hYK hy)⟩
      rwa [h2] at h1
    have h := isHallTwoPrimeOf_inf_of_le_normalizer hB hYi hYN'
    have h3 : B ⊓ borelOf Ki T = B ⊓ Ki := by
      refine le_antisymm (inf_le_inf_left B inf_le_left) fun x hx => ⟨hx.1, ?_⟩
      rw [← h2]
      exact ⟨hBY hx.1, hx.2⟩
    rwa [h3] at h
  have hL₂ : LieModel (O2Q K₂) .PSL 2 2 n := by
    obtain ⟨t, -, hK₂eq⟩ := tc.conj
    let e₀ : ↥K₁ ≃* ↥K₂ := Vol2.Ch11.SecA.mapEquivOfEq (MulAut.conj t) hK₂eq.symm
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥K₁) (CFSG.pCore 2 ↥K₂) e₀
        (Vol2.Ch11.SecA.pCore_map_mulEquiv' 2 e₀)) hL
  have hc₁ : Nat.card ↥(B ⊓ K₁) = 2 ^ n - 1 :=
    (isCyclic_card_of_isHall_borelOf hn hL
      (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₁) hTH)
      (hHall hK₁K hKN₁ hY₁)).2
  have hc₂ : Nat.card ↥(B ⊓ K₂) = 2 ^ n - 1 :=
    (isCyclic_card_of_isHall_borelOf hn hL₂
      (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂) hTH)
      (hHall hK₂K hKN₂ hY₂)).2
  have hBB : (B ⊓ K₂) ⊓ (B ⊓ K₁) = ⊥ := by
    rw [eq_bot_iff, ← hBO]
    intro x hx
    exact ⟨hx.1.1, tc.inf_le_pCoreOf hK₁H ⟨hx.2.2, hx.1.2⟩⟩
  have hB₂N : B ⊓ K₂ ≤ Subgroup.normalizer ((B ⊓ K₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx.1, hKN₁ (hBK hx.1)⟩
  have hsq : Nat.card ↥((B ⊓ K₂) ⊔ (B ⊓ K₁)) = (2 ^ n - 1) ^ 2 := by
    have h := C5.card_sup_mul_card_inf_of_le_normalizer hB₂N
    rw [hBB, Subgroup.card_bot, mul_one, hc₁, hc₂] at h
    rw [h, sq]
  rw [← hsq]
  exact Subgroup.card_dvd_of_le (sup_le inf_le_left inf_le_left)

end TwoComp

end CFSG.Quasithin.H13
