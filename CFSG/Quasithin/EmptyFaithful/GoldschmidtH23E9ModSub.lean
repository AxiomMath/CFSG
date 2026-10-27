module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModRefl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModEps
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModFree

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

omit [Finite W] in
theorem trace_eq_one_of_free {ε : MulAut W} (hε3 : orderOf ε = 3)
    (hεf : ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w) (hεW : ∀ w ∈ S.W₂, ε w ∈ S.W₂) {u : W} (hu : u ∈ S.W₂) :
    u * ε u * ε (ε u) = 1 := by
  have hε3' : ε * (ε * ε) = 1 := by
    have := pow_orderOf_eq_one ε
    rwa [hε3, pow_three] at this
  have hεu : ε (ε (ε u)) = u := by
    have : (ε * (ε * ε)) u = u := by rw [hε3']; rfl
    exact this
  have hy : u * ε u * ε (ε u) ∈ S.W₂ :=
    S.W₂.mul_mem (S.W₂.mul_mem hu (hεW u hu)) (hεW _ (hεW u hu))
  by_contra hne
  apply hεf _ hy hne
  rw [map_mul, map_mul, hεu]
  ac_rfl

omit [Finite W] in
theorem part₂_mem {ε : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hε3 : orderOf ε = 3)
    (hε₁ : ∀ w ∈ S.W₁, ε w = w) (hεf : ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w)
    (hεW : ∀ w ∈ S.W₂, ε w ∈ S.W₂) {U : Subgroup W} (hU₂ : ∀ w ∈ U, ε w ∈ U) {u₁ u₂ : W}
    (hu₁ : u₁ ∈ S.W₁) (hu₂ : u₂ ∈ S.W₂) (hu : u₁ * u₂ ∈ U) : u₂ ∈ U := by
  have h1 : ε (u₁ * u₂) = u₁ * ε u₂ := by rw [map_mul, hε₁ u₁ hu₁]
  have h2 : ε (ε (u₁ * u₂)) = u₁ * ε (ε u₂) := by rw [h1, map_mul, hε₁ u₁ hu₁]
  have hmem : ε (u₁ * u₂) * ε (ε (u₁ * u₂)) ∈ U := U.mul_mem (hU₂ _ hu) (hU₂ _ (hU₂ _ hu))
  have h3 := S.trace_eq_one_of_free hε3 hεf hεW hu₂
  have hu₁sq : u₁ * u₁ = 1 := by rw [← pow_two]; exact hW u₁
  have h4 : ε (u₁ * u₂) * ε (ε (u₁ * u₂)) = u₂ := by
    rw [h2, h1]
    calc u₁ * ε u₂ * (u₁ * ε (ε u₂)) = (u₁ * u₁) * (ε u₂ * ε (ε u₂)) := by ac_rfl
      _ = ε u₂ * ε (ε u₂) := by rw [hu₁sq, one_mul]
      _ = u₂ := by
        have h5 : u₂ * (ε u₂ * ε (ε u₂)) = 1 := by rw [← mul_assoc]; exact h3
        rw [eq_inv_of_mul_eq_one_right h5, inv_eq_self_of_sq151b hW]
  rw [h4] at hmem
  exact hmem

theorem eq_vE_or_top (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {x₁ x₂ ε₂ t : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₂ : x₂ ∈ S.A₂) (hx₁2 : orderOf x₁ = 2) (hx₂2 : orderOf x₂ = 2)
    (hε₂ : orderOf ε₂ = 3 ∧ (∀ w ∈ S.W₁, ε₂ w = w) ∧ ∀ w ∈ S.W₂, w ≠ 1 → ε₂ w ≠ w)
    (hε₂W : ∀ w ∈ S.W₂, ε₂ w ∈ S.W₂) (ht : S.Swap₁₂ t) {U : Subgroup W}
    (hU : S.vEMod x₁ x₂ ≤ U) (hU₂ : ∀ w ∈ U, ε₂ w ∈ U) (hUt : ∀ w ∈ U, t w ∈ U) :
    U = S.vEMod x₁ x₂ ∨ U = ⊤ := by
  obtain ⟨hε3, hε₁, hεf⟩ := hε₂
  set L₁ : Subgroup W := S.W₁ ⊓ fixV (Subgroup.zpowers x₁) with hL₁
  set L₂ : Subgroup W := S.W₂ ⊓ fixV (Subgroup.zpowers x₂) with hL₂
  have hL₁4 : Nat.card L₁ = 4 := S.card_fix_reflection₁ hW hcard hx₁ hx₁2
  have hL₂4 : Nat.card L₂ = 4 := S.card_fix_reflection₂ hW hcard hx₂ hx₂2
  have hL₁U : L₁ ≤ U := (show L₁ ≤ S.vEMod x₁ x₂ from le_sup_left).trans hU
  have hL₂U : L₂ ≤ U := (show L₂ ≤ S.vEMod x₁ x₂ from le_sup_right).trans hU
  set U₁ : Subgroup W := U ⊓ S.W₁ with hU₁
  set U₂ : Subgroup W := U ⊓ S.W₂ with hU₂'
  have hdecomp : U = U₁ ⊔ U₂ := by
    refine le_antisymm (fun u hu => ?_) (sup_le inf_le_left inf_le_left)
    have hu' : u ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top u
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu'
    have hu₂U : u₂ ∈ U := S.part₂_mem hW hε3 hε₁ hεf hε₂W hU₂ hu₁ hu₂ hu
    have hu₁U : u₁ ∈ U := by
      have : u₁ = (u₁ * u₂) * u₂⁻¹ := by group
      rw [this]
      exact U.mul_mem hu (U.inv_mem hu₂U)
    exact Subgroup.mul_mem_sup ⟨hu₁U, hu₁⟩ ⟨hu₂U, hu₂⟩
  have hU₂W : U₂ ≤ S.W₂ := inf_le_right
  have hL₂U₂ : L₂ ≤ U₂ := le_inf hL₂U inf_le_left
  have hL₁U₁ : L₁ ≤ U₁ := le_inf hL₁U inf_le_left
  have hc4 : 4 ≤ Nat.card U₂ := hL₂4 ▸ Subgroup.card_le_of_le hL₂U₂
  have hc16 : Nat.card U₂ ≤ 16 := (S.card_W₂ hcard) ▸ Subgroup.card_le_of_le hU₂W
  have hpow : Nat.card U₂ = 2 ^ rk U₂ := card_eq_two_pow hW U₂
  have hε3' : ε₂ ^ 3 = 1 := by
    have := pow_orderOf_eq_one ε₂
    rwa [hε3] at this
  have hinvU₂ : ∀ w ∈ U₂, ε₂ w ∈ U₂ := fun w hw => ⟨hU₂ w hw.1, hε₂W w hw.2⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmod := card_modEq_card_inf_fixV151b (U := U₂) (Y := Subgroup.zpowers ε₂)
    (isPGroup_zpowers_of_pow_eq_one151b hε3') (invariant_zpowers151b hinvU₂)
  have hfix : Nat.card ↥(U₂ ⊓ fixV (Subgroup.zpowers ε₂)) = 1 := by
    apply Subgroup.card_eq_one.mpr
    rw [eq_bot_iff]
    rintro w ⟨hwU, hwf⟩
    by_contra hw1
    exact hεf w hwU.2 hw1 (mem_fixV_zpowers_iff.mp hwf)
  rw [hfix] at hmod
  have h4or16 : Nat.card U₂ = 4 ∨ Nat.card U₂ = 16 := by
    rw [hpow] at hc4 hc16 hmod ⊢
    generalize rk U₂ = r at hc4 hc16 hmod ⊢
    have hr4 : r ≤ 4 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_le.mp h)
      omega
    interval_cases r <;> first | omega | (exfalso; revert hmod; decide)
  have hcard₁₂ : Nat.card U₁ = Nat.card U₂ := by
    apply le_antisymm
    · exact Nat.card_le_card_of_injective
        (fun w : U₁ => (⟨t w.1, hUt _ w.2.1, ht.1 _ w.2.2⟩ : U₂))
        (fun a b h => Subtype.ext (t.injective (congrArg Subtype.val h)))
    · exact Nat.card_le_card_of_injective
        (fun w : U₂ => (⟨t w.1, hUt _ w.2.1, ht.2 _ w.2.2⟩ : U₁))
        (fun a b h => Subtype.ext (t.injective (congrArg Subtype.val h)))
  rcases h4or16 with h4 | h16
  · left
    have e₂ : L₂ = U₂ := Subgroup.eq_of_le_of_card_ge hL₂U₂ (by rw [h4, hL₂4])
    have e₁ : L₁ = U₁ := Subgroup.eq_of_le_of_card_ge hL₁U₁ (by rw [hcard₁₂, h4, hL₁4])
    calc U = U₁ ⊔ U₂ := hdecomp
      _ = L₁ ⊔ L₂ := by rw [← e₁, ← e₂]
      _ = S.vEMod x₁ x₂ := rfl
  · right
    have e₂ : U₂ = S.W₂ := Subgroup.eq_of_le_of_card_ge hU₂W (by rw [h16, S.card_W₂ hcard])
    have e₁ : U₁ = S.W₁ :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard₁₂, h16, S.card_W₁ hcard])
    calc U = U₁ ⊔ U₂ := hdecomp
      _ = S.W₁ ⊔ S.W₂ := by rw [e₁, e₂]
      _ = ⊤ := S.wsup

theorem exists_eps_with_stab (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hE9 : ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ ε : MulAut W, ε ∈ Mb ∧ orderOf ε = 3 ∧ (∀ w ∈ S.W₁, ε w = w) ∧ ε * S.a₂ = S.a₂ * ε ∧
      (∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w) ∧ S.Stab₁ ε ∧ S.Stab₂ ε := by
  obtain ⟨ε, h1, h2, h3, h4, h5⟩ := S.exists_eps hW hcard hnorm hτ hE9
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ S.W₁, z ≠ 1 := by
    by_contra hcon
    have hbot : S.W₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
      by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h6 := Subgroup.card_eq_one.mpr hbot
    have h7 := S.card_W₁ hcard
    omega
  have hs := S.stab_of_mem_of_fix₁ hW hnorm h1 ⟨z, hz, hz1, h3 z hz⟩
  exact ⟨ε, h1, h2, h3, h4, h5, hs.1, hs.2⟩

theorem exists_eps₁_with_stab (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hE9 : ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ ε : MulAut W, ε ∈ Mb ∧ orderOf ε = 3 ∧ (∀ w ∈ S.W₂, ε w = w) ∧ ε * S.a₁ = S.a₁ * ε ∧
      (∀ w ∈ S.W₁, w ≠ 1 → ε w ≠ w) ∧ S.Stab₁ ε ∧ S.Stab₂ ε := by
  obtain ⟨ε, h1, h2, h3, h4, h5⟩ := S.exists_eps₁ hW hcard hnorm hτ hE9
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ S.W₂, z ≠ 1 := by
    by_contra hcon
    have hbot : S.W₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
      by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h6 := Subgroup.card_eq_one.mpr hbot
    have h7 := S.card_W₂ hcard
    omega
  have hnorm' : ∀ g ∈ Mb, ∀ z ∈ S.swap.A₁ ⊔ S.swap.A₂,
      g * z * g⁻¹ ∈ S.swap.A₁ ⊔ S.swap.A₂ := by
    intro g hg z hz
    have hz' : z ∈ S.A₁ ⊔ S.A₂ := by
      rwa [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl, sup_comm] at hz
    have := hnorm g hg z hz'
    rwa [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl, sup_comm]
  have hs := S.swap.stab_of_mem_of_fix₁ hW hnorm' h1 ⟨z, hz, hz1, h3 z hz⟩
  exact ⟨ε, h1, h2, h3, h4, h5, hs.2, hs.1⟩

end CFSG.Quasithin.SixData151b
