module

public import CFSG.Timmesfeld.Bridge.Asc73Central
public import CFSG.Timmesfeld.Bridge.InvolutionSet

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

@[expose] def Asc73For (G : Type*) [Group G] : Prop :=
  ∀ (D : Set G) (hN : IsNormalSet D), IsInvolutionSet D → Subgroup.closure D = ⊤ →
    Moufang.NoPolar D → Disconnected D →
      ∀ d ∈ D, BenderSuzuki.IsStronglyEmbeddedOrder (compStab hN d)

variable {G : Type} [Group G] {D : Set G}

theorem mem_zpowers_of_mul_self {x y : G} (hx : x * x = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, hx, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem not_mem_of_mem_center (hdisc : Disconnected D) {x : G} (hxc : x ∈ Subgroup.center G) :
    x ∉ D := by
  intro hxD
  obtain ⟨a, ha, b, hb, hab⟩ := hdisc
  have hx : ∀ y ∈ D, Reach D x y := fun y hy =>
    reach_of_commute hxD hy (Subgroup.mem_center_iff.1 hxc y).symm
  exact hab (reach_trans (reach_symm (hx a ha)) (hx b hb))

section Lift

variable {Q : Type*} [Group Q] (φ : G →* Q) {x : G}

theorem commute_of_commute_map (hN : IsNormalSet D) (hD : IsInvolutionSet D)
    (hnp : Moufang.NoPolar D) (hker : ∀ g, φ g = 1 → g = 1 ∨ g = x) (hxx : x * x = 1)
    (hx1 : x ≠ 1) (hxD : x ∉ D) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (h : Commute (φ a) (φ b)) : Commute a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : φ ((a * b)⁻¹ * (b * a)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, h.eq, inv_mul_cancel]
  rcases hker _ h1 with h2 | h2
  · exact inv_mul_eq_one.1 h2
  · exfalso
    apply hxD
    have hba : (b * a) ^ 2 = x := by
      calc (b * a) ^ 2 = b⁻¹ * a⁻¹ * (b * a) := by
            rw [pow_two, hD.inv_eq ha, hD.inv_eq hb]
        _ = (a * b)⁻¹ * (b * a) := by rw [mul_inv_rev]
        _ = x := h2
    have hnot : ¬ (b * a) ^ 2 ^ 1 = 1 := by
      rw [pow_one, hba]
      exact hx1
    have hfin : (b * a) ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hba, pow_two, hxx]
    have h4 : orderOf (b * a) = 2 + 2 := by simpa using orderOf_eq_prime_pow hnot hfin
    exact hba ▸ pow_half_mem hN hD hnp hb ha h4 two_ne_zero

theorem eq_of_map_eq (hD : IsInvolutionSet D) (hnp : Moufang.NoPolar D)
    (hker : ∀ g, φ g = 1 → g = 1 ∨ g = x) (hxc : x ∈ Subgroup.center G) (hx1 : x ≠ 1)
    (hxD : x ∉ D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (h : φ a = φ b) : a = b := by
  have h1 : φ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases hker _ h1 with h2 | h2
  · exact inv_mul_eq_one.1 h2
  · exfalso
    have hb' : b = a * x := by rw [← h2, mul_inv_cancel_left]
    have hcomm : Commute a b := by
      rw [hb']
      exact (Commute.refl a).mul_right (Subgroup.mem_center_iff.1 hxc a)
    have hne : a ≠ b := fun h' => hx1 (by
      rw [h', hb'] at h2
      simpa using h2.symm)
    have := hnp a ha b hb hcomm hne
    rw [hb', ← mul_assoc, hD.mul_self_eq_one ha, one_mul] at this
    exact hxD this

theorem reach_of_reach_map (hN : IsNormalSet D) (hD : IsInvolutionSet D) (hnp : Moufang.NoPolar D)
    (hker : ∀ g, φ g = 1 → g = 1 ∨ g = x) (hxc : x ∈ Subgroup.center G) (hxx : x * x = 1)
    (hx1 : x ≠ 1) (hxD : x ∉ D) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (h : Reach (φ '' D) (φ a) (φ b)) : Reach D a b := by
  suffices key : ∀ y, Reach (φ '' D) (φ a) y → ∀ c ∈ D, φ c = y → Reach D a c from
    key _ h b hb rfl
  intro y hy
  induction hy with
  | refl =>
    intro c hc hca
    rw [← eq_of_map_eq φ hD hnp hker hxc hx1 hxD ha hc hca.symm]
    exact reach_refl a
  | tail _ hbc ih =>
    intro c hc hcy
    obtain ⟨⟨e, he, rfl⟩, -, hcomm⟩ := hbc
    refine reach_trans (ih e he rfl) (reach_of_commute he hc ?_)
    refine commute_of_commute_map φ hN hD hnp hker hxx hx1 hxD he hc ?_
    rw [hcy]
    exact hcomm

theorem noPolar_image (hN : IsNormalSet D) (hD : IsInvolutionSet D) (hnp : Moufang.NoPolar D)
    (hker : ∀ g, φ g = 1 → g = 1 ∨ g = x) (hxx : x * x = 1) (hx1 : x ≠ 1) (hxD : x ∉ D) :
    Moufang.NoPolar (φ '' D) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hcomm hne
  refine ⟨a * b, hnp a ha b hb (commute_of_commute_map φ hN hD hnp hker hxx hx1 hxD ha hb hcomm)
    (fun h => hne (by rw [h])), map_mul φ a b⟩

end Lift

theorem false_of_mem_center (hS : SchurNarrowInput) [Finite G] (hN : IsNormalSet D)
    (hD : IsInvolutionSet D) (hgen : Subgroup.closure D = ⊤) (hnp : Moufang.NoPolar D)
    (hdisc : Disconnected D) {u v : G} (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v)
    (hc : Commute u v)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card G → Asc73For Y) {x : G}
    (hxc : x ∈ Subgroup.center G) (hx2 : orderOf x = 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx2
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hxD : x ∉ D := not_mem_of_mem_center hdisc hxc
  have hK : (Subgroup.zpowers x).Normal := zpowers_normal_of_mem_center hxc
  set φ : G →* G ⧸ Subgroup.zpowers x := QuotientGroup.mk' (Subgroup.zpowers x) with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hkerφ : ∀ g, φ g = 1 ↔ g ∈ Subgroup.zpowers x := fun g => QuotientGroup.eq_one_iff g
  have hker : ∀ g, φ g = 1 → g = 1 ∨ g = x := fun g h =>
    (mem_zpowers_of_mul_self hxx).1 ((hkerφ g).1 h)
  have hφ1 : ∀ d ∈ D, φ d ≠ 1 := fun d hd h1 => by
    rcases hker d h1 with h | h
    · exact hD.ne_one hd h
    · exact hxD (h ▸ hd)
  have hNQ := isNormalSet_image hN φ hsurj
  have hDQ := isInvolutionSet_image hD φ hφ1
  have hgenQ := closure_image_eq_top hgen φ hsurj
  have hnpQ := noPolar_image φ hN hD hnp hker hxx hx1 hxD
  have hdiscQ : Disconnected (φ '' D) := by
    obtain ⟨a, ha, b, hb, hab⟩ := hdisc
    exact ⟨φ a, ⟨a, ha, rfl⟩, φ b, ⟨b, hb, rfl⟩,
      fun h => hab (reach_of_reach_map φ hN hD hnp hker hxc hxx hx1 hxD ha hb h)⟩
  have hcard : Nat.card (G ⧸ Subgroup.zpowers x) < Nat.card G := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers x)
    rw [Nat.card_zpowers, hx2] at h1
    have h2 : 0 < Nat.card (G ⧸ Subgroup.zpowers x) := Nat.card_pos
    omega
  have hSE := (fusionStronglyEmbedded_iff _).2
    (hIH _ hcard (φ '' D) hNQ hDQ hgenQ hnpQ hdiscQ (φ u) ⟨u, hu, rfl⟩)
  have hlift : ∀ s : G, orderOf (φ s) = 2 → ∃ c ∈ D, s = c ∨ s = c * x := by
    intro s hs
    have hu2 : orderOf (φ u) = 2 := hDQ.orderOf_eq_two ⟨u, hu, rfl⟩
    obtain ⟨q, hq⟩ := isConj_iff.1 (isConj_of_orderOf_eq_two hSE hu2 hs)
    obtain ⟨g, rfl⟩ := hsurj q
    refine ⟨g * u * g⁻¹, hN g u hu, ?_⟩
    have h1 : φ ((g * u * g⁻¹)⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hq, inv_mul_cancel]
    rcases hker _ h1 with h | h
    · exact Or.inl (inv_mul_eq_one.1 h).symm
    · exact Or.inr (by rw [← h, mul_inv_cancel_left])
  have hrank : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo (G ⧸ Subgroup.zpowers x) := by
    refine twoRankAtLeastTwo_of_commute (a := φ u) (b := φ v) ?_ ?_ (hc.map φ) (hφ1 u hu)
      (hφ1 v hv) (fun h => huv (eq_of_map_eq φ hD hnp hker hxc hx1 hxD hu hv h))
    · rw [← map_mul, hD.mul_self_eq_one hu, map_one]
    · rw [← map_mul, hD.mul_self_eq_one hv, map_one]
  obtain ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hB⟩ := exists_bender_series hSE hrank
  have hxG : x ∈ commutator G := by
    have hodd := oddAcross_of_noPolar hN hD hnp
    rw [commutator_eq_top_of_mul_mem hgen
      (fun a ha b hb => isConj_of_disconnected_of_odd hD hodd hdisc ha hb)
      hu hv (hnp u hu v hv hc huv)]
    trivial
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | hSzU
  ·
    have hsq : ∀ s : G, ∀ n : ℕ, s ^ 2 ^ n = 1 → s * s = 1 := by
      intro s n hn
      have h1 : φ s ^ 2 = 1 :=
        sq_eq_one_of_bender_psl2 hModd hNodd hf e (by rw [← map_pow, hn, map_one])
      by_cases hs1 : φ s = 1
      · rcases hker s hs1 with rfl | rfl
        · exact one_mul 1
        · exact hxx
      · obtain ⟨c, hc, rfl | rfl⟩ := hlift s (orderOf_eq_prime h1 hs1)
        · exact hD.mul_self_eq_one hc
        · have hcx : Commute c x := Subgroup.mem_center_iff.1 hxc c
          rw [← pow_two, hcx.mul_pow, pow_two, pow_two, hD.mul_self_eq_one hc, hxx, one_mul]
    obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
    have hS2 : ∀ y ∈ (S : Subgroup G), y * y = 1 := by
      intro y hy
      obtain ⟨n, hn⟩ := S.isPGroup' ⟨y, hy⟩
      exact hsq y n (by simpa using congrArg Subtype.val hn)
    refine not_mem_commutator_of_sylow_commute hxc hx2 S (fun a ha b hb => ?_) hxG
    exact (commute_iff_mul_sq_eq_one (hS2 a ha) (hS2 b hb)).2
      (by rw [pow_two]; exact hS2 _ ((S : Subgroup G).mul_mem ha hb))
  ·
    obtain ⟨w, hw2, hwK, hwc⟩ := hS G x hK hxc hx2 hxG M N hMn hNn hMNn hMN hModd hNodd hSzU
    have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
    have hw1 : φ w ≠ 1 := fun h => hwK ((hkerφ w).1 h)
    have hwsq : φ w ^ 2 = 1 := by rw [← map_pow, pow_two, hww, map_one]
    obtain ⟨c, hcD, hwc'⟩ := hlift w (orderOf_eq_prime hwsq hw1)
    obtain ⟨g, hg⟩ := isConj_iff.1 hwc
    have hfw : w ∈ D → w * x ∈ D := fun h => hg ▸ hN g w h
    have hbw : w * x ∈ D → w ∈ D := fun h => by
      have := hN g⁻¹ (w * x) h
      rwa [← hg, show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this
    have hwD : w ∈ D := by
      rcases hwc' with rfl | rfl
      · exact hcD
      · exact hbw (by rw [mul_assoc, hxx, mul_one]; exact hcD)
    have hcomm : Commute w (w * x) := (Commute.refl w).mul_right (Subgroup.mem_center_iff.1 hxc w)
    have hne : w ≠ w * x := fun h => hx1 (by simpa using h.symm)
    have := hnp w hwD (w * x) (hfw hwD) hcomm hne
    rw [← mul_assoc, hww, one_mul] at this
    exact hxD this

end CFSG.Timmesfeld.Bridge
