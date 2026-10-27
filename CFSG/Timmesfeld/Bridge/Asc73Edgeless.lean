module

public import CFSG.Timmesfeld.Bridge.InvolutionSet

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem eq_of_reach_of_edgeless (hedge : ∀ x ∈ D, ∀ y ∈ D, Commute x y → x = y) {a b : G}
    (h : Reach D a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hedge _ hbc.1 _ hbc.2.1 hbc.2.2)

theorem card_le_two_of_isPGroup [Finite G] {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    {z : G} (hz2 : z * z = 1) (htop : N ⊔ Subgroup.zpowers z = ⊤) {P : Subgroup G}
    (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : P ⊓ N = ⊥ := by
    apply disjoint_iff.1
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hN)
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := by
    intro p q hpq
    have h1 : ((p : G))⁻¹ * q ∈ N := by
      simpa [QuotientGroup.eq] using hpq
    have h2 : ((p : G))⁻¹ * q ∈ P ⊓ N := Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem p.2) q.2, h1⟩
    rw [hPN, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  have hle := Nat.card_le_card_of_injective _ hinj
  have hQ : (⊤ : Subgroup (G ⧸ N)) = Subgroup.zpowers (QuotientGroup.mk' N z) := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) htop
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    have h2 : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨n, hn, rfl⟩
      exact (QuotientGroup.eq_one_iff n).2 hn
    rw [h2, bot_sup_eq] at h1
    exact h1.symm
  have hcardQ : Nat.card (G ⧸ N) ≤ 2 := by
    rw [← Subgroup.card_top, hQ, Nat.card_zpowers]
    refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, pow_two, hz2, map_one]
  exact hle.trans hcardQ

theorem isStronglyEmbeddedOrder_of_edgeless [Finite G] (hN : IsNormalSet D)
    (hD : IsInvolutionSet D) (hodd : OddAcross D) (hgen : Subgroup.closure D = ⊤)
    (hdisc : Disconnected D)
    (hedge : ∀ x ∈ D, ∀ y ∈ D, Commute x y → x = y) {z : G} (hz : z ∈ D) :
    BenderSuzuki.IsStronglyEmbeddedOrder (compStab hN z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype G := Fintype.ofFinite G
  have hz2 := hD.mul_self_eq_one hz
  have hiso : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z :=
    fun g hg => hedge _ (hN g z hz) _ hz hg
  obtain ⟨N, hNn, hNodd, hNz⟩ := CFSG.ZStar.glauberman_zStar G z (hD.ne_one hz) hz2 hiso
  have htop : N ⊔ Subgroup.zpowers z = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro d hd
    obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_disconnected_of_odd hD hodd hdisc hz hd)
    have : g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
    rw [SetLike.mem_coe, this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hNz g))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have huniq : ∀ t : G, orderOf t = 2 → Commute t z → t = z := by
    intro t ht htz
    by_contra hne
    have ht2 := (commute_iff_mul_sq_eq_one (by rw [← pow_two, ← ht, pow_orderOf_eq_one]) hz2).1
      htz
    have hP2 : IsPGroup 2 (Subgroup.closure ({t, z} : Set G)) :=
      isPGroup_two_closure_pair (by rw [← pow_two, ← ht, pow_orderOf_eq_one]) hz2
        (by rw [pow_one]; exact ht2)
    have hcard := card_le_two_of_isPGroup hNodd hz2 htop hP2
    have hlt : Subgroup.zpowers t < Subgroup.closure ({t, z} : Set G) := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · intro heq
        have hzt : z ∈ Subgroup.zpowers t := by
          rw [heq]; exact Subgroup.subset_closure (by simp)
        have hfin : IsOfFinOrder t := orderOf_pos_iff.1 (by rw [ht]; norm_num)
        rw [hfin.mem_zpowers_iff_mem_range_orderOf, ht] at hzt
        obtain ⟨k, hk, hkz⟩ := Finset.mem_image.1 hzt
        rw [Finset.mem_range] at hk
        interval_cases k
        · exact hD.ne_one hz (by simpa using hkz.symm)
        · exact hne (by simpa using hkz)
    have hc := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, ht] at hc
    omega
  have hstab : ∀ g : G, g ∈ compStab hN z ↔ g * z * g⁻¹ = z := by
    intro g
    rw [mem_compStab_iff]
    exact ⟨fun h => (eq_of_reach_of_edgeless hedge h).symm, fun h => by rw [h]; exact reach_refl z⟩
  refine ⟨compStab_ne_top_of_odd hN hD hodd hdisc hz, ?_, fun g hg => ?_⟩
  · exact even_iff_two_dvd.2 (by
      rw [← hD.orderOf_eq_two hz]
      exact Subgroup.orderOf_dvd_natCard _ (mem_compStab_self hN z))
  by_contra hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (Nat.not_odd_iff_even.1 hodd).two_dvd
  have ht2 : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨ht1, s, hs, hst⟩ := Subgroup.mem_inf.1 t.2
  have hcomm : ∀ u : G, u ∈ compStab hN z → Commute u z := fun u hu => by
    have := (hstab u).1 hu
    show u * z = z * u
    calc u * z = u * z * u⁻¹ * u := by group
      _ = z * u := by rw [this]
  have htz : (t : G) = z := huniq _ ht2 (hcomm _ ht1)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hst
  have hs2 : orderOf s = 2 := by
    rw [← ht2, ← hst, orderOf_conj_eq]
  have hsz : s = z := huniq s hs2 (hcomm s hs)
  apply hg
  rw [hstab, ← hsz, hst, htz]
  rw [hsz]

end CFSG.Timmesfeld.Bridge
