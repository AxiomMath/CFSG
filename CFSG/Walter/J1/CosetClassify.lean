module

public import CFSG.Walter.J1.Coset
public import CFSG.Walter.J1.BenderLemma

public section

namespace CFSG.Walter.J1

section Defs

variable {G : Type*} [Group G]

@[expose] noncomputable def invOrd (H : Subgroup G) (u : G) (k : ℕ) : ℕ :=
  {d | d ∈ {d | d ∈ H ∧ u * d * u⁻¹ = d⁻¹} ∧ orderOf d = k}.ncard

@[expose] noncomputable def kap (H : Subgroup G) (u : G) : ℕ :=
  {x | x ∈ H ∧ orderOf x = 3 ∧ u * x = x * u}.ncard

theorem mem_zpowers_of_orderOf_eq_three {x z : G} (hx : orderOf x = 3)
    (hz : z ∈ Subgroup.zpowers x) : z = 1 ∨ z = x ∨ z = x⁻¹ := by
  have h3 : x ^ (3 : ℤ) = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    rw [zpow_ofNat, this]
  obtain ⟨k, rfl⟩ := hz
  have hk : k = 3 * (k / 3) + k % 3 := by omega
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  change x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x⁻¹
  rw [hk, zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rcases hmod with h0 | h0 | h0 <;> rw [h0]
  · left; exact zpow_zero x
  · right; left; exact zpow_one x
  · right; right
    rw [show (2 : ℤ) = 3 + -1 by norm_num, zpow_add, h3, one_mul, zpow_neg_one]

end Defs

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem ncard_inv_eq (Q : Sylow 2 G) (u : G) :
    {d | d ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ u * d * u⁻¹ = d⁻¹}.ncard =
      1 + invOrd (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u 2 +
        invOrd (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u 3 +
        invOrd (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u 6 +
        invOrd (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u 7 := by
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  set S := {d | d ∈ H ∧ u * d * u⁻¹ = d⁻¹}
  have hsum := ncard_eq_sum_ncard_fiber S orderOf {1, 2, 3, 6, 7}
    (fun x hx => by
      rcases h.orderOf_mem_normalizer Q hx.1 with h0 | h0 | h0 | h0 | h0 <;> simp [h0])
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  have h1 : {x | x ∈ S ∧ orderOf x = 1}.ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨1, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, orderOf_eq_one_iff, S]
    constructor
    · exact fun hx => hx.2
    · rintro rfl
      exact ⟨⟨H.one_mem, by simp⟩, rfl⟩
  rw [hsum, h1]
  simp only [invOrd]
  ring

include h in
theorem eq_or_eq_inv_of_three (Q : Sylow 2 G) {u : G}
    (huH : u ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (h7 : ∀ y ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u, orderOf y ≠ 7)
    {x x' : G} (hxD : x ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u)
    (hx'D : x' ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u)
    (hx : orderOf x = 3) (hx' : orderOf x' = 3) : x' = x ∨ x' = x⁻¹ := by
  set D := cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u
  by_cases hmem : x' ∈ Subgroup.zpowers x
  · rcases mem_zpowers_of_orderOf_eq_three hx hmem with h0 | h0 | h0
    · rw [h0, orderOf_one] at hx'
      omega
    · exact Or.inl h0
    · exact Or.inr h0
  · exfalso
    have h6 : Nat.card D ∣ 6 := h.card_cosetD_dvd_6 Q huH h7
    have hle := card_mul_card_le_of_inf_eq_bot (D := D) ((Subgroup.zpowers_le).mpr hxD)
      ((Subgroup.zpowers_le).mpr hx'D) (zpowers_inf_eq_bot Nat.prime_three hx' hmem)
    rw [Nat.card_zpowers, Nat.card_zpowers, hx, hx'] at hle
    have := Nat.le_of_dvd (by norm_num) h6
    omega

theorem pow_mem_inv {G : Type*} [Group G] {H : Subgroup G} {u d : G}
    (hd : d ∈ {d | d ∈ H ∧ u * d * u⁻¹ = d⁻¹}) (k : ℕ) :
    d ^ k ∈ {d | d ∈ H ∧ u * d * u⁻¹ = d⁻¹} := by
  refine ⟨H.pow_mem hd.1 k, ?_⟩
  rw [← conj_pow, hd.2, inv_pow]

include h in
theorem classify (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {u : G} (hu : orderOf u = 2)
    (huH : u ∉ H) :
    (invOrd H u 2 = 0 ∧ invOrd H u 3 = 0 ∧ invOrd H u 6 = 0 ∧ invOrd H u 7 = 0 ∧
      (kap H u = 0 ∨ kap H u = 2) ∧ (kap H u = 2 ↔ ∃ g ∈ H, g ≠ 1 ∧ g * u = u * g)) ∨
    (invOrd H u 2 = 1 ∧ invOrd H u 3 = 0 ∧ invOrd H u 6 = 0 ∧ invOrd H u 7 = 0 ∧
      kap H u ≤ 2) ∨
    (invOrd H u 2 = 0 ∧ invOrd H u 3 = 2 ∧ invOrd H u 6 = 0 ∧ invOrd H u 7 = 0 ∧
      kap H u = 0) ∨
    (invOrd H u 2 = 1 ∧ invOrd H u 3 = 2 ∧ invOrd H u 6 = 2 ∧ invOrd H u 7 = 0 ∧
      kap H u = 0) ∨
    (invOrd H u 2 = 0 ∧ invOrd H u 3 = 0 ∧ invOrd H u 6 = 0 ∧ invOrd H u 7 = 6) := by
  subst hH
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  set D := cosetD H u
  set S := {d | d ∈ H ∧ u * d * u⁻¹ = d⁻¹}
  have hu2 := (orderOf_eq_two_iff.mp hu).1
  have hSD : ∀ d ∈ S, d ∈ D := fun d hd => mem_cosetD.mpr ⟨hd.1, hd.2 ▸ H.inv_mem hd.1⟩
  have hinvS : ∀ k, invOrd H u k = {d | d ∈ S ∧ orderOf d = k}.ncard := fun k => rfl
  by_cases hA : ∃ y ∈ D, orderOf y = 7
  ·
    obtain ⟨y, hyD, hy⟩ := hA
    have hS : S = (Subgroup.zpowers y : Set G) := h.inv_set_eq_of_seven Q hu huH hyD hy
    have hord : ∀ d ∈ Subgroup.zpowers y, d = 1 ∨ orderOf d = 7 := by
      intro d hd
      have : orderOf d ∣ 7 := by
        have := Subgroup.orderOf_dvd_natCard _ hd
        rwa [Nat.card_zpowers, hy] at this
      rcases (Nat.dvd_prime (by norm_num)).mp this with h0 | h0
      · exact Or.inl (orderOf_eq_one_iff.mp h0)
      · exact Or.inr h0
    have hzero : ∀ k, k ≠ 1 → k ≠ 7 → invOrd H u k = 0 := by
      intro k hk1 hk7
      rw [hinvS, hS, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro d ⟨hd, hdk⟩
      rcases hord d hd with h0 | h0
      · rw [h0, orderOf_one] at hdk
        exact hk1 hdk.symm
      · exact hk7 (hdk.symm.trans h0)
    have h7' : invOrd H u 7 = 6 := by
      rw [hinvS, hS]
      have : {d | d ∈ (Subgroup.zpowers y : Set G) ∧ orderOf d = 7} =
          (Subgroup.zpowers y : Set G) \ {1} := by
        ext d
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
        constructor
        · rintro ⟨hd, hd7⟩
          refine ⟨hd, fun h1 => ?_⟩
          rw [h1, orderOf_one] at hd7
          omega
        · rintro ⟨hd, hd1⟩
          exact ⟨hd, (hord d hd).resolve_left hd1⟩
      rw [this, Set.ncard_sdiff_singleton_of_mem (by simp), ← Nat.card_coe_set_eq,
        SetLike.coe_sort_coe, Nat.card_zpowers, hy]
    right; right; right; right
    exact ⟨hzero 2 (by norm_num) (by norm_num), hzero 3 (by norm_num) (by norm_num),
      hzero 6 (by norm_num) (by norm_num), h7'⟩
  ·
    push Not at hA
    have hc7 : invOrd H u 7 = 0 := by
      rw [hinvS, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro d ⟨hd, hd7⟩
      exact hA d (hSD d hd) hd7
    have hinv2 : ∀ s ∈ D, ∀ s' ∈ D, orderOf s = 2 → orderOf s' = 2 → s = s' :=
      fun s hs s' hs' h2 h2' => h.eq_of_mem_cosetD Q huH hs hs' h2 h2'
    have hinv3 : ∀ x ∈ D, ∀ x' ∈ D, orderOf x = 3 → orderOf x' = 3 → x' = x ∨ x' = x⁻¹ :=
      fun x hx x' hx' h3 h3' => h.eq_or_eq_inv_of_three Q huH hA hx hx' h3 h3'
    have hinvmem : ∀ x ∈ S, x⁻¹ ∈ S := fun x hx =>
      ⟨H.inv_mem hx.1, by rw [show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group, hx.2]⟩
    have hx3ne : ∀ x : G, orderOf x = 3 → x ≠ x⁻¹ := by
      intro x hx h1
      have h2 : x * x = 1 := by
        calc x * x = x * x⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel x
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
      rw [hx] at this
      norm_num at this
    have hc2 : (∃ s ∈ S, orderOf s = 2) → invOrd H u 2 = 1 := by
      rintro ⟨s, hsS, hs⟩
      rw [hinvS, Set.ncard_eq_one]
      refine ⟨s, ?_⟩
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hd, hd2⟩
        exact hinv2 d (hSD d hd) s (hSD s hsS) hd2 hs
      · rintro rfl
        exact ⟨hsS, hs⟩
    have hc2' : (¬ ∃ s ∈ S, orderOf s = 2) → invOrd H u 2 = 0 := by
      intro hn
      rw [hinvS, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro d ⟨hd, hd2⟩
      exact hn ⟨d, hd, hd2⟩
    have hc3 : (∃ x ∈ S, orderOf x = 3) → invOrd H u 3 = 2 := by
      rintro ⟨x, hxS, hx⟩
      rw [hinvS]
      have : {d | d ∈ S ∧ orderOf d = 3} = {x, x⁻¹} := by
        ext d
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hd, hd3⟩
          exact hinv3 x (hSD x hxS) d (hSD d hd) hx hd3
        · rintro (rfl | rfl)
          · exact ⟨hxS, hx⟩
          · exact ⟨hinvmem x hxS, by rw [orderOf_inv, hx]⟩
      rw [this, Set.ncard_pair (hx3ne x hx)]
    have hc3' : (¬ ∃ x ∈ S, orderOf x = 3) → invOrd H u 3 = 0 := by
      intro hn
      rw [hinvS, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro d ⟨hd, hd3⟩
      exact hn ⟨d, hd, hd3⟩
    have h6pow : ∀ d ∈ S, orderOf d = 6 →
        (d ^ 3 ∈ S ∧ orderOf (d ^ 3) = 2) ∧ (d ^ 4 ∈ S ∧ orderOf (d ^ 4) = 3) := by
      intro d hd hd6
      refine ⟨⟨pow_mem_inv hd 3, ?_⟩, ⟨pow_mem_inv hd 4, ?_⟩⟩
      · rw [orderOf_pow_of_dvd (by norm_num) (by rw [hd6]; norm_num), hd6]
      · rw [orderOf_pow' d (by norm_num), hd6]
        norm_num
    have hc6 : (∃ s ∈ S, orderOf s = 2) → (∃ x ∈ S, orderOf x = 3) → invOrd H u 6 = 2 := by
      rintro ⟨s, hsS, hs⟩ ⟨x, hxS, hx⟩
      have hsx : x * s = s * x := by
        have h1 : x * s * x⁻¹ ∈ D := D.mul_mem (D.mul_mem (hSD x hxS) (hSD s hsS))
          (D.inv_mem (hSD x hxS))
        have h2 := hinv2 _ h1 s (hSD s hsS)
          (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]) hs
        calc x * s = x * s * x⁻¹ * x := by group
          _ = s * x := by rw [h2]
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (orderOf_eq_two_iff.mp hs).1
      have hmul : ∀ z ∈ S, orderOf z = 3 → z * s = s * z → z * s ∈ S ∧ orderOf (z * s) = 6 := by
        intro z hzS hz hzs
        refine ⟨⟨H.mul_mem hzS.1 hsS.1, ?_⟩, ?_⟩
        · rw [show u * (z * s) * u⁻¹ = (u * z * u⁻¹) * (u * s * u⁻¹) by group, hzS.2, hsS.2,
            hsinv, mul_inv_rev, hsinv]
          exact (Commute.inv_left (show Commute z s from hzs)).eq
        · rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime hzs (by rw [hz, hs]; norm_num)),
            hz, hs]
      have hxs' : x⁻¹ * s = s * x⁻¹ := by
        calc x⁻¹ * s = x⁻¹ * (s * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * s) * x⁻¹ := by rw [hsx]
          _ = s * x⁻¹ := by group
      rw [hinvS]
      have : {d | d ∈ S ∧ orderOf d = 6} = {x * s, x⁻¹ * s} := by
        ext d
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hd, hd6⟩
          obtain ⟨⟨hd3S, hd3⟩, ⟨hd4S, hd4⟩⟩ := h6pow d hd hd6
          have e3 : d ^ 3 = s := hinv2 _ (hSD _ hd3S) s (hSD s hsS) hd3 hs
          have e7 : d ^ 4 * d ^ 3 = d := by
            rw [← pow_add, show 4 + 3 = 6 + 1 by norm_num, pow_succ, ← hd6, pow_orderOf_eq_one,
              one_mul]
          rcases hinv3 x (hSD x hxS) _ (hSD _ hd4S) hx hd4 with e4 | e4
          · left; rw [← e7, e4, e3]
          · right; rw [← e7, e4, e3]
        · rintro (rfl | rfl)
          · exact hmul x hxS hx hsx
          · exact hmul x⁻¹ (hinvmem x hxS) (by rw [orderOf_inv, hx]) hxs'
      rw [this, Set.ncard_pair (fun h1 => hx3ne x hx (mul_right_cancel h1))]
    have hc6' : ¬ ((∃ s ∈ S, orderOf s = 2) ∧ (∃ x ∈ S, orderOf x = 3)) →
        invOrd H u 6 = 0 := by
      intro hn
      rw [hinvS, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro d ⟨hd, hd6⟩
      obtain ⟨⟨hd3S, hd3⟩, ⟨hd4S, hd4⟩⟩ := h6pow d hd hd6
      exact hn ⟨⟨_, hd3S, hd3⟩, ⟨_, hd4S, hd4⟩⟩
    set K := {x | x ∈ H ∧ orderOf x = 3 ∧ u * x = x * u}
    have hkapK : kap H u = K.ncard := rfl
    have hKD : ∀ x ∈ K, x ∈ D := fun x hx => mem_cosetD.mpr ⟨hx.1, by
      rw [hx.2.2, mul_inv_cancel_right]; exact hx.1⟩
    have hk3 : (∃ x ∈ S, orderOf x = 3) → kap H u = 0 := by
      rintro ⟨x, hxS, hx⟩
      rw [hkapK, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro x' ⟨hx'H, hx', hx'u⟩
      have hx'D : x' ∈ D := hKD x' ⟨hx'H, hx', hx'u⟩
      have hx'S : x' ∈ S := by
        rcases hinv3 x (hSD x hxS) x' hx'D hx hx' with rfl | rfl
        · exact hxS
        · exact hinvmem _ hxS
      apply hx3ne x' hx'
      have := hx'S.2
      rw [hx'u, mul_inv_cancel_right] at this
      exact this
    have hk02 : kap H u = 0 ∨ kap H u = 2 := by
      by_cases hK : ∃ x, x ∈ K
      · obtain ⟨x, hx⟩ := hK
        right
        rw [hkapK]
        have : K = {x, x⁻¹} := by
          ext x'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro hx'
            exact hinv3 x (hKD x hx) x' (hKD x' hx') hx.2.1 hx'.2.1
          · rintro (rfl | rfl)
            · exact hx
            · refine ⟨H.inv_mem hx.1, by rw [orderOf_inv, hx.2.1], ?_⟩
              calc u * x⁻¹ = (x * u⁻¹)⁻¹ := by group
                _ = (u⁻¹ * (u * x) * u⁻¹)⁻¹ := by group
                _ = (u⁻¹ * (x * u) * u⁻¹)⁻¹ := by rw [hx.2.2]
                _ = x⁻¹ * u := by group
        rw [this, Set.ncard_pair (hx3ne x hx.2.1)]
      · left
        push Not at hK
        rw [hkapK, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
        exact hK
    have hk1 : (¬ ∃ s ∈ S, orderOf s = 2) → (¬ ∃ x ∈ S, orderOf x = 3) →
        (kap H u = 2 ↔ ∃ g ∈ H, g ≠ 1 ∧ g * u = u * g) := by
      intro n2 _
      constructor
      · intro hk
        have : K.Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          intro h0
          rw [hkapK, h0, Set.ncard_empty] at hk
          omega
        obtain ⟨x, hxH, hx, hxu⟩ := this
        refine ⟨x, hxH, fun h1 => ?_, hxu.symm⟩
        rw [h1, orderOf_one] at hx
        omega
      · rintro ⟨g, hgH, hg1, hgu⟩
        have hgD : g ∈ D := mem_cosetD.mpr ⟨hgH, by rw [← hgu, mul_inv_cancel_right]; exact hgH⟩
        rcases h.orderOf_mem_normalizer Q hgH with h0 | h0 | h0 | h0 | h0
        · exact absurd (orderOf_eq_one_iff.mp h0) hg1
        · exfalso
          apply n2
          refine ⟨g, ⟨hgH, ?_⟩, h0⟩
          rw [← hgu, mul_inv_cancel_right, inv_eq_of_mul_eq_one_right
            (orderOf_eq_two_iff.mp h0).1]
        · have hgK : g ∈ K := ⟨hgH, h0, hgu.symm⟩
          rcases hk02 with hk | hk
          · exfalso
            rw [hkapK, Set.ncard_eq_zero (Set.toFinite _)] at hk
            rw [hk] at hgK
            exact hgK
          · exact hk
        · exfalso
          apply n2
          have hg3 : orderOf (g ^ 3) = 2 := by
            rw [orderOf_pow_of_dvd (by norm_num) (by rw [h0]; norm_num), h0]
          refine ⟨g ^ 3, ⟨H.pow_mem hgH 3, ?_⟩, hg3⟩
          rw [← conj_pow, ← hgu, mul_inv_cancel_right, inv_eq_of_mul_eq_one_right
            (orderOf_eq_two_iff.mp hg3).1]
        · exact absurd h0 (hA g hgD)
    by_cases e2 : ∃ s ∈ S, orderOf s = 2 <;> by_cases e3 : ∃ x ∈ S, orderOf x = 3
    · right; right; right; left
      exact ⟨hc2 e2, hc3 e3, hc6 e2 e3, hc7, hk3 e3⟩
    · right; left
      refine ⟨hc2 e2, hc3' e3, hc6' (fun h0 => e3 h0.2), hc7, ?_⟩
      rcases hk02 with hk | hk <;> omega
    · right; right; left
      exact ⟨hc2' e2, hc3 e3, hc6' (fun h0 => e2 h0.1), hc7, hk3 e3⟩
    · left
      exact ⟨hc2' e2, hc3' e3, hc6' (fun h0 => e2 h0.1), hc7, hk02, hk1 e2 e3⟩

end JankoHyp

end CFSG.Walter.J1
