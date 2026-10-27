module

public import CFSG.Walter.J1.HSeven
public import CFSG.Walter.J1.BenderLemma

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem eq_of_commute_three (Q : Sylow 2 G) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hx : orderOf x = 3) {s s' : G}
    (hsQ : s ∈ Q) (hs'Q : s' ∈ Q) (hs1 : s ≠ 1) (hs'1 : s' ≠ 1) (hsx : s * x = x * s)
    (hs'x : s' * x = x * s') : s = s' := by
  set K := (Q : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)
  have hK : Nat.card K = 2 := h.card_inf_centralizer_three Q hxN hx
  have hsK : s ∈ K := ⟨hsQ, Subgroup.mem_centralizer_singleton_iff.mpr hsx⟩
  have hs'K : s' ∈ K := ⟨hs'Q, Subgroup.mem_centralizer_singleton_iff.mpr hs'x⟩
  rw [eq_zpowers_of_card_prime Nat.prime_two hK hsK hs1] at hs'K
  have hs2 : orderOf s = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q hsQ, hs1⟩
  rcases (mem_zpowers_of_orderOf_eq_two hs2).mp hs'K with h1 | h1
  · exact absurd h1 hs'1
  · exact h1.symm

include h in
theorem exists_commute_three (Q : Sylow 2 G) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hx : orderOf x = 3) :
    ∃ s ∈ Q, s ≠ 1 ∧ s * x = x * s := by
  obtain ⟨s, hs, hs1⟩ := exists_ne_one_of_card (h.card_inf_centralizer_three Q hxN hx)
    (by norm_num)
  exact ⟨s, hs.1, hs1, Subgroup.mem_centralizer_singleton_iff.mp hs.2⟩

include h in
theorem ncard_orderOf_six_eq (Q : Sylow 2 G) :
    {x : G | x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf x = 6}.ncard =
      {x : G | x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf x = 3}.ncard := by
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have h4 : ∀ y : G, orderOf y = 6 → orderOf (y ^ 4) = 3 := by
    intro y hy
    rw [orderOf_pow' y (by norm_num), hy]
    norm_num
  have h3 : ∀ y : G, orderOf y = 6 → orderOf (y ^ 3) = 2 := by
    intro y hy
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hy]; norm_num), hy]
  have hy7 : ∀ y : G, orderOf y = 6 → y ^ 4 * y ^ 3 = y := by
    intro y hy
    rw [← pow_add, show 4 + 3 = 6 + 1 by norm_num, pow_succ, ← hy, pow_orderOf_eq_one, one_mul]
  refine Set.ncard_congr (fun y _ => y ^ 4) ?_ ?_ ?_
  · rintro y ⟨hyH, hy⟩
    exact ⟨H.pow_mem hyH 4, h4 y hy⟩
  · rintro y y' ⟨hyH, hy⟩ ⟨hy'H, hy'⟩ hyy'
    have hs : y ^ 3 = y' ^ 3 := by
      refine h.eq_of_commute_three Q (H.pow_mem hyH 4) (h4 y hy)
        (mem_sylow_of_orderOf_eq_two Q (H.pow_mem hyH 3) (h3 y hy))
        (mem_sylow_of_orderOf_eq_two Q (H.pow_mem hy'H 3) (h3 y' hy'))
        (orderOf_eq_two_iff.mp (h3 y hy)).2 (orderOf_eq_two_iff.mp (h3 y' hy')).2
        (by rw [← pow_add, ← pow_add, add_comm]) ?_
      rw [hyy', ← pow_add, ← pow_add, add_comm]
    rw [← hy7 y hy, ← hy7 y' hy', hyy', hs]
  · rintro x ⟨hxH, hx⟩
    obtain ⟨s, hsQ, hs1, hsx⟩ := h.exists_commute_three Q hxH hx
    have hs2 : orderOf s = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q hsQ, hs1⟩
    have hcomm : Commute x s := hsx.symm
    refine ⟨x * s, ⟨H.mul_mem hxH (Subgroup.le_normalizer hsQ), ?_⟩, ?_⟩
    · rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hs2]; norm_num), hx, hs2]
    · have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      have hs2' : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
      rw [hcomm.mul_pow, show x ^ 4 = x ^ 3 * x by rw [← pow_succ], hx3, one_mul,
        show s ^ 4 = (s ^ 2) ^ 2 by rw [← pow_mul], hs2', one_pow, mul_one]

include h in
theorem ncard_orderOf_three (Q : Sylow 2 G) :
    {x : G | x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf x = 3}.ncard = 56 := by
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have hsum := ncard_eq_sum_ncard_fiber (H : Set G) orderOf {1, 2, 3, 6, 7}
    (fun x hx => by
      rcases h.orderOf_mem_normalizer Q hx with h0 | h0 | h0 | h0 | h0 <;> simp [h0])
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  have h1 : {x | x ∈ (H : Set G) ∧ orderOf x = 1}.ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨1, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, orderOf_eq_one_iff, SetLike.mem_coe]
    constructor
    · exact fun hx => hx.2
    · rintro rfl
      exact ⟨H.one_mem, rfl⟩
  have h2 : {x | x ∈ (H : Set G) ∧ orderOf x = 2}.ncard = 7 := by
    rw [← h.ncard_involutions_normalizer Q]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    exact and_comm
  have h7 : {x | x ∈ (H : Set G) ∧ orderOf x = 7}.ncard = 48 := h.ncard_orderOf_seven Q
  have h6 := h.ncard_orderOf_six_eq Q
  have hH : (H : Set G).ncard = 168 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.card_normalizer_sylow'' Q]
  change {x | x ∈ (H : Set G) ∧ orderOf x = 6}.ncard =
    {x | x ∈ (H : Set G) ∧ orderOf x = 3}.ncard at h6
  change {x | x ∈ (H : Set G) ∧ orderOf x = 3}.ncard = 56
  omega

include h in
theorem ncard_orderOf_six (Q : Sylow 2 G) :
    {x : G | x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf x = 6}.ncard = 56 := by
  rw [h.ncard_orderOf_six_eq Q, h.ncard_orderOf_three Q]

end JankoHyp

end CFSG.Walter.J1
