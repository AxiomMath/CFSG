module

public import CFSG.Walter.J1.Coprime

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem mul_self_of_mem_sylow' (Q : Sylow 2 G) {x : G} (hx : x ∈ Q) : x * x = 1 := by
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hx⟩
  exact h.sq_eq_one_of_pow (n := k) (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem mem_sylow_of_mem_normalizer {G : Type*} [Group G] (Q : Sylow 2 G) {x : G}
    (hx : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hR := IsPGroup.to_sup_of_normal_left' Q.isPGroup' hZ ((Subgroup.zpowers_le).mpr hx)
  have heq := Q.is_maximal' hR le_sup_left
  change x ∈ (Q : Subgroup G)
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem mem_sylow_of_orderOf_eq_two {G : Type*} [Group G] (Q : Sylow 2 G) {x : G}
    (hx : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hx2 : orderOf x = 2) :
    x ∈ Q :=
  mem_sylow_of_mem_normalizer Q hx (k := 1) (by rw [pow_one, ← hx2, pow_orderOf_eq_one])

include h in
theorem mem_sylow_of_commute_four (Q : Sylow 2 G) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {g : G} (hga : g * a = a * g)
    (hgb : g * b = b * g) : g ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : orderOf a = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q ha, ha1⟩
  have hb2 : orderOf b = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q hb, hb1⟩
  have hQab := h.abelian_sylow Q
  have hcab : a * b = b * a :=
    congrArg Subtype.val (hQab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set K := Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
  have hK : IsPGroup 2 K := by
    intro y
    obtain ⟨i, m, hm, hy⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf y)
      (orderOf_pos y).ne'
    set w := (y : G) ^ 2 ^ i
    have hwa : w * a = a * w :=
      (Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp y.2.1) _).eq
    have hwb : w * b = b * w :=
      (Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp y.2.2) _).eq
    have hwm : w ^ m = 1 := by
      rw [← pow_mul, ← hy, ← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    have hwodd : Odd (orderOf w) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hwm)
    have hw1 := h.eq_one_of_commute_four ha2 hb2 hab hcab hwodd hwa hwb
    exact ⟨i, Subtype.ext (by simpa [w] using hw1)⟩
  have hQK : (Q : Subgroup G) ≤ K := fun q hq =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hQab.is_comm.comm ⟨q, hq⟩ ⟨a, ha⟩)),
     Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hQab.is_comm.comm ⟨q, hq⟩ ⟨b, hb⟩))⟩
  have hKQ : K = Q := Q.is_maximal' hK hQK
  change g ∈ (Q : Subgroup G)
  rw [← hKQ]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hga,
    Subgroup.mem_centralizer_singleton_iff.mpr hgb⟩

include h in
theorem card_normalizer_sylow'' (Q : Sylow 2 G) :
    Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 168 := by
  obtain ⟨a, haQ, -, -, ha, -⟩ := h.exists_four_of_sylow Q
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq ha
  exact (h.conj g).card_normalizer_sylow Q (hg ▸ haQ)

include h in
theorem not_four_dvd_orderOf (g : G) : ¬ 4 ∣ orderOf g := by
  intro h4
  have hz := orderOf_pow_orderOf_div (orderOf_pos g).ne' h4
  set z := g ^ (orderOf g / 4)
  have h2 : z * z = 1 := h.sq_eq_one_of_pow (n := 2) (by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hz]; exact pow_orderOf_eq_one z)
  have : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rw [hz] at this
  norm_num at this

include h in
theorem not_seven_mul_dvd_orderOf {q : ℕ} (hq : q = 2 ∨ q = 3) (g : G) :
    ¬ 7 * q ∣ orderOf g := by
  intro h7
  have hq0 : q ≠ 0 := by rcases hq with rfl | rfl <;> norm_num
  have hz := orderOf_pow_orderOf_div (orderOf_pos g).ne' h7
  set z := g ^ (orderOf g / (7 * q))
  have h1 : orderOf (z ^ 7) = q := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hz]; exact Dvd.intro q rfl), hz]
    exact Nat.mul_div_cancel_left q (by norm_num)
  have h2 : orderOf (z ^ q) = 7 := by
    rw [orderOf_pow_of_dvd hq0 (by rw [hz]; exact Dvd.intro_left 7 rfl), hz]
    exact Nat.mul_div_cancel 7 (Nat.pos_of_ne_zero hq0)
  have h3 : z ^ q = 1 := h.eq_one_of_coprime_of_commute (x := z ^ 7)
    (by rw [h2]; norm_num) (by rcases hq with rfl | rfl <;> simp [h1])
    (by rw [← pow_add, ← pow_add, add_comm])
  rw [h3, orderOf_one] at h2
  omega

include h in
theorem orderOf_mem_normalizer (Q : Sylow 2 G) {x : G}
    (hx : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 6 ∨ orderOf x = 7 := by
  have hdvd : orderOf x ∣ 168 := by
    rw [← h.card_normalizer_sylow'' Q, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have h4 := h.not_four_dvd_orderOf x
  have h14 := h.not_seven_mul_dvd_orderOf (Or.inl rfl) x
  have h21 := h.not_seven_mul_dvd_orderOf (Or.inr rfl) x
  have hmem : orderOf x ∈ Nat.divisors 168 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have : Nat.divisors 168 = {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by
    decide
  rw [this] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 |
    h0 <;> rw [h0] at h4 h14 h21 ⊢ <;> omega

include h in
theorem centralizer_sylow'' (Q : Sylow 2 G) :
    Subgroup.centralizer ((Q : Subgroup G) : Set G) = Q := by
  obtain ⟨a, haQ, -, -, ha, -⟩ := h.exists_four_of_sylow Q
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq ha
  exact (h.conj g).centralizer_sylow Q (hg ▸ haQ)

include h in
theorem card_inf_centralizer_three (Q : Sylow 2 G) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hx : orderOf x = 3) :
    Nat.card ((Q : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 2 := by
  set V := Subgroup.zpowers x
  have hVN : V ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := (Subgroup.zpowers_le).mpr hxN
  let := conjAct V Q hVN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV3 : IsPGroup 3 V := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hmod := hV3.card_modEq_card_fixedPoints Q
  have hfix := card_fixedPointSubgroup_conjAct_top V Q hVN
  rw [inf_centralizer_zpowers] at hfix
  change Nat.card (MulAction.fixedPoints V Q) = _ at hfix
  rw [hfix, h.card_sylow' Q] at hmod
  set K := (Q : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)
  have hdvd : Nat.card K ∣ 8 := by
    rw [← h.card_sylow' Q]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne8 : Nat.card K ≠ 8 := by
    intro h8
    have heq : K = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.card_sylow' Q])
    obtain ⟨a, haQ, b, hbQ, ha, hb, hab, -⟩ := h.exists_four_of_sylow Q
    have hxa : x * a = a * x := by
      have : a ∈ K := heq ▸ haQ
      exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
    have hxb : x * b = b * x := by
      have : b ∈ K := heq ▸ hbQ
      exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
    have hxQ := h.mem_sylow_of_commute_four Q haQ hbQ (orderOf_eq_two_iff.mp ha).2
      (orderOf_eq_two_iff.mp hb).2 hab hxa hxb
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.mul_self_of_mem_sylow' Q hxQ)
    rw [hx] at h2
    norm_num at h2
  have hmem : Nat.card K ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [this] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  unfold Nat.ModEq at hmod
  rcases hmem with h0 | h0 | h0 | h0 <;> rw [h0] at hmod ⊢ <;> omega

include h in
theorem involutions_normalizer_eq (Q : Sylow 2 G) :
    {u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)} =
      ((Q : Subgroup G) : Set G) \ {1} := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hu, huN⟩
    exact ⟨mem_sylow_of_orderOf_eq_two Q huN hu, (orderOf_eq_two_iff.mp hu).2⟩
  · rintro ⟨huQ, hu1⟩
    exact ⟨orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q huQ, hu1⟩,
      Subgroup.le_normalizer huQ⟩

include h in
theorem ncard_involutions_normalizer (Q : Sylow 2 G) :
    {u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)}.ncard = 7 := by
  rw [h.involutions_normalizer_eq Q, Set.ncard_sdiff_singleton_of_mem (by simp),
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.card_sylow' Q]

end JankoHyp

end CFSG.Walter.J1
