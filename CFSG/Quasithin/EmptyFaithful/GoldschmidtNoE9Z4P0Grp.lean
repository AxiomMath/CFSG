module

public import CFSG.Quasithin.EmptyFaithful.S14612GA2

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

omit [Finite V] in
theorem P_le_X (h : E9Z4Str X Tb P) : P ≤ X := by
  rw [h.eq]
  exact le_sup_left

omit [Finite V] in
theorem Tb_le_X (h : E9Z4Str X Tb P) : Tb ≤ X := by
  rw [h.eq]
  exact le_sup_right

omit [Finite V] in
theorem P_inf_Tb (h : E9Z4Str X Tb P) : P ⊓ Tb = ⊥ := by
  have h1 : Nat.card ↥(P ⊓ Tb) ∣ 9 := h.card_P ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(P ⊓ Tb) ∣ 4 := h.card_Tb ▸ Subgroup.card_dvd_of_le inf_le_right
  exact Subgroup.card_eq_one.mp (by simpa using Nat.dvd_gcd h1 h2)

omit [Finite V] in
theorem Tb_le_normalizer (h : E9Z4Str X Tb P) : Tb ≤ Subgroup.normalizer (P : Set (MulAut V)) :=
  fun _ hs => h.normalP.le_normalizer (h.Tb_le_X hs)

omit [Finite V] in
theorem conj_mem (h : E9Z4Str X Tb P) {s a : MulAut V} (hs : s ∈ Tb) (ha : a ∈ P) :
    s * a * s⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp (h.Tb_le_normalizer hs) a).mp ha

omit [Finite V] in
theorem exists_mul (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X) :
    ∃ a ∈ P, ∃ s ∈ Tb, x = a * s := by
  have hxmem : x ∈ ((P ⊔ Tb : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← h.eq]
    exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Tb h.Tb_le_normalizer] at hxmem
  obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hxmem
  exact ⟨a, ha, s, hs, rfl⟩

theorem eq_of_orderOf_eq_two (h : E9Z4Str X Tb P) {s t : MulAut V} (hs : s ∈ Tb) (ht : t ∈ Tb)
    (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) : s = t := by
  have : Fintype ↥Tb := Fintype.ofFinite _
  have hcyc := h.cyclic_Tb
  have hcard : Fintype.card ↥Tb = 4 := by rw [← Nat.card_eq_fintype_card]; exact h.card_Tb
  have hS := IsCyclic.card_orderOf_eq_totient (α := ↥Tb) (d := 2) (by rw [hcard]; norm_num)
  rw [Nat.totient_two] at hS
  have hsmem : (⟨s, hs⟩ : ↥Tb) ∈ (Finset.univ.filter fun a : ↥Tb => orderOf a = 2) := by
    simpa [Subgroup.orderOf_mk] using hs2
  have htmem : (⟨t, ht⟩ : ↥Tb) ∈ (Finset.univ.filter fun a : ↥Tb => orderOf a = 2) := by
    simpa [Subgroup.orderOf_mk] using ht2
  exact congrArg Subtype.val (Finset.card_le_one.mp hS.le _ hsmem _ htmem)

omit [Finite V] in
theorem orderOf_Tb (h : E9Z4Str X Tb P) {s : MulAut V} (hs : s ∈ Tb) :
    orderOf s = 1 ∨ orderOf s = 2 ∨ orderOf s = 4 := by
  have hdvd : orderOf s ∣ 4 := by
    have := orderOf_dvd_natCard (⟨s, hs⟩ : ↥Tb)
    rwa [Subgroup.orderOf_mk, h.card_Tb] at this
  have hmem : orderOf s ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdivs] at hmem
  simpa using hmem

theorem sq_mul_involution (h : E9Z4Str X Tb P) {t a : MulAut V} (ht : t ∈ X) (ht2 : orderOf t = 2)
    (ha : a ∈ P) : (a * t) ^ 2 = 1 := by
  have htsq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  calc (a * t) ^ 2 = a * (t * a * t⁻¹) * t ^ 2 := by rw [pow_two]; group
    _ = 1 := by rw [h.inverts_of_involution ht ht2 a ha, htsq]; group

omit [Finite V] in
theorem mul_ne_one (h : E9Z4Str X Tb P) {t a : MulAut V} (ht : t ∈ Tb) (ht1 : t ≠ 1)
    (ha : a ∈ P) : a * t ≠ 1 := by
  intro hat
  have hta : t = a⁻¹ := eq_inv_of_mul_eq_one_right hat
  have : t ∈ P ⊓ Tb := ⟨by rw [hta]; exact P.inv_mem ha, ht⟩
  rw [h.P_inf_Tb, Subgroup.mem_bot] at this
  exact ht1 this

theorem orderOf_mul_Tb (h : E9Z4Str X Tb P) {a s : MulAut V} (ha : a ∈ P) (hs : s ∈ Tb)
    (hs1 : s ≠ 1) : orderOf (a * s) = orderOf s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h.orderOf_Tb hs with h1 | h2 | h4
  · exact absurd (orderOf_eq_one_iff.mp h1) hs1
  · rw [h2]
    exact orderOf_eq_prime (h.sq_mul_involution (h.Tb_le_X hs) h2 ha) (h.mul_ne_one hs hs1 ha)
  · have hs2 : orderOf (s ^ 2) = 2 := by
      rw [orderOf_pow' _ (by norm_num), h4]
      norm_num
    have hs2T : s ^ 2 ∈ Tb := Tb.pow_mem hs 2
    have hsq : (a * s) ^ 2 = (a * (s * a * s⁻¹)) * s ^ 2 := by rw [pow_two]; group
    have hy : a * (s * a * s⁻¹) ∈ P := P.mul_mem ha (h.conj_mem hs ha)
    have h4' : (a * s) ^ 2 ^ (1 + 1) = 1 := by
      rw [pow_succ, pow_one, pow_mul, hsq]
      exact h.sq_mul_involution (h.Tb_le_X hs2T) hs2 hy
    have hne : ¬ (a * s) ^ 2 ^ 1 = 1 := by
      rw [pow_one, hsq]
      exact h.mul_ne_one hs2T (fun e => by rw [e] at hs2; simp at hs2) hy
    rw [h4, orderOf_eq_prime_pow hne h4']
    norm_num

theorem orderOf_mem (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X) :
    orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by
  obtain ⟨a, ha, s, hs, rfl⟩ := h.exists_mul hx
  by_cases hs1 : s = 1
  · subst hs1
    rw [mul_one]
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (h.exp_P a ha)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inl e))
  · rw [h.orderOf_mul_Tb ha hs hs1]
    rcases h.orderOf_Tb hs with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr e))

theorem exists_mul_of_involution (h : E9Z4Str X Tb P) {t x : MulAut V} (ht : t ∈ Tb)
    (ht2 : orderOf t = 2) (hx : x ∈ X) (hx2 : orderOf x = 2) : ∃ a ∈ P, x = a * t := by
  obtain ⟨a, ha, s, hs, rfl⟩ := h.exists_mul hx
  by_cases hs1 : s = 1
  · subst hs1
    rw [mul_one] at hx2 ⊢
    have h3 : a ^ 3 = 1 := h.exp_P a ha
    have h2 : a ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one a
    have ha1 : a = 1 := by
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    rw [ha1] at hx2
    simp at hx2
  · rw [h.orderOf_mul_Tb ha hs hs1] at hx2
    exact ⟨a, ha, by rw [h.eq_of_orderOf_eq_two hs ht hx2 ht2]⟩

theorem exists_gen (h : E9Z4Str X Tb P) {t : MulAut V} (ht : t ∈ Tb) (ht2 : orderOf t = 2) :
    ∃ g ∈ Tb, orderOf g = 4 ∧ g ^ 2 = t := by
  obtain ⟨g, hg⟩ := h.cyclic_Tb.exists_generator
  have hog : orderOf (g : MulAut V) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact h.card_Tb
  have hg2 : orderOf ((g : MulAut V) ^ 2) = 2 := by
    rw [orderOf_pow' _ (by norm_num), hog]
    norm_num
  exact ⟨g, g.2, hog, h.eq_of_orderOf_eq_two (Tb.pow_mem g.2 2) ht hg2 ht2⟩

theorem eq_of_commute_of_involution (h : E9Z4Str X Tb P) {x y : MulAut V} (hx : x ∈ X)
    (hy : y ∈ X) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x * y = y * x) : x = y := by
  obtain ⟨t, htT, ht2, htinv⟩ := h.inv
  have htsq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  obtain ⟨a, ha, rfl⟩ := h.exists_mul_of_involution htT ht2 hx hx2
  obtain ⟨b, hb, rfl⟩ := h.exists_mul_of_involution htT ht2 hy hy2
  have h1 : (a * t) * (b * t) = a * b⁻¹ := by
    calc (a * t) * (b * t) = a * (t * b * t⁻¹) * t ^ 2 := by group
      _ = a * b⁻¹ := by rw [htinv b hb, htsq]; group
  have hsx : (a * t) ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one _
  have hsy : (b * t) ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one _
  have h2 : (a * b⁻¹) ^ 2 = 1 := by
    rw [← h1, (Commute.mul_pow hxy), hsx, hsy, one_mul]
  have h3 : (a * b⁻¹) ^ 3 = 1 := h.exp_P _ (P.mul_mem ha (P.inv_mem hb))
  have h4 : a * b⁻¹ = 1 := by
    calc a * b⁻¹ = (a * b⁻¹) ^ 3 * ((a * b⁻¹) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  rw [mul_inv_eq_one.mp h4]

end E9Z4Str

end CFSG.Quasithin
