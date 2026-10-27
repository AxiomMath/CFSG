module

public import CFSG.Quasithin.EmptyFaithful.S1565L13
public import CFSG.Quasithin.EmptyFaithful.S1565L10

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem natfree_sl2_of_two_le {L : Subgroup (MulAut W)} {V C : Subgroup W} {n' : ℕ} (hn' : 2 ≤ n')
    (h : BinaryNaturalSL L V (V ⊓ C) 2 n') (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ω, hω1, hodd⟩ := exists_unit_odd_order_ne_one hK hn'
  obtain ⟨b, hb, hbr, hnf⟩ :=
    natural_sl2_borel_element ω hω1 (orderOf ω) (pow_orderOf_eq_one ω) hπ S
  exact ⟨b, hb, orderOf ω, hodd, hbr, hnf⟩

theorem natfree_su3 {L : Subgroup (MulAut W)} {V C : Subgroup W} {a : ℕ}
    (h : BinaryNaturalSU3 L V (V ⊓ C) a) (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have ha : 1 ≤ a := by
    by_contra hlt
    have ha0 : a = 0 := by omega
    subst ha0
    have h1 : Nat.card K = 1 := by simpa using hK
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ a) ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hord : orderOf g = (2 ^ a) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h4 : 4 ≤ (2 ^ a) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ a) ^ 2 := Nat.pow_le_pow_left h2a 2
  have h6 : 2 * 2 ^ a ≤ (2 ^ a) ^ 2 := by nlinarith [h2a]
  have hge : 3 ≤ (2 ^ a) ^ 2 - 1 := by omega
  have hodd : Odd (orderOf g) := by
    rw [hord]
    have h4 : Even ((2 ^ a) ^ 2) := Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
    obtain ⟨c, hc⟩ := h4
    exact ⟨c - 1, by omega⟩
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hgb : (g : K) ^ 2 ^ a ≠ g := by
    intro h1
    have h2 : g ^ (2 ^ a) = g := Units.ext (by simpa using h1)
    have h3 : g ^ (2 ^ a - 1) = 1 := by
      have : g ^ (2 ^ a) = g ^ (2 ^ a - 1) * g := by
        rw [← pow_succ]
        congr 1
        omega
      rw [this] at h2
      exact mul_eq_right.mp h2
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at h4
    have h5 := Nat.le_of_dvd (by omega) h4
    omega
  obtain ⟨b, hb, hbr, hnf⟩ := natural_su3_borel_element ha hK g hg1 hgb (orderOf g)
    (pow_orderOf_eq_one g) hπ S
  exact ⟨b, hb, orderOf g, hodd, hbr, hnf⟩

theorem typesFour_good_nat {L Q : Subgroup (MulAut W)}
    (S : Sylow 2 ↥L)
    (hS : ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), (b : MulAut W) ∈ Q)
    (h : (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L ⊤ (⊤ ⊓ fixV L) 2 n') ∨
      (∃ f, BinaryNaturalSz L ⊤ (⊤ ⊓ fixV L) f) ∨ (∃ a, BinaryNaturalSU3 L ⊤ (⊤ ⊓ fixV L) a)) :
    ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV L → w ∈ fixV L := by
  have key : ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ (⊤ : Subgroup W), ((b : MulAut W) u) * u⁻¹ ∈ (⊤ : Subgroup W) ⊓ fixV L →
        u ∈ (⊤ : Subgroup W) ⊓ fixV L := by
    rcases h with ⟨n', hn', h⟩ | ⟨f, h⟩ | ⟨a, h⟩
    · exact natfree_sl2_of_two_le hn' h S
    · exact natfree_sz h S
    · exact natfree_su3 h S
  obtain ⟨b, hbN, r, hr, hbr, hnf⟩ := key
  refine ⟨(b : MulAut W), hS b hbN, r, hr, ?_, ?_⟩
  · have := congrArg Subtype.val hbr
    simpa using this
  · intro w hw
    exact (hnf w trivial ⟨trivial, hw⟩).2

end CFSG.Quasithin
