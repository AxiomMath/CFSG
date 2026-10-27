module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Idx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Aut
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Alt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Rank

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem mul_comm_of_commutator_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_def] at this
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

theorem false_of_pow_two_pow_three {k : G} (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1)
    (h2 : ∃ m : ℕ, k ^ 2 ^ m = 1) : False := by
  obtain ⟨m, hm⟩ := h2
  have h1 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have h3 : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
  have hd : orderOf k ∣ Nat.gcd (2 ^ m) 3 := Nat.dvd_gcd h1 h3
  have hg : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
  rw [hg] at hd
  exact hk1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))

theorem false_of_mem_commuting_blocks [Finite G] {X Y : Subgroup G} (hX : IsShort2 X)
    (hcomm : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) {k : G} (hkX : k ∈ X) (hkY : k ∈ Y)
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) : False := by
  have hkc : k ∈ pCoreOf 2 X := by
    have hmem : k ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine ⟨hkX, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact hcomm a (pCoreOf_le 2 X ha) k hkY
    exact hX.2.1 hmem
  exact false_of_pow_two_pow_three hk1 hk3
    (C1.exists_pow_eq_one_of_isPGroup (pCoreOf_isPGroup 2 X) hkc)

theorem mem_normalizer_of_commute [Finite G] {I X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I) (hX : IsBlock2 I X)
    {z k : G} (hz : z ∈ I) (hkX : k ∈ X) (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) (hkz : k * z = z * k) :
    z ∈ Subgroup.normalizer (X : Set G) := by
  by_contra hzn
  have hX' : IsBlock2 I (conjByElt z X) :=
    isBlock2_conjByElt_of_normalizer1515c hX (Subgroup.le_normalizer hz)
  have hne : X ≠ conjByElt z X := fun h =>
    hzn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm' := hC19 I X (conjByElt z X) hchar hX hX' hne
  have hcomm : ∀ a ∈ X, ∀ b ∈ conjByElt z X, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm', Subgroup.mem_bot, commutatorElement_def] at this
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [this, one_mul]
  have hkY : k ∈ conjByElt z X := by
    rw [mem_conjByElt]
    have : z⁻¹ * k * z = k := by
      calc z⁻¹ * k * z = z⁻¹ * (k * z) := by group
        _ = k := by rw [hkz]; group
    rw [this]
    exact hkX
  exact false_of_mem_commuting_blocks hX.1 hcomm hkX hkY hk3 hk1

theorem commute_block_of_central [Finite G] {I S K P Zs X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hS : IsSylowTwoOf S I) (hKI : K ≤ I)
    (hPK : P ≤ K) (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Zs, k * z = z * k)
    (hZS : ∀ z ∈ Zs, z ∈ S ∧ z ^ 2 = 1 ∧ ∀ s ∈ S, z * s = s * z)
    (hX : IsBlock2 I X) (htype : IsAltType X 3 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type X n) :
    ∀ z ∈ Zs, ∀ x ∈ X, x * z = z * x := by
  have h3 := three_dvd_card_of_type htype
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank' : CFSG.Open.pRank 3 I ≤ 2 := by
    rw [← pRank_top_subtype (p := 3) I]
    exact hrank
  have hPo : P ≤ oTwoUpper K := fun x hx => by
    refine mem_oTwoUpper_of_odd (hPK hx) ?_
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hP.2 x hx)
    exact Odd.of_dvd_nat (by decide) h1
  have hPN : P ≤ Subgroup.normalizer (X : Set G) :=
    hPo.trans (oTwoUpper_le_normalizer_of_block hC19 hchar hrank hX h3 hKI)
  obtain ⟨k, hkPX, hk1⟩ := exists_mem_inf_ne_one hrank' hX.2.1 (hPK.trans hKI) hPN hP hP9 h3
  have hkP : k ∈ P := hkPX.1
  have hkX : k ∈ X := hkPX.2
  have hk3 : k ^ 3 = 1 := hP.2 k hkP
  have hkQ : k ∉ blockQ X := fun h =>
    false_of_pow_two_pow_three hk1 hk3 (C1.exists_pow_eq_one_of_isPGroup (C1.blockQ_isPGroup X) h)
  have hSyl : IsSylowIn 2 (S ⊓ X) X := isSylowIn_inf_of_block hC19 hchar hrank hS hX h3
  have hU₂2 : IsPGroup 2 (S ⊓ X : Subgroup G) := hS.2.1.to_inf_left
  have hodd : ¬ 2 ∣ ((S ⊓ X).subgroupOf X).index := hSyl.2.2
  intro z hz
  obtain ⟨hzS, hz2, hzc⟩ := hZS z hz
  have hkz : k * z = z * k := hKZ k (hPK hkP) z hz
  have hzN : z ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_of_commute hC19 hchar hX (hS.1 hzS) hkX hk3 hk1 hkz
  have hUz : ∀ u ∈ S ⊓ X, u * z = z * u := fun u hu => (hzc u hu.1).symm
  have hzQ : ∀ l ∈ X, z * l * z⁻¹ * l⁻¹ ∈ blockQ X := by
    rcases htype with halt | ⟨n, hn, hlin⟩
    · exact commutator_mem_blockQ_of_alt3 halt hzN hkX hkQ hkz
    · exact commutator_mem_blockQ_of_lin2 hn hlin hzN hU₂2 hUz hodd hkX hk3 hkQ hkz
  exact centralizes_of_fixed hX.1 htype hz2 hzN hzQ hUz hodd hkX hk3 hkQ hkz

end CFSG.Quasithin.S15223
