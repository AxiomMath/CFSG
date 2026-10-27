module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type*} [Group G]

theorem odd_eq_of_two_pow_mul_eq {b c i r : ℕ} (hi : Odd i) (hr : Odd r)
    (h : 2 ^ b * i = 2 ^ c * r) : i = r := by
  wlog hbc : b ≤ c generalizing b c i r
  · exact (this hr hi h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbc
  rw [pow_add, mul_assoc] at h
  have h2 : i = 2 ^ d * r := Nat.eq_of_mul_eq_mul_left (by positivity) h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using h2
  · exfalso
    have : Even i := by
      rw [h2]
      exact (Nat.even_pow.mpr ⟨even_two, hd.ne'⟩).mul_right r
    exact (Nat.not_even_iff_odd.mpr hi) this

variable [Finite G]

theorem index_sylow_eq_of_card_quot {H T : Subgroup G} (hT : IsSylowTwoOf T H) {k r : ℕ}
    (hr : Odd r) (hcard : Nat.card (OTwoQuot H) = 2 ^ k * r) : (T.subgroupOf H).index = r := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card H = Nat.card (OTwoQuot H) * Nat.card (Open.pCore 2 H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 H)
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2).exists_card_eq
  obtain ⟨b, hb⟩ := hT.2.1.exists_card_eq
  have h2 : Nat.card H = Nat.card (T.subgroupOf H) * (T.subgroupOf H).index :=
    (Subgroup.card_mul_index _).symm
  have h3 : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  have hodd : Odd (T.subgroupOf H).index := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]; exact hT.2.2)
  refine odd_eq_of_two_pow_mul_eq (b := b) (c := k + a) hodd hr ?_
  calc 2 ^ b * (T.subgroupOf H).index = Nat.card T * (T.subgroupOf H).index := by rw [hb]
    _ = Nat.card H := by rw [← h3, h2]
    _ = 2 ^ (k + a) * r := by rw [h1, hcard, ha]; ring

omit [Finite G] in
theorem eq_or_eq_of_le_of_index_prime {H T K : Subgroup G} (hTK : T ≤ K) (hKH : K ≤ H) {r : ℕ}
    (hr : r.Prime) (hidx : (T.subgroupOf H).index = r) : K = T ∨ K = H := by
  have h1 : T.relIndex H = T.relIndex K * K.relIndex H :=
    (Subgroup.relIndex_mul_relIndex T K H hTK hKH).symm
  have h2 : T.relIndex H = r := hidx
  rw [h2] at h1
  rcases (Nat.prime_mul_iff.mp (h1 ▸ hr)) with ⟨-, hb⟩ | ⟨-, ha⟩
  · right
    exact le_antisymm hKH (Subgroup.relIndex_eq_one.mp hb)
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp ha) hTK

theorem inf_normalizer_eq_of_card_quot {H T : Subgroup G} (hT : IsSylowTwoOf T H) {k r : ℕ}
    (hk : 1 ≤ k) (hr : r.Prime) (hr2 : Odd r) (hcard : Nat.card (OTwoQuot H) = 2 ^ k * r) :
    H ⊓ Subgroup.normalizer (T : Set G) = T := by
  have hidx := index_sylow_eq_of_card_quot hT hr2 hcard
  have hTle : T ≤ H ⊓ Subgroup.normalizer (T : Set G) := le_inf hT.1 Subgroup.le_normalizer
  refine le_antisymm ?_ hTle
  rcases eq_or_eq_of_le_of_index_prime hTle inf_le_left hr hidx with h | h
  · exact h.le
  · exfalso
    have hHN : H ≤ Subgroup.normalizer (T : Set G) := by
      have : H ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (T : Set G) := inf_le_right
      rw [h] at this
      exact this
    have hTcore : T ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hT.1 hHN hT.2.1
    have heq : pCoreOf 2 H = T := le_antisymm (isSylowTwoOf_pCoreOf_le hT) hTcore
    have h1 : Nat.card H = Nat.card (OTwoQuot H) * Nat.card (Open.pCore 2 H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 H)
    have h2 : Nat.card H = Nat.card (T.subgroupOf H) * (T.subgroupOf H).index :=
      (Subgroup.card_mul_index _).symm
    have h3 : Nat.card (T.subgroupOf H) = Nat.card (Open.pCore 2 H) := by
      have e1 : Nat.card (T.subgroupOf H) = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
      have e2 : Nat.card (pCoreOf 2 H) = Nat.card (Open.pCore 2 H) := by
        unfold pCoreOf
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm.toEquiv
      have e3 : Nat.card T = Nat.card (pCoreOf 2 H) :=
        congrArg (fun K : Subgroup G => Nat.card K) heq.symm
      rw [e1, e3, e2]
    have hpos : 0 < Nat.card (Open.pCore 2 H) := Nat.card_pos
    have h4 : Nat.card (OTwoQuot H) = r := by
      have : Nat.card (OTwoQuot H) * Nat.card (Open.pCore 2 H) = r * Nat.card (Open.pCore 2 H) := by
        rw [← h1, h2, h3, hidx]
        ring
      exact Nat.eq_of_mul_eq_mul_right hpos this
    have h5 : 2 ^ k * r = 1 * r := by rw [← hcard, h4, one_mul]
    have h6 : 2 ^ k = 1 := Nat.eq_of_mul_eq_mul_right hr.pos h5
    have := Nat.pow_eq_one.mp h6
    omega

omit [Finite G] in
@[expose] def SmallQuot (H : Subgroup G) : Prop :=
  Nonempty (OTwoQuot H ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot H ≃* ↥(Sz 0)) ∨
    Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3))

omit [Finite G] in
theorem SmallQuot.exists_card {H : Subgroup G} (h : SmallQuot H) (hSz : Nat.card ↥(Sz 0) = 20) :
    ∃ k r : ℕ, 1 ≤ k ∧ r.Prime ∧ Odd r ∧ Nat.card (OTwoQuot H) = 2 ^ k * r := by
  obtain h | h | h := h
  · obtain ⟨e⟩ := h
    refine ⟨1, 5, le_rfl, by norm_num, by decide, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    norm_num
  · obtain ⟨e⟩ := h
    refine ⟨2, 5, by norm_num, by norm_num, by decide, ?_⟩
    rw [Nat.card_congr e.toEquiv, hSz]
    norm_num
  · obtain ⟨e⟩ := h
    refine ⟨1, 3, le_rfl, by norm_num, by decide, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl

end CFSG.Quasithin
