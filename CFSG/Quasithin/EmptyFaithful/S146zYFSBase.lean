module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg

public section

namespace CFSG.Quasithin.S146zY

open CFSG.QuasithinUnique

theorem isSylowTwoOf_top_iff_index {X : Type*} [Group X] {Q : Subgroup X} :
    IsSylowTwoOf Q ⊤ ↔ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index := by
  unfold IsSylowTwoOf
  rw [show (Q.subgroupOf ⊤).index = Q.index from Subgroup.relIndex_top_right Q]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

theorem card_isSylowTwoOf_top {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) {a m : ℕ} (hm : ¬ 2 ∣ m) (hX : Nat.card X = 2 ^ a * m) :
    Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff_index.mp hS
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  have hidx := Subgroup.card_mul_index S
  rw [hk, hX] at hidx
  have hidx_ne : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  have hv := congrArg (padicValNat 2) hidx
  rw [padicValNat.mul (by positivity) hidx_ne, padicValNat.mul (by positivity) hm0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hi,
    padicValNat.eq_zero_of_not_dvd hm] at hv
  rw [hk]
  have : k = a := by omega
  rw [this]

section Config

variable {A : Type} [Group A] {L P T : Subgroup A}

theorem E25Config.exists_sylow_le [Finite A] (h : E25Config L P T) :
    ∃ (S Y : Subgroup ↥L) (k : ℕ), IsSylowTwoOf S ⊤ ∧ S ≤ Y ∧ Nat.card S = 2 ^ k ∧
      Nat.card Y = 25 * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hidx⟩ := E25Config.isSylowTwoOf_inf h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  refine ⟨(T ⊓ L).subgroupOf L, (P ⊔ (T ⊓ L)).subgroupOf L, k, ?_, ?_, ?_, ?_⟩
  · exact isSylowTwoOf_top_iff_index.mpr
      ⟨hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm, hidx⟩
  · exact Subgroup.subgroupOf_mono L le_sup_right
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hk]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E25Config.sup_inf_le h)).toEquiv,
      E25Config.card_sup_inf h, hk]

theorem E25Config.exists_sylow_le_of_card [Finite A] (h : E25Config L P T) {a m : ℕ}
    (hm : ¬ 2 ∣ m) (hL : Nat.card L = 2 ^ a * m) :
    ∃ S Y : Subgroup ↥L, IsSylowTwoOf S ⊤ ∧ S ≤ Y ∧ Nat.card S = 2 ^ a ∧
      Nat.card Y = 25 * 2 ^ a := by
  obtain ⟨S, Y, k, hS, hSY, hSk, hYk⟩ := E25Config.exists_sylow_le h
  have hSa := card_isSylowTwoOf_top hS hm hL
  exact ⟨S, Y, hS, hSY, hSa, by rw [hYk, ← hSk, hSa]⟩

end Config

end CFSG.Quasithin.S146zY
