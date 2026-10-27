module

public import CFSG.Quasithin.Background.F1Rank
public import CFSG.Quasithin.Recognition.CertSzZero

public section

namespace CFSG.Quasithin

open CFSG.Open

section Generic

variable {K : Type*} [Group K] [Finite K]

theorem index_eq_of_card_two_pow_mul_prime {a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card K = 2 ^ a * p) {T : Subgroup K} (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) :
    T.index = p ∧ Nat.card T = 2 ^ a := by
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  have hmul := T.card_mul_index
  rw [hb, hcard] at hmul
  have hcop2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hcopi : Nat.Coprime 2 T.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have hba : b ≤ a := by
    have h1 : 2 ^ b ∣ 2 ^ a * p := ⟨T.index, hmul.symm⟩
    have h2 : 2 ^ b ∣ 2 ^ a := (hcop2p.pow_left b).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  have hab : a ≤ b := by
    have h1 : 2 ^ a ∣ 2 ^ b * T.index := ⟨p, hmul⟩
    have h2 : 2 ^ a ∣ 2 ^ b := (hcopi.pow_left a).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  have hab' : b = a := le_antisymm hba hab
  subst hab'
  exact ⟨Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) b) hmul, hb⟩

theorem isRankOneSylow_of_card_two_pow_mul_prime {a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 1 ≤ a) (hcard : Nat.card K = 2 ^ a * p) (hO : CFSG.Open.pCore 2 K = ⊥) :
    IsRankOneSylow K := by
  intro T hT hodd
  obtain ⟨hi, hTc⟩ := index_eq_of_card_two_pow_mul_prime hp hp2 hcard hT hodd
  have hnn : ¬ T.Normal := by
    intro hN
    have hle : T ≤ CFSG.Open.pCore 2 K := CFSG.LieType.BorelTits.le_pCore 2 hN hT
    rw [hO, le_bot_iff] at hle
    have h1 : Nat.card T = 1 := by rw [hle]; exact Subgroup.card_bot
    rw [hTc] at h1
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hmax : ∀ M : Subgroup K, T ≤ M → M ≠ ⊤ → M = T := by
    intro M hTM hM
    have h1 : T.relIndex M * M.index = T.index := Subgroup.relIndex_mul_index hTM
    rw [hi] at h1
    have hMi : M.index ≠ 1 := fun h => hM (Subgroup.index_eq_one.mp h)
    have hMd : M.index ∣ p := ⟨T.relIndex M, by rw [← h1]; ring⟩
    have hMp : M.index = p := ((Nat.dvd_prime hp).mp hMd).resolve_left hMi
    rw [hMp] at h1
    have h2 : T.relIndex M = 1 := by
      have : T.relIndex M * p = 1 * p := by rw [h1, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    exact (Subgroup.relIndex_eq_one.mp h2).antisymm hTM
  have hN : Subgroup.normalizer (T : Set K) = T := by
    refine hmax _ Subgroup.le_normalizer ?_
    intro h
    exact hnn (Subgroup.normalizer_eq_top_iff.mp h)
  refine ⟨fun h => hnn (Subgroup.normalizer_eq_top_iff.mp h), fun M hTM hM => ?_,
    fun x hx y hy => ?_⟩
  · rw [hmax M hTM hM]
    exact Subgroup.le_normalizer
  · rw [hN] at hx hy
    exact T.mul_mem (T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)) (T.inv_mem hy)

theorem pCore_eq_bot_of_two_involutions {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card K = 2 * p) {x y : K} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x ≠ y) : CFSG.Open.pCore 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ z : K, orderOf z = 2 → ∃ P : Sylow 2 K, (P : Subgroup K) = Subgroup.zpowers z := by
    intro z hz
    have hc : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by rw [Nat.card_zpowers, hz]; norm_num
    have hpg : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card hc
    have hind : ¬ 2 ∣ (Subgroup.zpowers z).index := by
      have hm := (Subgroup.zpowers z).card_mul_index
      rw [hc, hcard] at hm
      have : (Subgroup.zpowers z).index = p := by
        have : 2 * (Subgroup.zpowers z).index = 2 * p := by simpa using hm
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
      rw [this]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm
    exact ⟨hpg.toSylow hind, IsPGroup.toSylow_coe hpg hind⟩
  obtain ⟨P, hP⟩ := hsyl x hx
  obtain ⟨Q, hQ⟩ := hsyl y hy
  have hN : (CFSG.Open.pCore 2 K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hpc : IsPGroup 2 (CFSG.Open.pCore 2 K) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h1 : CFSG.Open.pCore 2 K ≤ Subgroup.zpowers x := hP ▸ hpc.le_sylow_of_normal P
  have h2 : CFSG.Open.pCore 2 K ≤ Subgroup.zpowers y := hQ ▸ hpc.le_sylow_of_normal Q
  refine le_bot_iff.mp fun z hz => ?_
  have hzx := h1 hz
  have hzy := h2 hz
  have key : ∀ (w v : K), orderOf w = 2 → v ∈ Subgroup.zpowers w → v = 1 ∨ v = w := by
    intro w v hw hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul]
      simp [hw2]
    · right
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul]
      simp [hw2]
  have hz1 : z = 1 := by
    rcases key x z hx hzx with h | h
    · exact h
    · rcases key y z hy hzy with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hxy
  exact Subgroup.mem_bot.mpr hz1

end Generic

theorem isRankOneSylow_perm_three : IsRankOneSylow (Equiv.Perm (Fin 3)) := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 2 ^ 1 * 3 := by
    rw [Nat.card_perm]; simp [Nat.factorial]
  have h01 : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have h02 : orderOf (Equiv.swap (0 : Fin 3) 2) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  refine isRankOneSylow_of_card_two_pow_mul_prime Nat.prime_three (by norm_num) le_rfl hcard ?_
  exact pCore_eq_bot_of_two_involutions Nat.prime_three (by norm_num) (by simpa using hcard) h01
    h02 (by decide)

theorem isRankOneSylow_dihedral_five : IsRankOneSylow (DihedralGroup 5) := by
  have hcard : Nat.card (DihedralGroup 5) = 2 ^ 1 * 5 := by
    rw [DihedralGroup.nat_card]; norm_num
  have h0 : orderOf (DihedralGroup.sr (0 : ZMod 5)) = 2 := DihedralGroup.orderOf_sr 0
  have h1 : orderOf (DihedralGroup.sr (1 : ZMod 5)) = 2 := DihedralGroup.orderOf_sr 1
  refine isRankOneSylow_of_card_two_pow_mul_prime Nat.prime_five (by norm_num) le_rfl hcard ?_
  exact pCore_eq_bot_of_two_involutions Nat.prime_five (by norm_num) (by simpa using hcard) h0 h1
    (by decide)

theorem isRankOneSylow_sz_zero : IsRankOneSylow ↥(Sz 0) := by
  have hcard : Nat.card ↥(Sz 0) = 2 ^ 2 * 5 := by rw [card_sz_zero_eq_twenty]; norm_num
  exact isRankOneSylow_of_card_two_pow_mul_prime Nat.prime_five (by norm_num) (by norm_num) hcard
    pCore_two_sz_zero_eq_bot

end CFSG.Quasithin
