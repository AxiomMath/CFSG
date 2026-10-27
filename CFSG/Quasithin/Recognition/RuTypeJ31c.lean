module

public import CFSG.Quasithin.Recognition.RuTypeA65
public import CFSG.Quasithin.Recognition.RuTypeJ31a
public import CFSG.Quasithin.Recognition.RuTypeJ31b
public import CFSG.Quasithin.Recognition.RuTypeJ210d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem arith_J31 {N n m7 m13 : ℕ} (hG : N = 2 ^ 11 * 120 * n) (h27 : 27 ∣ N)
    (h125 : 125 ∣ N) (h91 : 91 ∣ N) (hodd : ¬ 2 ∣ n) (hn : n ≤ 455 * (455 + 4608))
    (h7 : N = 4 * 7 * (7 - 1) * m7) (hm7 : m7 % 7 = 1) (h13 : N = 4 * 13 * (13 - 1) * m13)
    (hm13 : m13 % 13 = 1) : N = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 := by
  norm_num at hG h7 h13 hn ⊢
  subst hG
  have h9 : 9 ∣ n := by
    have h : 27 ∣ 245760 * n := h27
    clear h27 h125 h91 h7 h13 hm7 hm13 hn hodd
    omega
  have h25 : 25 ∣ n := by
    have h : 125 ∣ 245760 * n := h125
    clear h27 h125 h91 h7 h13 hm7 hm13 hn hodd h9
    omega
  have h91' : 91 ∣ n := by
    have h : 91 ∣ 245760 * n := h91
    clear h27 h125 h91 h7 h13 hm7 hm13 hn hodd h9 h25
    omega
  have h20475 : 20475 ∣ n := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h25) h91'
    norm_num at h
    exact h
  obtain ⟨k, rfl⟩ := h20475
  clear h27 h125 h91 h9 h25 h91'
  have hk : k ≤ 112 := by
    clear h7 h13 hm7 hm13 hodd
    omega
  have hk2 : ¬ 2 ∣ k := fun h => hodd (h.mul_left _)
  have hk7 : k % 7 = 1 := by
    clear h13 hm13 hn hk hk2 hodd
    omega
  have hk13 : k % 13 = 3 := by
    clear h7 hm7 hn hk hk2 hk7 hodd
    omega
  have hk29 : k = 29 := by
    clear h7 h13 hm7 hm13 hn hodd
    omega
  subst hk29
  norm_num

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem centralizer_z_eq_H : Subgroup.centralizer ({M.z} : Set G) = ruH M.T := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, M.toRuData.mem_H_iff]
  constructor
  · intro h w hw
    rcases M.mem_Z_iff.mp hw with rfl | rfl
    · rw [one_mul, mul_one]
    · exact h.symm
  · intro h
    exact (h M.z M.z_mem_Z).symm

theorem exists_S0_ne_one : ∃ s ∈ M.S0, s ≠ 1 := by
  by_contra h
  have hb : M.S0 = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
    by_contra fun h1 => h ⟨x, hx, h1⟩
  have hc := M.card_S0
  rw [hb, Subgroup.card_bot] at hc
  norm_num at hc

theorem exists_card_eq_sylow
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ}
    (hp : p = 7 ∨ p = 13) : ∃ m, Nat.card G = 4 * p * (p - 1) * m ∧ m % p = 1 := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p (Ls s)))
  set Y : Subgroup G := (Q : Subgroup (Ls s)).map (Ls s).subtype
  have hYL : Y ≤ Ls s := Subgroup.map_subtype_le _
  have hYQ : Y.subgroupOf (Ls s) = Q :=
    Subgroup.comap_map_eq_self_of_injective (Ls s).subtype_injective _
  have hY := M.card_of_sylow_Ls hs hs1 hp hYL ⟨Q, hYQ.symm⟩
  obtain ⟨P, hP⟩ := M.exists_sylow_Y hs hs1 hp hYL hY
  have hN := M.card_normalizer_Y hs hs1 hp hYL hY
  refine ⟨(Subgroup.normalizer (Y : Set G)).index, ?_, ?_⟩
  · rw [← hN, Subgroup.card_mul_index]
  · have hmod := card_sylow_modEq_one p G
    have hPY : (P : Set G) = (Y : Set G) := by
      rw [← hP]
      rfl
    rw [Sylow.card_eq_index_normalizer P, hPY] at hmod
    rw [Nat.ModEq] at hmod
    rw [hmod, Nat.mod_eq_of_lt hpp.one_lt]

include M in
theorem card_eq
    : Nat.card G = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 := by
  obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzo : orderOf M.z = 2 := orderOf_eq_prime M.z_sq M.z_ne_one
  have hso : orderOf s = 2 := orderOf_eq_prime (M.S0_elem.2 s hs) hs1
  obtain ⟨hzs, hcl0⟩ := M.lemma_J27_4 hs hs1
  have hcl : ∀ x : G, orderOf x = 2 → IsConj M.z x ∨ IsConj s x := fun x hx =>
    hcl0 x (by rw [← hx]; exact pow_orderOf_eq_one x) (by
      rintro rfl
      rw [orderOf_one] at hx
      exact absurd hx (by norm_num))
  have hidx := A65.index_centralizer_le hzo hso hzs hcl fun u v hu hv huv h1 =>
    M.lemma_J32 hs hs1 hu hv huv h1
  rw [(M.lemma_J33 hs hs1).1, M.centralizer_z_eq_H] at hidx
  have hd := M.card_conj_z_H_le
  have hn : (ruH M.T).index ≤ 455 * (455 + 4608) :=
    hidx.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hd _))
  have hG : Nat.card G = 2 ^ 11 * 120 * (ruH M.T).index := by
    rw [← M.toRuData.card_H, Subgroup.card_mul_index]
  have hodd : ¬ 2 ∣ (ruH M.T).index := fun h2 =>
    M.T.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le M.toRuData.T_le_H))
  have h27 : 27 ∣ Nat.card G := by
    have := Subgroup.card_subgroup_dvd_card M.GP
    rw [M.card_GP] at this
    exact (show 27 ∣ 4320 by norm_num).trans this
  have h125 : 125 ∣ Nat.card G := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ruH M.T) 5
      (by rw [M.toRuData.card_H]; norm_num)
    have hb5 : orderOf (b : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hb
    have h := (RuDataM.lemma_J27_5 (M := M) b.2 hb5).1
    have := Subgroup.card_subgroup_dvd_card (P5 (b : G))
    rwa [h] at this
  have h91 : 91 ∣ Nat.card G := by
    have := Subgroup.card_subgroup_dvd_card (Ls s)
    rw [M.card_Ls hs hs1] at this
    exact (show 91 ∣ 29120 by norm_num).trans this
  obtain ⟨m7, h7, hm7⟩ := M.exists_card_eq_sylow hs hs1 (Or.inl rfl)
  obtain ⟨m13, h13, hm13⟩ := M.exists_card_eq_sylow hs hs1 (Or.inr rfl)
  exact arith_J31 hG h27 h125 h91 hodd hn h7 hm7 h13 hm13

end RuDataM

end CFSG.Quasithin.RuType
