module

public import CFSG.Quasithin.Vol2.GoldschmidtRes2WBase
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WBruhat
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WGen
public import CFSG.Quasithin.Vol2.Ch3E215MD

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B6 E2 CFSG.Timmesfeld

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem psl2_bounds (h : E2.Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 2 ≤ n)
    (hcard : (kerIn M X).relIndex X = 2 ^ n * ((2 ^ n) ^ 2 - 1))
    (h9 : n = 3 → ∃ c ∈ X, orderOf c = 9) :
    (kerIn M X ⊓ V).relIndex V ≤ 2 ^ n ∧
      2 ^ n ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  have hq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hVle := Ch3E213M.relIndex_le_two_pow h
    (by rw [hq]; exact Ch3E213M.odd_two_pow_sub_one (by omega)) hcard
  refine ⟨hVle, ?_⟩
  by_cases hn3 : n = 3
  · subst hn3
    obtain ⟨c, hcX, hc⟩ := h9 rfl
    obtain ⟨m, hm, hdvd, hle⟩ := Ch3E215M.exists_two_pow_le_of_orderOf h hchar hcX (ℓ := 3)
      (a := 1) Nat.prime_three (by norm_num) (by rw [hc]; norm_num)
    have h6 : 6 ∣ m := Ch3E213M.six_dvd_of_nine_dvd_two_pow_sub_one (by simpa using hdvd)
    refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
    calc (2 ^ 3) ^ 2 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm h6)
      _ ≤ _ := hle
  · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
    have h1 : r ∣ (2 ^ n) ^ 2 - 1 := by
      rw [hq]
      exact hr.dvd
    have hrX : r ∣ Nat.card X :=
      (h1.trans (Dvd.intro_left _ hcard.symm)).trans (Subgroup.relIndex_dvd_card _ _)
    refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
    rw [hq]
    exact Ch3E215M.two_pow_le_of_primitive h hchar (by omega) hr hrX

theorem e215DataW_of_psl2 (h : E2.Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 2 ≤ n)
    (hcard : (kerIn M X).relIndex X = 2 ^ n * ((2 ^ n) ^ 2 - 1))
    (h9 : n = 3 → ∃ c ∈ X, orderOf c = 9)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂)
    (hidx : M.relIndex X = 2 ^ n + 1) (hJ : IsPGroup 2 ↥(kerIn M X))
    (hb4 : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) ≤ 4) : E215DataW X M V g := by
  obtain ⟨hVle, hqb⟩ := psl2_bounds h hchar hn hcard h9
  rcases (hVle.trans hqb).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  refine Or.inr ?_
  have hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 2 ^ n := le_antisymm (heq ▸ hVle) hqb
  have hVB : (kerIn M X ⊓ V).relIndex V = 2 ^ n := heq.trans hBZ
  have h4 : 2 ^ n = 4 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
    omega
  have hBN := conjSub_B_of_general h hchar (by rw [hcard, h4]; norm_num) (by rw [hidx, h4]) hJ
    (by rw [hVB, h4]) (by rw [hBZ, h4]) hBru
  exact commutator_eq_bot_of_bruhat_of_normalized h hBN hBru (by rw [hidx, hBZ])

theorem lt_of_sz (h : E2.Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 3 ≤ n)
    (hcard : (kerIn M X).relIndex X = (2 ^ n) ^ 2 * (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)))
    (hV : (kerIn M X ⊓ V).relIndex V ≤ 2 ^ n) :
    (kerIn M X ⊓ V).relIndex V < (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  have hrX : r ∣ Nat.card X :=
    (((Ch3E213M.primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
      (Dvd.intro_left _ hcard.symm)).trans (Subgroup.relIndex_dvd_card _ _)
  have h1 := Ch3E215M.two_pow_le_of_primitive h hchar (k := 4 * n) (by omega) hr hrX
  have e : ((2 ^ n) ^ 2) ^ 2 = 2 ^ (4 * n) := by
    rw [← pow_mul, ← pow_mul]
    ring_nf
  have h2 : (2 ^ n) ^ 2 ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) :=
    (Nat.pow_le_pow_iff_left two_ne_zero).1 (e ▸ h1)
  have h3 : 2 ^ n < (2 ^ n) ^ 2 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    nlinarith
  omega

theorem e215DataW_of_sz (h : E2.Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 3 ≤ n)
    (hcard : (kerIn M X).relIndex X = (2 ^ n) ^ 2 * (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)))
    (hV : (kerIn M X ⊓ V).relIndex V ≤ 2 ^ n) : E215DataW X M V g :=
  Or.inl (lt_of_sz h hchar hn hcard hV)

end CFSG.Quasithin.Res2
