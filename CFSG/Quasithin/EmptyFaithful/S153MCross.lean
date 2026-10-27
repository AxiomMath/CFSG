module

public import CFSG.Quasithin.EmptyFaithful.SzN15Sort
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.EmptyFaithful.S153LKsA2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

private theorem bender_odd_two_pow_add_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k + 1) :=
  ((Nat.even_pow' hk.ne').mpr even_two).add_one

private theorem bender_two_pow_cases {j : ℕ} (hj : 1 ≤ j) :
    2 ^ j = 2 ∨ 2 ^ j = 4 ∨ 8 ≤ 2 ^ j := by
  rcases Nat.lt_or_ge j 3 with h | h
  · have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl
    · left; norm_num
    · right; left; norm_num
  · right; right
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h

private theorem bender_poly_sz {x c : ℕ} (hx : x = 2 ∨ x = 4 ∨ 8 ≤ x) (hc : c = 1 ∨ c = 3)
    (h : c * ((x ^ 6 + 1) * (x ^ 3 - 1)) = (x ^ 4 - 1) * (x ^ 6 - 1)) : False := by
  rcases hx with rfl | rfl | hx
  · rcases hc with rfl | rfl <;> norm_num at h
  · rcases hc with rfl | rfl <;> norm_num at h
  · have hy : 512 ≤ x ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
    have hx6 : x ^ 6 = x ^ 3 * x ^ 3 := by ring
    have hx4 : x ^ 4 = x * x ^ 3 := by ring
    have hxy : 8 * x ^ 3 ≤ x * x ^ 3 := Nat.mul_le_mul_right _ hx
    have hsq : x ^ 3 * x ^ 3 - 1 = (x ^ 3 + 1) * (x ^ 3 - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (x ^ 3) 1
      simpa using this
    rw [hx6, hsq, hx4] at h
    generalize x ^ 3 = y at h hy hxy
    have hpos : 0 < y - 1 := by omega
    have h' : c * (y * y + 1) = (x * y - 1) * (y + 1) := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc c * (y * y + 1) * (y - 1) = c * ((y * y + 1) * (y - 1)) := by ring
        _ = (x * y - 1) * ((y + 1) * (y - 1)) := h
        _ = (x * y - 1) * (y + 1) * (y - 1) := by ring
    obtain ⟨t, ht⟩ : ∃ t, x * y = t + 1 := ⟨x * y - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel] at h'
    have ht7 : 7 * y ≤ t := by omega
    have hc3 : c ≤ 3 := by rcases hc with rfl | rfl <;> norm_num
    nlinarith [Nat.mul_le_mul ht7 (le_refl (y + 1)), Nat.mul_le_mul hc3 (le_refl (y * y + 1))]

private theorem bender_arith_sl3 {n m c N : ℕ} (hn : 3 ≤ n) (hm : 1 ≤ m) (hc : c = 1 ∨ c = 3)
    (hN : N = 2 ^ n * (2 ^ (2 * n) - 1) ∨ N = 2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) ∨
      3 * N = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))
    (h : N * c = 2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1))) : False := by
  have hB : Odd ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) :=
    Odd.mul (SzN15.odd_two_pow_sub_one (by omega)) (SzN15.odd_two_pow_sub_one (by omega))
  rcases hN with hN | hN | hN
  · subst hN
    have hu : Odd (c * (2 ^ (2 * n) - 1)) :=
      SzN15.odd_mul_c hc (SzN15.odd_two_pow_sub_one (by omega))
    have e : 2 ^ n * (c * (2 ^ (2 * n) - 1)) =
        2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) := by rw [← h]; ring
    have hnm : n = 3 * m := SzN15.two_pow_mul_odd_inj hu hB e
    subst hnm
    have e3 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := pow_mul' 2 3 m
    have e2 : (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 := pow_mul' 2 2 m
    have e6 : (2 : ℕ) ^ (2 * (3 * m)) = ((2 ^ m) ^ 3) ^ 2 := by
      rw [← pow_mul, ← pow_mul]; ring_nf
    rw [e3, e2, e6] at h
    refine SzN15.key_sl2 (2 ^ m) c (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm) hc ?_
    rw [mul_comm c]; exact h
  · subst hN
    have hu : Odd (c * ((2 ^ (2 * n) + 1) * (2 ^ n - 1))) :=
      SzN15.odd_mul_c hc (Odd.mul (bender_odd_two_pow_add_one (by omega))
        (SzN15.odd_two_pow_sub_one (by omega)))
    have e : 2 ^ (2 * n) * (c * ((2 ^ (2 * n) + 1) * (2 ^ n - 1))) =
        2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) := by rw [← h]; ring
    have hnm : 2 * n = 3 * m := SzN15.two_pow_mul_odd_inj hu hB e
    obtain ⟨j, rfl, rfl⟩ : ∃ j, n = 3 * j ∧ m = 2 * j := ⟨m / 2, by omega, by omega⟩
    have hj : 1 ≤ j := by omega
    have p1 : (2 : ℕ) ^ (2 * (3 * j)) = (2 ^ j) ^ 6 := by rw [← pow_mul]; ring_nf
    have p2 : (2 : ℕ) ^ (3 * j) = (2 ^ j) ^ 3 := pow_mul' 2 3 j
    have p3 : (2 : ℕ) ^ (3 * (2 * j)) = (2 ^ j) ^ 6 := by rw [← pow_mul]; ring_nf
    have p4 : (2 : ℕ) ^ (2 * (2 * j)) = (2 ^ j) ^ 4 := by rw [← pow_mul]; ring_nf
    rw [p1, p2, p3, p4] at h
    have hx := bender_two_pow_cases hj
    generalize (2 : ℕ) ^ j = x at h hx
    have hx6 : 0 < x ^ 6 := by
      rcases hx with rfl | rfl | hx
      · norm_num
      · norm_num
      · positivity
    refine bender_poly_sz hx hc ?_
    apply Nat.eq_of_mul_eq_mul_left hx6
    calc x ^ 6 * (c * ((x ^ 6 + 1) * (x ^ 3 - 1))) = x ^ 6 * (x ^ 6 + 1) * (x ^ 3 - 1) * c := by
          ring
      _ = x ^ 6 * ((x ^ 4 - 1) * (x ^ 6 - 1)) := h
  · have hu : Odd (c * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) :=
      SzN15.odd_mul_c hc (Odd.mul (SzN15.odd_two_pow_sub_one (by omega))
        (bender_odd_two_pow_add_one (by omega)))
    have hB3 : Odd (3 * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1))) := Odd.mul (by decide) hB
    have e : 2 ^ (3 * n) * (c * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) =
        2 ^ (3 * m) * (3 * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1))) := by
      calc _ = c * (2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by ring
        _ = c * (3 * N) := by rw [hN]
        _ = 3 * (N * c) := by ring
        _ = _ := by rw [h]; ring
    have hnm : 3 * n = 3 * m := SzN15.two_pow_mul_odd_inj hu hB3 e
    have hnm' : n = m := by omega
    rw [hnm'] at e
    have e' := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (3 * m)) e
    have hpos : 0 < 2 ^ (2 * m) - 1 := by
      have : 2 ^ 2 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have e'' : c * (2 ^ (3 * m) + 1) = 3 * (2 ^ (3 * m) - 1) := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc (2 ^ (2 * m) - 1) * (c * (2 ^ (3 * m) + 1))
          = c * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) + 1)) := by ring
        _ = 3 * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) := e'
        _ = (2 ^ (2 * m) - 1) * (3 * (2 ^ (3 * m) - 1)) := by ring
    have h8 : 8 ≤ 2 ^ (3 * m) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hc with rfl | rfl <;> omega

private theorem bender_arith_sp4 {n m N : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hm : 1 ≤ m)
    (hN : N = 2 ^ n * (2 ^ (2 * n) - 1) ∨ N = 2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) ∨
      3 * N = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))
    (h : N = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) : False := by
  have hB : Odd ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) :=
    Odd.mul (SzN15.odd_two_pow_sub_one (by omega)) (SzN15.odd_two_pow_sub_one (by omega))
  obtain ⟨k, hk⟩ := hodd
  rcases hN with hN | hN | hN
  · have hu : Odd (2 ^ (2 * n) - 1) := SzN15.odd_two_pow_sub_one (by omega)
    have e : 2 ^ n * (2 ^ (2 * n) - 1) =
        2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := hN.symm.trans h
    have := SzN15.two_pow_mul_odd_inj hu hB e
    omega
  · have hu : Odd ((2 ^ (2 * n) + 1) * (2 ^ n - 1)) :=
      Odd.mul (bender_odd_two_pow_add_one (by omega)) (SzN15.odd_two_pow_sub_one (by omega))
    have e : 2 ^ (2 * n) * ((2 ^ (2 * n) + 1) * (2 ^ n - 1)) =
        2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
      calc _ = N := by rw [hN]; ring
        _ = _ := h
    have := SzN15.two_pow_mul_odd_inj hu hB e
    omega
  · have hu : Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) :=
      Odd.mul (SzN15.odd_two_pow_sub_one (by omega)) (bender_odd_two_pow_add_one (by omega))
    have hB3 : Odd (3 * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) := Odd.mul (by decide) hB
    have e : 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) =
        2 ^ (4 * m) * (3 * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) := by
      calc _ = 3 * N := by rw [hN]; ring
        _ = 3 * (2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) := by rw [h]
        _ = _ := by ring
    have := SzN15.two_pow_mul_odd_inj hu hB3 e
    omega

private theorem bender_card {Y : Type} [Group Y] {Ks : Subgroup Y}
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hKs : IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks ∨ IsPSU 3 2 n ↥Ks) :
    Nat.card ↥Ks = 2 ^ n * (2 ^ (2 * n) - 1) ∨
      Nat.card ↥Ks = 2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) ∨
      3 * Nat.card ↥Ks = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
  have hn0 : 0 < n := by omega
  rcases hKs with h | h | h
  · left
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    rw [hc]
    have hg : Nat.gcd (1 + 1) (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (S153L.ks_odd_two_pow_sub_one hn0)
    unfold CFSG.Open.ordA
    rw [show (2 : ℕ) - 1 = 1 from rfl, show Finset.Icc 2 (1 + 1) = {2} by decide,
      Finset.prod_singleton, hg, Nat.div_one, show 1 * (1 + 1) / 2 = 1 from rfl, pow_one,
      pow_mul']
  · right; left
    obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hK
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', ← hf]
    ring
  · right; right
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
    have key : Nat.card ↥Ks = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) / 3 := by
      rw [hc]
      unfold CFSG.Open.ordTwistedA
      have e2 : ((((2 ^ n : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = 2 ^ (2 * n) - 1 := by
        have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
        have h2 : ((((2 ^ n : ℕ) : ℤ)) ^ 2 - (-1) ^ 2) = ((2 ^ (2 * n) - 1 : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub h1]
          ring
        rw [h2, Int.toNat_natCast]
      have e3 : ((((2 ^ n : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = 2 ^ (3 * n) + 1 := by
        have h2 : ((((2 ^ n : ℕ) : ℤ)) ^ 3 - (-1) ^ 3) = ((2 ^ (3 * n) + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [h2, Int.toNat_natCast]
      have hg3 : Nat.gcd 3 (2 ^ n + 1) = 3 :=
        Nat.gcd_eq_left (S153L.ks_three_dvd_two_pow_add_one hodd)
      rw [show (3 - 1 : ℕ) = 2 from rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by decide,
        Finset.prod_pair (by norm_num), e2, e3, show 2 + 1 = 3 from rfl, hg3,
        show 2 * (2 + 1) / 2 = 3 from rfl]
      congr 1
      ring
    have hd : 3 ∣ 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) :=
      Dvd.dvd.mul_left (S153L.ks_three_dvd_two_pow_add_one ((by decide : Odd 3).mul hodd)) _
    rw [key]
    exact Nat.mul_div_cancel' hd

private theorem bender_card_center_sl3 {L K : Type} [Group L] [Field K] [Finite K]
    (e : ↥(StatedSL 3 K) ≃* L) : Nat.card (Subgroup.center L) ∣ 3 := by
  have h1 : Nat.card (Subgroup.center L) = Nat.card (Subgroup.center ↥(StatedSL 3 K)) :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  have h2 : Nat.card (Subgroup.center ↥(StatedSL 3 K)) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) :=
    (Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 K)).toEquiv).symm
  have h3 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) =
      Nat.gcd (Nat.card K - 1) 3 := by
    have h : rootsOfUnity 3 K = (powMonoidHom 3 : Kˣ →* Kˣ).ker := by
      ext x
      rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin, h, IsCyclic.card_powMonoidHom_ker, Nat.card_units]
  rw [h1, h2, h3]
  exact Nat.gcd_dvd_right _ _

private theorem bender_center_sp4 {K : Type} [Field K] [CharP K 2] :
    Subgroup.center ↥(StatedSp 2 K) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hmem : (c : K) ^ 2 = 1 := by
    have h := x.2
    rw [← hc, CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff (by norm_num)] at h
    exact h
  have hc1 : (c : K) = 1 := by
    have h := sub_pow_char (p := 2) (c : K) 1
    rw [hmem, one_pow, sub_self] at h
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one]

private theorem bender_not_sl3 {L : Type} [Group L] {Y : Type}
    [Group Y] {Ks : Subgroup Y} {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hKs : IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks ∨ IsPSU 3 2 n ↥Ks) (σ : L →* ↥Ks)
    (hσ : Function.Surjective σ) (hz : σ.ker ≤ Subgroup.center L) {K : Type} [Field K]
    [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (e : ↥(StatedSL 3 K) ≃* L) : False := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      omega
    · exact h
  have hcard : Nat.card L = Nat.card ↥Ks * Nat.card σ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσ).toEquiv]
  have e3 : (2 ^ m) ^ 3 = 2 ^ (3 * m) := (pow_mul' 2 3 m).symm
  have e2 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := (pow_mul' 2 2 m).symm
  have hL : Nat.card L = 2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) := by
    rw [← Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK, e3, e2]
  have hc3 : Nat.card σ.ker ∣ 3 := (Subgroup.card_dvd_of_le hz).trans (bender_card_center_sl3 e)
  have hc : Nat.card σ.ker = 1 ∨ Nat.card σ.ker = 3 := (Nat.dvd_prime Nat.prime_three).1 hc3
  exact bender_arith_sl3 hn hm hc (bender_card hn hodd hKs) (by rw [← hcard, hL])

private theorem bender_not_sp4 {L : Type} [Group L] {Y : Type}
    [Group Y] {Ks : Subgroup Y} {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hKs : IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks ∨ IsPSU 3 2 n ↥Ks) (σ : L →* ↥Ks)
    (hσ : Function.Surjective σ) (hz : σ.ker ≤ Subgroup.center L) {K : Type} [Field K]
    [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (e : ↥(StatedSp 2 K) ≃* L) : False := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      omega
    · exact h
  have hcp : CharP K 2 := SzN15.charP_two_of_card hK
  have hcard : Nat.card L = Nat.card ↥Ks * Nat.card σ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσ).toEquiv]
  have hL : Nat.card L = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
    rw [← Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    have a1 : (2 ^ m) ^ (2 ^ 2) = 2 ^ (4 * m) := by rw [← pow_mul]; ring_nf
    have a2 : (2 ^ m) ^ (2 * 1) = 2 ^ (2 * m) := by rw [← pow_mul]; ring_nf
    have a3 : (2 ^ m) ^ (2 * 2) = 2 ^ (4 * m) := by rw [← pow_mul]; ring_nf
    rw [a1, a2, a3]
  have hZ : Nat.card (Subgroup.center L) = 1 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, bender_center_sp4, Subgroup.card_bot]
  have hc1 : Nat.card σ.ker = 1 := by
    have := Subgroup.card_dvd_of_le hz
    rw [hZ] at this
    exact Nat.dvd_one.1 this
  rw [hc1, mul_one] at hcard
  exact bender_arith_sp4 hn hodd hm (bender_card hn hodd hKs) (by rw [← hcard, hL])

theorem not_natOutcome_of_bender {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} (_hq : CFSG.IsQuasisimple ↥L) {Y : Type} [Group Y] {Ks : Subgroup Y}
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hKs : IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks ∨ IsPSU 3 2 n ↥Ks) (σ : ↥L →* ↥Ks)
    (hσ : Function.Surjective σ) (hz : σ.ker ≤ Subgroup.center ↥L) : ¬ SzN15.NatOutcome L := by
  rintro (⟨K, _, _, m, hK, π, hπ⟩ | ⟨K, _, _, m, hK, π, hπ⟩ | ⟨K, _, _, m, I, π, hK, -, -, hreal⟩)
  · exact bender_not_sl3 hn hodd hKs σ hσ hz hK (MulEquiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩)
  · exact bender_not_sp4 hn hodd hKs σ hσ hz hK (MulEquiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩)
  · exact bender_not_sl3 hn hodd hKs σ hσ hz hK (MulEquiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0), (hreal 0).1⟩)

end S153M

end CFSG.Quasithin
