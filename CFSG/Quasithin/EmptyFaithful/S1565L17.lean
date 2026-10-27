module

public import CFSG.Quasithin.EmptyFaithful.S1565L16

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

theorem pow_two_mul_odd_inj {x y u v : ℕ} (hu : Odd u) (hv : Odd v) (h : 2 ^ x * u = 2 ^ y * v) :
    x = y := by
  have key : ∀ {x y u v : ℕ}, Odd u → 2 ^ x * u = 2 ^ y * v → x < y → False := by
    intro x y u v hu h hxy
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hxy
    have h2 : 2 ^ x * u = 2 ^ x * (2 ^ (d + 1) * v) := by
      rw [h]
      ring
    have h3 : u = 2 ^ (d + 1) * v := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have h4 : Even u := by
      rw [h3]
      exact Even.mul_right (by simp [pow_succ]) v
    exact (Nat.not_even_iff_odd.mpr hu) h4
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact (key hu h hxy).elim
  · exact hxy
  · exact (key hv h.symm hxy).elim

private theorem odd_pow_sq_sub_one (m : ℕ) (hm : 1 ≤ m) : Odd ((2 ^ m) ^ 2 - 1) := by
  have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : Even ((2 ^ m) ^ 2) :=
    Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
  obtain ⟨c, hc⟩ := h2
  exact ⟨c - 1, by omega⟩

private theorem sz_vs_sl2_false {x : ℕ} (hx : 8 ≤ x)
    (h : x ^ 2 * ((x - 1) * (x ^ 2 + 1)) = x ^ 2 * ((x ^ 2) ^ 2 - 1)) : False := by
  have h1 : (x - 1) * (x ^ 2 + 1) = (x ^ 2) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have hy : 7 ≤ y := by omega
  have h2 : ((y + 1) ^ 2) ^ 2 - 1 = y * ((y + 1) ^ 3 + (y + 1) ^ 2 + (y + 1) + 1) := by
    have hle : 1 ≤ ((y + 1) ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    zify [hle]
    ring
  rw [h2, Nat.add_sub_cancel] at h1
  have h3 : y * ((y + 1) ^ 2 + 1) = y * ((y + 1) ^ 3 + (y + 1) ^ 2 + (y + 1) + 1) := h1
  have h4 : (y + 1) ^ 2 + 1 = (y + 1) ^ 3 + (y + 1) ^ 2 + (y + 1) + 1 :=
    Nat.eq_of_mul_eq_mul_left (by omega) h3
  nlinarith [h4, hy]

theorem orthExcl_of : OrthExcl := by
  intro W _ _ n hn3 hnodd L₀ V C hshape ⟨a, ha1, hBO⟩
  obtain ⟨K, fK, finK, hchar, hK, π, hπ⟩ := hBO
  have hπs : Function.Surjective π := hπ.1
  have h504 := le_card_of_psl2_or_sz hn3 hshape
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSL : IsSimpleGroup (FFModel.twistTensor a (StatedSL 2 K)).Gam :=
    isSimpleGroup_statedSL2 hq4
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      have hall : ∀ x : ↥L₀, x = 1 := by
        intro x
        obtain ⟨g, rfl⟩ := hπs x
        have : g ∈ π.ker := by rw [h]; trivial
        exact this
      have : Nat.card ↥L₀ = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => (hall x).trans (hall y).symm⟩, ⟨1⟩⟩
      omega
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  have hbij : Nat.card ↥L₀ = Nat.card ↥(StatedSL 2 K) :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπs⟩)).symm
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ (2 * a) := by rw [← Nat.card_eq_fintype_card, hK]
  have hcardSL : Nat.card ↥(StatedSL 2 K) = 2 ^ (2 * a) * ((2 ^ (2 * a)) ^ 2 - 1) := by
    rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL_two K, hcardK]
  rw [hcardSL] at hbij
  have hv : Odd ((2 ^ (2 * a)) ^ 2 - 1) := odd_pow_sq_sub_one _ (by omega)
  rcases hshape with h | h
  · obtain ⟨-, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two h
    rw [hc] at hbij
    have hu : Odd (Vol2.Ch11.SecA.oSL2 n) := by
      have := odd_pow_sq_sub_one n (by omega)
      rw [← pow_mul, mul_comm n 2] at this
      exact this
    have := pow_two_mul_odd_inj hu hv hbij
    obtain ⟨k, hk⟩ := hnodd
    omega
  · obtain ⟨-, a', ha', K', _, _, hf, hK', ⟨e⟩⟩ := h
    subst hf
    have hcS := CFSG.LieType.Ree.suzuki_order (a := a') hK'
    rw [Nat.card_congr e.toEquiv, hcS] at hbij
    set x : ℕ := 2 ^ (2 * a' + 1) with hx
    have hx8 : 8 ≤ x := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hodd1 : Odd ((x - 1) * (x ^ 2 + 1)) := by
      have h1 : Odd (x - 1) := by
        have : Even x := Nat.even_pow.mpr ⟨even_two, by omega⟩
        obtain ⟨c, hc⟩ := this
        exact ⟨c - 1, by omega⟩
      have h2 : Odd (x ^ 2 + 1) := by
        have : Even (x ^ 2) := Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
        exact this.add_one
      exact Nat.odd_mul.mpr ⟨h1, h2⟩
    have e2 : x ^ 2 = 2 ^ (2 * (2 * a' + 1)) := by
      rw [hx, ← pow_mul, mul_comm (2 * a' + 1) 2]
    have hL : x ^ 2 * (x - 1) * (x ^ 2 + 1) =
        2 ^ (2 * (2 * a' + 1)) * ((x - 1) * (x ^ 2 + 1)) := by
      rw [mul_assoc, e2]
    rw [hL] at hbij
    have h2a := pow_two_mul_odd_inj hodd1 hv hbij
    have haeq : a = 2 * a' + 1 := by omega
    subst haeq
    apply sz_vs_sl2_false hx8
    rw [← e2] at hbij
    exact hbij

end CFSG.Quasithin
