module

public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace B51

theorem pow_three_eq_one_of_mem_center {K : Type} [Field K]
    {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) : A ^ 3 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem card_center_SL3_le {K : Type} [Field K] [Finite K] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  simpa using card_rootsOfUnity (R := K) (Fintype.card (Fin 3))

theorem card_eq_of_surjective_SL3 {K : Type} [Field K] [Finite K] {H : Type*} [Group H]
    (π : Matrix.SpecialLinearGroup (Fin 3) K →* H) (hπ : Function.Surjective π)
    (h3 : 3 < Nat.card H) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = Nat.card H ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 3 * Nat.card H := by
  set S := Matrix.SpecialLinearGroup (Fin 3) K
  set Z := Subgroup.center S
  set N := π.ker
  have hsimp : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) :=
    (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  have hcard : Nat.card S = Nat.card H * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have hZ3 : Nat.card Z ≤ 3 := card_center_SL3_le
  have hNm : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  rcases hNm.eq_bot_or_eq_top with h | h
  · have hNZ : N ≤ Z := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    have hN3 : Nat.card N ≤ 3 := (Subgroup.card_le_of_le hNZ).trans hZ3
    have hN2 : Nat.card N ≠ 2 := by
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (by rw [h2])
      have hx3 : x ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact pow_three_eq_one_of_mem_center (hNZ x.2))
      have hd := orderOf_dvd_of_pow_eq_one hx3
      rw [hx] at hd
      norm_num at hd
    have hNpos : 0 < Nat.card N := Nat.card_pos
    have hN : Nat.card N = 1 ∨ Nat.card N = 3 := by omega
    rcases hN with hN | hN
    · left
      rw [hcard, hN, mul_one]
    · right
      rw [hcard, hN, mul_comm]
  · exfalso
    have hsurj : Function.Surjective (π.comp Z.subtype) := by
      intro y
      obtain ⟨g, rfl⟩ := hπ y
      have hg : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := h ▸ Subgroup.mem_top _
      obtain ⟨x, hxN, hx⟩ := hg
      have hxg : x⁻¹ * g ∈ Z := QuotientGroup.eq.mp hx
      refine ⟨⟨x⁻¹ * g, hxg⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
      rw [MonoidHom.mem_ker.mp hxN, inv_one, one_mul]
    have := Nat.card_le_card_of_surjective _ hsurj
    omega

theorem le_of_two_pow_dvd {a b c : ℕ} (hc : Odd c) (h : 2 ^ a ∣ 2 ^ b * c) : a ≤ b := by
  have hcop : Nat.Coprime (2 ^ a) c := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hc)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

theorem card_SL3_eq_pow {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) := by
  rw [CFSG.BrauerLinearThree.card_SL_three, hK, ← pow_mul, ← pow_mul, mul_comm m 3,
    mul_comm m 2, mul_assoc]

theorem card_Sp4_eq_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSp 2 K) = 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
  rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num), hK, ← pow_mul, ← pow_mul, ← pow_mul]
  norm_num [mul_comm n]

theorem card_G2_eq_pow (hG2 : SecA.FactG2DerivedOrder) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ =
      2 ^ (6 * n) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by
  rw [hG2 K n hn hK, ← pow_mul, ← pow_mul, mul_comm n 6, mul_comm n 2]

theorem one_le_of_card_eq {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    1 ≤ m := by
  by_contra h
  have hm : m = 0 := by omega
  rw [hm, pow_zero] at hK
  have := Finite.one_lt_card (α := K)
  omega

theorem not_surjective_SL3_Sp4 {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (π : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(StatedSp 2 F)) :
    ¬ Function.Surjective π := by
  intro hπ
  have hm := one_le_of_card_eq hK
  have hSp := card_Sp4_eq_pow hF
  have hSL := card_SL3_eq_pow hK
  have ho1 : Odd ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) :=
    (SecA.odd_two_pow_sub_one (by omega)).mul (SecA.odd_two_pow_sub_one (by omega))
  have ho2 : Odd ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
    (SecA.odd_two_pow_sub_one (by omega)).mul (SecA.odd_two_pow_sub_one (by omega))
  have h28 : 2 ^ 8 ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 3 < Nat.card ↥(StatedSp 2 F) := by
    rw [hSp]
    have := ho1.pos
    nlinarith
  have hpos : 0 < 2 ^ (4 * n) := by positivity
  have hpos' : 0 < 2 ^ (4 * n) - 1 := (SecA.odd_two_pow_sub_one (by omega)).pos
  have hx4 : 4 ∣ 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hy4 : 4 ∣ 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 (by omega)
  rcases card_eq_of_surjective_SL3 π hπ h3 with h | h
  · rw [hSL, hSp] at h
    have he := SecA.eq_of_two_pow_mul_odd ho2 ho1 h
    rw [he] at h
    have h1 := Nat.eq_of_mul_eq_mul_left hpos h
    rw [mul_comm (2 ^ (2 * n) - 1)] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hpos' h1
    have h22 : 2 ^ (2 * m) = 2 ^ (2 * n) := by
      have := Nat.one_le_two_pow (n := 2 * m)
      have := Nat.one_le_two_pow (n := 2 * n)
      omega
    have := Nat.pow_right_injective le_rfl h22
    omega
  · rw [hSL, hSp, show 3 * (2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))) =
      2 ^ (4 * n) * (3 * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))) by ring] at h
    have he := SecA.eq_of_two_pow_mul_odd ho2 ((by decide : Odd 3).mul ho1) h
    rw [he] at h
    have h1 := Nat.eq_of_mul_eq_mul_left hpos h
    rw [show 3 * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) =
      (2 ^ (4 * n) - 1) * (3 * (2 ^ (2 * n) - 1)) by ring] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hpos' h1
    have := Nat.one_le_two_pow (n := 2 * m)
    have := Nat.one_le_two_pow (n := 2 * n)
    generalize 2 ^ (2 * m) = y at *
    generalize 2 ^ (2 * n) = x at *
    omega

theorem not_surjective_SL3_G2 (hG2 : SecA.FactG2DerivedOrder) {K : Type} [Field K] [Finite K]
    {m : ℕ} (hK : Nat.card K = 2 ^ m) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (π : Matrix.SpecialLinearGroup (Fin 3) K →* ↥⁅quasithinG2 F, quasithinG2 F⁆) :
    ¬ Function.Surjective π := by
  intro hπ
  have hm := one_le_of_card_eq hK
  have hG := card_G2_eq_pow hG2 hn hF
  have hSL := card_SL3_eq_pow hK
  have ho1 : Odd ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) :=
    (SecA.odd_two_pow_sub_one (by omega)).mul (SecA.odd_two_pow_sub_one (by omega))
  have ho2 : Odd ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
    (SecA.odd_two_pow_sub_one (by omega)).mul (SecA.odd_two_pow_sub_one (by omega))
  have h12 : 2 ^ 12 ≤ 2 ^ (6 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 3 < Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ := by
    rw [hG]
    have := ho1.pos
    nlinarith
  have hpos : 0 < 2 ^ (6 * n) := by positivity
  have hpos' : 0 < 2 ^ (6 * n) - 1 := (SecA.odd_two_pow_sub_one (by omega)).pos
  have hx16 : 16 ≤ 2 ^ (2 * n) := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : ∀ c : ℕ, c ≤ 3 → 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) =
      2 ^ (6 * n) * (c * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1))) → Odd c → False := by
    intro c hc h hco
    have he := SecA.eq_of_two_pow_mul_odd ho2 (hco.mul ho1) h
    rw [he] at h
    have h1 := Nat.eq_of_mul_eq_mul_left hpos h
    rw [show c * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) =
      (2 ^ (6 * n) - 1) * (c * (2 ^ (2 * n) - 1)) by ring] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hpos' h1
    have hmn : 2 * m = 2 * n + 2 * n := by omega
    rw [hmn, pow_add] at h2
    generalize 2 ^ (2 * n) = x at *
    have hxx : 16 * x ≤ x * x := Nat.mul_le_mul_right x hx16
    have hcx : c * (x - 1) ≤ 3 * (x - 1) := Nat.mul_le_mul_right _ hc
    generalize x * x = y at *
    omega
  rcases card_eq_of_surjective_SL3 π hπ h3 with h | h
  · rw [hSL, hG] at h
    exact key 1 (by norm_num) (by rw [h, one_mul]) odd_one
  · rw [hSL, hG] at h
    exact key 3 le_rfl (by rw [h]; ring) (by decide)

theorem card_statedSL_four : Nat.card ↥(StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem le_of_two_pow_dvd_card_L45 {m a : ℕ} (hm : m = 4 ∨ m = 5)
    (h : 2 ^ a ∣ Nat.card ↥(StatedSL m (ZMod 2))) : a ≤ 10 ∧ (m = 4 → a ≤ 6) := by
  rcases hm with rfl | rfl
  · rw [card_statedSL_four, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at h
    have := le_of_two_pow_dvd ⟨157, by norm_num⟩ h
    exact ⟨by omega, fun _ => this⟩
  · rw [card_statedSL_five, show (9999360 : ℕ) = 2 ^ 10 * 9765 by norm_num] at h
    exact ⟨le_of_two_pow_dvd ⟨4882, by norm_num⟩ h, fun h => by omega⟩

theorem not_surjective_L45_SL3 {m : ℕ} (hm : m = 4 ∨ m = 5) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (π : ↥(StatedSL m (ZMod 2)) →* Matrix.SpecialLinearGroup (Fin 3) F) :
    ¬ Function.Surjective π := by
  intro hπ
  have hd := Subgroup.card_dvd_of_surjective hπ
  rw [card_SL3_eq_pow hF] at hd
  have h2 := le_of_two_pow_dvd_card_L45 hm ((Dvd.intro _ rfl).trans hd)
  rcases hm with rfl | rfl
  · have hn2 : n = 2 := by omega
    subst hn2
    rw [card_statedSL_four] at hd
    norm_num at hd
  · rw [card_statedSL_five] at hd
    have : n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl <;> norm_num at hd

theorem not_surjective_L45_Sp4 {m : ℕ} (hm : m = 4 ∨ m = 5) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (π : ↥(StatedSL m (ZMod 2)) →* ↥(StatedSp 2 F)) : ¬ Function.Surjective π := by
  intro hπ
  have hd := Subgroup.card_dvd_of_surjective hπ
  rw [card_Sp4_eq_pow hF] at hd
  have h2 := le_of_two_pow_dvd_card_L45 hm ((Dvd.intro _ rfl).trans hd)
  rcases hm with rfl | rfl
  · omega
  · have hn2 : n = 2 := by omega
    subst hn2
    rw [card_statedSL_five] at hd
    norm_num at hd

theorem not_surjective_L45_G2 (hG2 : SecA.FactG2DerivedOrder) {m : ℕ} (hm : m = 4 ∨ m = 5)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (π : ↥(StatedSL m (ZMod 2)) →* ↥⁅quasithinG2 F, quasithinG2 F⁆) :
    ¬ Function.Surjective π := by
  intro hπ
  have hd := Subgroup.card_dvd_of_surjective hπ
  rw [card_G2_eq_pow hG2 hn hF] at hd
  have h2 := le_of_two_pow_dvd_card_L45 hm ((Dvd.intro _ rfl).trans hd)
  omega

end B51

end CFSG.Quasithin.Vol2.Ch11.SecC
