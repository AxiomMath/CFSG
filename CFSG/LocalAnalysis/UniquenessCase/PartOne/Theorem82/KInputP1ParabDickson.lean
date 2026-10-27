module

public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open scoped MatrixGroups commutatorElement
open Matrix
open CFSG.BenderSuzuki.MatrixGroups

theorem center_sl2_eq_bot (K : Type*) [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by
      linear_combination hr2 + (1 - r) * (CharP.cast_eq_zero K 2)
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  apply Subtype.ext
  rw [← hAr, hr1]
  ext i j
  simp [Matrix.scalar_apply]

theorem exists_perfect_psl2_image (K : Type*) [Field K] [Finite K] [CharP K 2]
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hH : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    ∃ P : Subgroup (PSL2MatrixGroup K), ⁅P, P⁆ = P ∧ P ≠ ⊥ ∧ Nat.card P = Nat.card H := by
  let π : Matrix.SpecialLinearGroup (Fin 2) K →* PSL2MatrixGroup K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  have hker : π.ker = ⊥ := by
    change (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).ker = ⊥
    rw [QuotientGroup.ker_mk', center_sl2_eq_bot K]
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  refine ⟨H.map π, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hH]
  · intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : π x ∈ H.map π := Subgroup.mem_map_of_mem π hx
    rw [hbot, Subgroup.mem_bot] at hx'
    have : x ∈ π.ker := MonoidHom.mem_ker.mpr hx'
    rwa [hker, Subgroup.mem_bot] at this
  · exact Subgroup.card_map_of_injective hinj

theorem three_not_dvd_two_pow_sub_one {m : ℕ} (hm : Odd m) : ¬ 3 ∣ 2 ^ m - 1 := by
  have h2 : 2 ^ m % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hm
    have h : (2 : ℕ) ^ (2 * k) ≡ 1 [MOD 3] := by
      rw [pow_mul]
      simpa using (show (2 : ℕ) ^ 2 ≡ 1 [MOD 3] by decide).pow k
    have h3 : 2 ^ (2 * k + 1) ≡ 2 [MOD 3] := by
      rw [pow_succ]
      simpa using h.mul (Nat.ModEq.refl 2)
    have hm3 : 2 % 3 = 2 := by norm_num
    rwa [Nat.ModEq, hm3] at h3
  intro hd
  have hmod : (2 ^ m - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

theorem two_pow_odd_sq_modEq_five {f : ℕ} (hf : Odd f) : (2 ^ f) ^ 2 ≡ 4 [MOD 5] := by
  obtain ⟨k, rfl⟩ := hf
  have hsq : ((2 : ℕ) ^ (2 * k + 1)) ^ 2 = 16 ^ k * 4 := by
    rw [← pow_mul, show (2 * k + 1) * 2 = 4 * k + 2 by ring, pow_add, pow_mul]
    norm_num
  rw [hsq]
  have h : (16 : ℕ) ^ k ≡ 1 [MOD 5] := by
    simpa using (show (16 : ℕ) ≡ 1 [MOD 5] by decide).pow k
  simpa using h.mul (Nat.ModEq.refl 4)

theorem not_modEq_five_one_of_odd {f : ℕ} (hf : Odd f) : ¬ (2 ^ f) ^ 2 ≡ 1 [MOD 5] := by
  intro h1
  have h4 : (2 ^ f) ^ 2 % 5 = 4 := by
    have h := two_pow_odd_sq_modEq_five hf
    rwa [Nat.ModEq, show 4 % 5 = 4 by norm_num] at h
  have h1' : (2 ^ f) ^ 2 % 5 = 1 := by
    have := h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by norm_num : 1 < 5)] at this
  omega

theorem not_modEq_sixteen_one_of_odd {f : ℕ} (hf : Odd f) : ¬ (2 ^ f) ^ 2 ≡ 1 [MOD 16] := by
  intro h1
  have hf1 : 1 ≤ f := by obtain ⟨k, hk⟩ := hf; omega
  have h2 : (2 ^ f) ^ 2 ≡ 1 [MOD 2] := h1.of_dvd (by norm_num)
  have hdvd : 2 ∣ (2 ^ f) ^ 2 :=
    (dvd_pow_self 2 (by omega : f ≠ 0)).trans (dvd_pow_self (2 ^ f) (by norm_num : 2 ≠ 0))
  have h0 : (2 ^ f) ^ 2 % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have h2' : (2 ^ f) ^ 2 % 2 = 1 := by
    have := h2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by norm_num : 1 < 2)] at this
  omega

theorem not_two_mul_dvd_of_odd {f m : ℕ} (hf : Odd f) : ¬ 2 * m ∣ f := by
  rintro ⟨j, hj⟩
  exact (Nat.not_even_iff_odd.mpr hf) ⟨m * j, by rw [hj]; ring⟩

theorem two_pow_sub_one_odd {m : ℕ} (hm : m ≠ 0) : Odd (2 ^ m - 1) := by
  have h2 : 2 ∣ 2 ^ m := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
  obtain ⟨c, hc⟩ := h2
  have hpos : 0 < 2 ^ m := by positivity
  exact ⟨c - 1, by omega⟩

theorem eq_bot_of_perfect_of_isSolvable {X : Type*} [Group X] {P : Subgroup X}
    (hperf : ⁅P, P⁆ = P) [Group.IsSolvable P] : P = ⊥ :=
  eq_bot_of_perfect_of_le_solvable le_rfl hperf

theorem not_isPerfect_of_card_eq_six {Q : Type*} [Group Q] (h : Nat.card Q = 6) :
    ¬ Group.IsPerfect Q := by
  intro hperf
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [h]; norm_num)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hN, h] at this
    omega
  have hle : commutator Q ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [key, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  have htop : Subgroup.zpowers x = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hcard := congrArg (fun H : Subgroup Q => Nat.card H) htop
  simp only [Subgroup.card_top, hN, h] at hcard
  omega

theorem isSolvable_semidirectProduct {E C : Type*} [Group E] [Group C] (φ : C →* MulAut E)
    [Group.IsSolvable E] [Group.IsSolvable C] : Group.IsSolvable (E ⋊[φ] C) :=
  Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
    SemidirectProduct.range_inl_eq_ker_rightHom.ge

theorem eq_bot_of_perfect_of_equiv_semidirect {X : Type*} [Group X] {P : Subgroup X}
    {E C : Subgroup P} (hE : IsElementaryAbelian 2 E) (hC : IsCyclic C)
    (φ : C →* MulAut E) (e : P ≃* E ⋊[φ] C) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  haveI : Group.IsSolvable ↥E := by
    haveI : IsMulCommutative ↥E := hE.toIsMulCommutative
    infer_instance
  haveI : Group.IsSolvable ↥C := by
    haveI : CommGroup ↥C := hC.commGroup
    infer_instance
  haveI : Group.IsSolvable (↥E ⋊[φ] ↥C) := isSolvable_semidirectProduct φ
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact eq_bot_of_perfect_of_isSolvable hperf

theorem eq_bot_of_perfect_of_equiv_dihedral {X : Type*} [Group X] {P : Subgroup X} {z : ℕ}
    (hz : 2 ≤ z) (e : P ≃* DihedralGroup z) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  haveI : NeZero z := ⟨by omega⟩
  haveI : Group.IsSolvable (DihedralGroup z) := CFSG.LinearGroups.isSolvable_dihedralGroup z
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact eq_bot_of_perfect_of_isSolvable hperf

theorem card_psl2_gf2_one : Nat.card (PSL2MatrixGroup (GaloisField 2 1)) = 6 := by
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear
    (GaloisField 2 1) 2 (by norm_num)]
  rw [GaloisField.card 2 1 (by norm_num)]
  norm_num

theorem card_psl2_char_two {m : ℕ} (hm : m ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField 2 m)) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear
    (GaloisField 2 m) 2 (by norm_num)]
  rw [GaloisField.card 2 m hm]
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 :=
    Nat.coprime_two_left.mpr (two_pow_sub_one_odd hm)
  rw [hg, Nat.div_one]
  norm_num

theorem two_pow_sub_one_dvd_card_psl2_char_two {m : ℕ} (hm : m ≠ 0) :
    2 ^ m - 1 ∣ Nat.card (PSL2MatrixGroup (GaloisField 2 m)) := by
  rw [card_psl2_char_two hm]
  have hd1 : 2 ^ m - 1 ∣ (2 ^ m) ^ 2 - 1 := by
    simpa using Nat.pow_sub_one_dvd_pow_sub_one (2 ^ m) (by norm_num : 1 ∣ 2)
  exact hd1.trans (dvd_mul_left ((2 ^ m) ^ 2 - 1) (2 ^ m))

theorem exists_prime_ge_five_dvd_two_pow_sub_one {m : ℕ} (hmodd : Odd m) (hm1 : m ≠ 1) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ m - 1 := by
  have hmne : m ≠ 0 := by obtain ⟨k, hk⟩ := hmodd; omega
  have hm3 : 3 ≤ m := by
    obtain ⟨k, hk⟩ := hmodd
    cases k with
    | zero => omega
    | succ k => omega
  have hne1 : 2 ^ m - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hsubodd : Odd (2 ^ m - 1) := two_pow_sub_one_odd hmne
  have hr2 : r ≠ 2 := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hsubodd) (even_iff_two_dvd.mpr (h ▸ hrdvd))
  have hr3 : r ≠ 3 := fun h => three_not_dvd_two_pow_sub_one hmodd (h ▸ hrdvd)
  have h5 : 5 ≤ r := by
    have h2 := hr.two_le
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
    omega
  exact ⟨r, hr, h5, hrdvd⟩

theorem exists_prime_of_psl2_mulEquiv {K : Type*} [Field K] [Finite K] [CharP K 2] {f m : ℕ}
    (hKf : Nat.card K = 2 ^ f) (hfodd : Odd f) (hmf : m ∣ f)
    {P : Subgroup (PSL2MatrixGroup K)} (hperf : ⁅P, P⁆ = P)
    (e : P ≃* PSL2MatrixGroup (GaloisField 2 m)) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card P ∧ r ∣ Nat.card K - 1 := by
  have hfne : f ≠ 0 := by obtain ⟨k, hk⟩ := hfodd; omega
  have hmne : m ≠ 0 := by rintro rfl; exact hfne (zero_dvd_iff.mp hmf)
  have hmodd : Odd m := by
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      obtain ⟨j, hj⟩ := he
      obtain ⟨k, hk⟩ := hmf
      refine (Nat.not_even_iff_odd.mpr hfodd) ⟨j * k, ?_⟩
      rw [hk, hj]
      ring
    · exact ho
  by_cases hm1 : m = 1
  · subst hm1
    have hcard : Nat.card P = 6 := by rw [Nat.card_congr e.toEquiv, card_psl2_gf2_one]
    exact (not_isPerfect_of_card_eq_six hcard (Subgroup.isPerfect_iff.mpr hperf)).elim
  · obtain ⟨r, hr, h5, hrdvd⟩ := exists_prime_ge_five_dvd_two_pow_sub_one hmodd hm1
    refine ⟨r, hr, h5, ?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv]
      exact hrdvd.trans (two_pow_sub_one_dvd_card_psl2_char_two hmne)
    · rw [hKf]
      exact hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmf)

theorem exists_prime_of_perfect_psl2 (K : Type*) [Field K]
    [Finite K] [CharP K 2] (f : ℕ) (hKf : Nat.card K = 2 ^ f) (hfodd : Odd f)
    (P : Subgroup (PSL2MatrixGroup K)) (hperf : ⁅P, P⁆ = P) (hne : P ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card P ∧ r ∣ Nat.card K - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list
      (F := K) (p := 2) (f := f) hKf P with
    ⟨m, hmf, hcard, hel⟩ | ⟨z, hzdiv, hcard, hcyc⟩ | ⟨z, hz2, hzdiv, ⟨e⟩⟩ |
      ⟨hA4, ⟨e⟩⟩ | ⟨hS4, ⟨e⟩⟩ | ⟨hA5, ⟨e⟩⟩ |
      ⟨m, t, hm1, hmf, ht1, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith,
        φ, hφinj, ⟨e⟩⟩ |
      ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hm2f, ⟨e⟩⟩
  · haveI : IsMulCommutative ↥P := hel.toIsMulCommutative
    exact (hne (eq_bot_of_perfect_of_isSolvable hperf)).elim
  · haveI : CommGroup ↥P := hcyc.commGroup
    exact (hne (eq_bot_of_perfect_of_isSolvable hperf)).elim
  · exact (hne (eq_bot_of_perfect_of_equiv_dihedral hz2 e hperf)).elim
  · exact (hA4.elim (by rintro ⟨k, hk⟩; omega) (Nat.not_even_iff_odd.mpr hfodd)).elim
  · exact (not_modEq_sixteen_one_of_odd hfodd hS4).elim
  · exact (hA5.elim (by norm_num) (not_modEq_five_one_of_odd hfodd)).elim
  · exact (hne (eq_bot_of_perfect_of_equiv_semidirect hEel hCcyc φ e hperf)).elim
  · exact exists_prime_of_psl2_mulEquiv hKf hfodd hmf hperf e
  · exact (not_two_mul_dvd_of_odd hfodd hm2f).elim

theorem dicksonSL2_holds : DicksonSL2 := by
  intro K _ _ _ f hKf hfodd H hH hHne
  obtain ⟨P, hperf, hne, hcard⟩ := exists_perfect_psl2_image K H hH hHne
  obtain ⟨r, hr, h5, hrP, hrK⟩ := exists_prime_of_perfect_psl2 K f hKf hfodd P hperf hne
  exact ⟨r, hr, h5, hcard ▸ hrP, hrK⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
