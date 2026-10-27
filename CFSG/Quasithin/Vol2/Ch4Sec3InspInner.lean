module

public import CFSG.Quasithin.Vol2.KGNatSL3Lev
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.Quasithin.H13.Ch4.InspInner

open CFSG.Open
open CFSG.Quasithin
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_of_mem_zpowers {K : Subgroup X} {x : X} (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) {b : X} (hb : b ∈ Subgroup.zpowers x) :
    b ∈ Subgroup.normalizer (K : Set X) ∧ ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hON : Subgroup.normalizer (K : Set X) ≤
      Subgroup.normalizer ((pCoreOf 2 K : Subgroup X) : Set X) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  let C : Subgroup X :=
    { carrier := {g | g ∈ Subgroup.normalizer (K : Set X) ∧
        ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K}
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, fun k hk => ?_⟩
        have e : a * b * k * (a * b)⁻¹ * k⁻¹ =
            (a * (b * k * b⁻¹ * k⁻¹) * a⁻¹) * (a * k * a⁻¹ * k⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hON haN) _).mp (hb k hk))
          (ha k hk)
      one_mem' := ⟨Subgroup.one_mem _, fun k hk => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨Subgroup.inv_mem _ haN, fun k hk => ?_⟩
        have hk' : a⁻¹ * k * a⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) k).mp hk
        have h1 := Subgroup.inv_mem _ (ha _ hk')
        have e : (a * (a⁻¹ * k * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * k * a⁻¹⁻¹)⁻¹)⁻¹ =
            a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ := by group
        rwa [e] at h1 }
  have hxC : x ∈ C := ⟨hxN, hxK⟩
  exact (Subgroup.zpowers_le.mpr hxC) hb

theorem two_le_pRank {S K : Subgroup X} (hKS : K ≤ S) {F : Type} [Field F] [Fintype F]
    [CharP F 2] {χ : ↥K →* SL(2, F)} (hχ : Function.Surjective χ) (hker : IsPGroup 2 ↥χ.ker)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Fintype.card F - 1) {x : X} (hxS : x ∈ S)
    (hxo : orderOf x = p) (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    2 ≤ CFSG.Open.pRank p S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemO : ∀ k : ↥K, (k : X) ∈ pCoreOf 2 K ↔ k ∈ CFSG.Open.pCore 2 ↥K := fun k =>
    ⟨fun ⟨k', hk', e⟩ => by rwa [Subtype.ext e] at hk', fun hk => ⟨k, hk, rfl⟩⟩
  have hO : ∀ k : ↥K, k ∈ CFSG.Open.pCore 2 ↥K → χ k = 1 := by
    have hN : ((CFSG.Open.pCore 2 ↥K).map χ).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2 : (CFSG.Open.pCore 2 ↥K).Normal).map _ hχ
    have h2 : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥K).map χ) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥K)).map _
    have hbot := Vol2.KGNat.eq_bot_of_normal_isPGroup_SL2 h2
    intro k hk
    have hmem : χ k ∈ (CFSG.Open.pCore 2 ↥K).map χ := ⟨k, hk, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  have hxN : x ∈ Subgroup.normalizer (K : Set X) :=
    CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun k hk => by
      have e : x * k * x⁻¹ = (x * k * x⁻¹ * k⁻¹) * k := by group
      rw [e]
      exact K.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 K (hxK k hk)) hk
  have hpow := fun {b : X} (hb : b ∈ Subgroup.zpowers x) => mem_of_mem_zpowers hxN hxK hb
  have hcen : ∀ b : ↥K, (∀ k ∈ K, (b : X) * k * (b : X)⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → χ b = 1 := by
    intro b hb
    have hz : χ b ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨k, rfl⟩ := hχ w
      have h1 : χ (b * k * b⁻¹ * k⁻¹) = 1 := by
        apply hO
        rw [← hmemO]
        exact hb k k.2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ k * χ b = χ b * χ k * (χ b)⁻¹ * (χ k)⁻¹ * (χ k * χ b) := by
            rw [h1, one_mul]
        _ = χ b * χ k := by group
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have hpu : p ∣ Fintype.card Fˣ := by rwa [Fintype.card_units]
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card p hpu
  let d : SL(2, F) := ⟨Matrix.diagonal ![(l : F), ((l⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp⟩
  have hl1 : (l : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hl, pow_orderOf_eq_one, Units.val_one]
  have hdp : d ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change (Matrix.diagonal ![(l : F), ((l⁻¹ : Fˣ) : F)]) ^ p = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hl1]
  have hd1 : d ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [d, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h1
    have : l = 1 := Units.ext h1
    rw [this, orderOf_one] at hl
    exact hp.one_lt.ne' hl.symm
  have hdo : orderOf d = p := orderOf_eq_prime hdp hd1
  obtain ⟨k₀, hk₀⟩ := hχ d
  have hk₀p : χ (k₀ ^ p) = 1 := by rw [map_pow, hk₀, hdp]
  obtain ⟨b, hb⟩ := hker ⟨k₀ ^ p, hk₀p⟩
  have hb' : (k₀ ^ p) ^ 2 ^ b = 1 := congrArg Subtype.val hb
  set k₁ := k₀ ^ 2 ^ b with hk₁
  have hcopd : Nat.Coprime p (2 ^ b) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hχk₁ : orderOf (χ k₁) = p := by
    rw [hk₁, map_pow, hk₀, Nat.Coprime.orderOf_pow (by rw [hdo]; exact hcopd), hdo]
  have hsub : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set X) :=
    Subgroup.zpowers_le.mpr hxN
  have : Subgroup.Normalizes (Subgroup.zpowers x) K := ⟨hsub⟩
  have : (CFSG.Open.pCore 2 ↥K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hinv : IsInvariant ↥(Subgroup.zpowers x) ↥K (CFSG.Open.pCore 2 ↥K) := by
    have key : ∀ (a : ↥(Subgroup.zpowers x)) (g : ↥K), g ∈ CFSG.Open.pCore 2 ↥K →
        a • g ∈ CFSG.Open.pCore 2 ↥K := by
      intro a g hg
      rw [← hmemO, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have hON : Subgroup.normalizer (K : Set X) ≤
          Subgroup.normalizer ((pCoreOf 2 K : Subgroup X) : Set X) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
      exact (Subgroup.mem_normalizer_iff.mp (hON (hsub a.2)) _).mp ((hmemO g).mpr hg)
    exact ⟨fun a g => ⟨fun hg => key a g hg, fun hag => by
      have := key a⁻¹ _ hag
      rwa [inv_smul_smul] at this⟩⟩
  have hsolv : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥K) := by
    have := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥K)).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(CFSG.Open.pCore 2 ↥K)) := by
    obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥K))
    rw [Nat.card_zpowers, hxo, hc]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨c, hcfix, hck⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    (CFSG.Open.pCore 2 ↥K) hinv hsolv hcop k₁ (fun a => by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have h1 := (hpow a.2).2 k₁ k₁.2
      rw [← hmemO]
      have e : (((k₁⁻¹ * (a • k₁) : ↥K)) : X) =
          (k₁ : X)⁻¹ * ((a : X) * k₁ * (a : X)⁻¹ * (k₁ : X)⁻¹) * k₁ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        group
      rw [e]
      have hON : Subgroup.normalizer (K : Set X) ≤
          Subgroup.normalizer ((pCoreOf 2 K : Subgroup X) : Set X) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
      have hk₁N : ((k₁ : X))⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup X) : Set X) :=
        hON (Subgroup.inv_mem _ (Subgroup.le_normalizer k₁.2))
      have := (Subgroup.mem_normalizer_iff.mp hk₁N _).mp h1
      simpa using this)
  have hcx : (x : X) * c = c * x := by
    have h1 : (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) • c = c := hcfix _
    have h2 := congrArg (fun w : ↥K => (w : X)) h1
    simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h2
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h2]
  have hχc : χ c = χ k₁ := by
    have h1 := hO _ hck
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hcp : χ (c ^ p) = 1 := by rw [map_pow, hχc, ← hχk₁, pow_orderOf_eq_one]
  obtain ⟨e, he⟩ := hker ⟨c ^ p, hcp⟩
  have he' : (c ^ p) ^ 2 ^ e = 1 := congrArg Subtype.val he
  set c₂ := c ^ 2 ^ e with hc₂
  have hcope : Nat.Coprime p (2 ^ e) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hχc₂ : orderOf (χ c₂) = p := by
    rw [hc₂, map_pow, Nat.Coprime.orderOf_pow (by rw [hχc, hχk₁]; exact hcope), hχc, hχk₁]
  have hc₂p : c₂ ^ p = 1 := by
    rw [hc₂, ← pow_mul, mul_comm, pow_mul, he']
  set e₁ : ↥S := ⟨x, hxS⟩ with he₁
  set e₂ : ↥S := ⟨c₂, hKS c₂.2⟩ with he₂
  have hcomm : Commute e₁ e₂ := by
    apply Subtype.ext
    change x * ((c ^ 2 ^ e : ↥K) : X) = ((c ^ 2 ^ e : ↥K) : X) * x
    rw [SubgroupClass.coe_pow]
    exact (Commute.pow_right hcx _)
  have h₁ : e₁ ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    change x ^ p = 1
    rw [← hxo, pow_orderOf_eq_one])
  have h₂ : e₂ ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    change ((c₂ : X)) ^ p = 1
    rw [← SubgroupClass.coe_pow, hc₂p, OneMemClass.coe_one])
  have hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j hij
    have hij' : x ^ i = ((c₂ ^ (-j) : ↥K) : X) := by
      have := congrArg (fun w : ↥S => (w : X)) hij
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow, OneMemClass.coe_one] at this
      rw [SubgroupClass.coe_zpow, zpow_neg]
      exact eq_inv_of_mul_eq_one_left this
    have hxiK : x ^ i ∈ K := by rw [hij']; exact (c₂ ^ (-j)).2
    have hxi := hcen ⟨x ^ i, hxiK⟩ (hpow (Subgroup.zpow_mem_zpowers x i)).2
    have hj : (p : ℤ) ∣ j := by
      have h1 : χ (c₂ ^ (-j)) = 1 := by
        have : (⟨x ^ i, hxiK⟩ : ↥K) = c₂ ^ (-j) := Subtype.ext hij'
        rw [← this]
        exact hxi
      rw [map_zpow, zpow_neg, inv_eq_one] at h1
      have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hχc₂] at h2
    refine ⟨?_, hj⟩
    have hc₂j : c₂ ^ (-j) = 1 := by
      obtain ⟨t, rfl⟩ := hj
      rw [neg_mul_eq_mul_neg, zpow_mul, zpow_natCast, hc₂p, one_zpow]
    rw [hc₂j, OneMemClass.coe_one] at hij'
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr hij'
    rwa [hxo] at h2
  have h := CFSG.RankThree.PartOne.two_le_pRank_of_two_elements hp hcomm h₁ h₂ hi
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype] at h

theorem eq_three {S K : Subgroup X} (hKS : K ≤ S) {n : ℕ} {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ n) {χ : ↥K →* SL(2, F)} (hχ : Function.Surjective χ)
    (hker : IsPGroup 2 ↥χ.ker)
    (hcond : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
      CFSG.Open.pRank p S ≤ 1 ∨
        (p = 3 ∧ ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q ↥S))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) {x : X} (hxS : x ∈ S)
    (hxo : orderOf x = p) (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    p = 3 ∧ ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
      IsPSLEps3q s q ↥S := by
  rcases hcond p hp hp2 hpn with h | h
  · have h2 := two_le_pRank hKS hχ hker hp hp2 (by rwa [hF]) hxS hxo hxK
    omega
  · exact h

theorem exists_prime_pow {K : Subgroup X} {n : ℕ} (hn : 1 ≤ n) {x : X} (hx1 : x ≠ 1)
    (hxn : x ^ (2 ^ n - 1) = 1) (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧ ∃ x' ∈ Subgroup.zpowers x, orderOf x' = p ∧
      ∀ k ∈ K, x' * k * x'⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd hne1
  have hord : orderOf x ∣ 2 ^ n - 1 := orderOf_dvd_of_pow_eq_one hxn
  have hpn : p ∣ 2 ^ n - 1 := hpx.trans hord
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨p, hp, hp2, hpn, x ^ (orderOf x / p), Subgroup.npow_mem_zpowers x _,
    orderOf_pow_orderOf_div hpos hpx, fun k hk => ?_⟩
  exact (mem_of_mem_zpowers hxN hxK (Subgroup.npow_mem_zpowers x _)).2 k hk

end CFSG.Quasithin.H13.Ch4.InspInner
