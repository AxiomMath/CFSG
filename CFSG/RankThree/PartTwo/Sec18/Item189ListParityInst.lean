module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListParity
public import CFSG.RankThree.PartTwo.Sec18.Item189ListBasic
public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Goldschmidt.G3a (BorelSetup)

section Instances

theorem outShape_projSL_two189 {n e m : ℕ} (hn : n = 2 ^ e * m) (hn2 : 2 ≤ n) {X : Type}
    [Group X] (ex : X ≃* projSL 2 (GaloisField 2 n)) :
    ∃ (Dd : Subgroup (Outer X)) (_ : Dd.Normal), Odd (Nat.card Dd) ∧
      IsCyclic (Outer X ⧸ Dd) ∧ Nat.card (Outer X ⧸ Dd) = 2 ^ e * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : CFSG.GH74.Uniqueness.Bender.BenderType X n 1 1 :=
    .linear n hn2 (ex.trans (Sec4.projSLEquivPSL (GaloisField 2 n)))
  obtain ⟨hcyc, hcard⟩ := hBT.outer_linear
  refine ⟨⊥, Subgroup.normal_bot, ?_, ?_, ?_⟩
  · rw [Subgroup.card_bot]
    exact odd_one
  · exact (QuotientGroup.quotientBot (G := Outer X)).isCyclic.mpr hcyc
  · rw [Nat.card_congr (QuotientGroup.quotientBot (G := Outer X)).toEquiv]
    exact hcard.trans hn

theorem outShape_projSU_three189 {n e m : ℕ} (hn : n = 2 ^ e * m) (hn2 : 2 ≤ n) {X : Type}
    [Group X] (ex : X ≃* projSU 3 2 n) :
    ∃ (Dd : Subgroup (Outer X)) (_ : Dd.Normal), Odd (Nat.card Dd) ∧
      IsCyclic (Outer X ⧸ Dd) ∧ Nat.card (Outer X ⧸ Dd) = 2 ^ (e + 1) * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 ^ n ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  obtain ⟨e'⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn2
    (statedClassicalModel_psu189 (by omega) hq ex)
  have hBT : CFSG.GH74.Uniqueness.Bender.BenderType X n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    .unitary n hn2 (e'.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n).symm))
  obtain ⟨Dd, hnorm, -, hd, hq', hcard⟩ := hBT.outer_unitary
  refine ⟨Dd, hnorm, ?_, hq', ?_⟩
  · rw [hd]
    exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  · rw [hcard, hn]
    ring

theorem two_pow_even_mod_three189 {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨j, rfl⟩ := hn
  rw [← two_mul, pow_mul]
  norm_num [Nat.pow_mod]

theorem borelOrderThree_projSL_two189 {X : Type} [Group X]
    [Finite X] {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) (ex : X ≃* projSL 2 (GaloisField 2 n)) :
    BorelOrderThree189 X ∧ Nat.card (Sylow 2 X) % 3 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : CFSG.Open.fusionIsBenderGroup X := fusionIsBenderGroup_of_projSL_two hn2 ex
  have hpsl := ex.trans (Sec4.projSLEquivPSL (GaloisField 2 n))
  have hq3 := two_pow_even_mod_three189 hn
  have hpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  refine ⟨fun T => ?_, ?_⟩
  · obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    obtain ⟨-, hDcard, hZ⟩ := hD.orders_psl2 hn2 hpsl
    refine ⟨D, hD, ?_⟩
    have hmul := hD.card_eq_mul
    rw [hDcard, hZ] at hmul
    have hk : Nat.card (BorelSetup.kerD D T) = 1 := by
      have : (2 ^ n - 1) * Nat.card (BorelSetup.kerD D T) = (2 ^ n - 1) * 1 := by
        rw [← hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    rw [hk]
    decide
  · obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
    obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    obtain ⟨hT, -, -⟩ := hD.orders_psl2 hn2 hpsl
    rw [hD.card, hT]
    omega

theorem borelOrderThree_projSU_three189 {X : Type} [Group X]
    [Finite X] {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) (ex : X ≃* projSU 3 2 n) :
    BorelOrderThree189 X ∧ Nat.card (Sylow 2 X) % 3 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : CFSG.Open.fusionIsBenderGroup X := fusionIsBenderGroup_of_projSU_three hn2 ex
  have hq : 2 ^ n ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  obtain ⟨e'⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn2
    (statedClassicalModel_psu189 (by omega) hq ex)
  have hq3 := two_pow_even_mod_three189 hn
  have hpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  refine ⟨fun T => ?_, ?_⟩
  · obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    obtain ⟨hZ, -, hDcard⟩ := hD.orders_psu3 hn2 e'
    refine ⟨D, hD, ?_⟩
    have hmul := hD.card_eq_mul
    rw [hDcard, hZ, hgcd, Nat.div_one] at hmul
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      zify [h1, show 1 ≤ 2 ^ n by omega]
      ring
    have hk : Nat.card (BorelSetup.kerD D T) = 2 ^ n + 1 := by
      have : (2 ^ n - 1) * Nat.card (BorelSetup.kerD D T) = (2 ^ n - 1) * (2 ^ n + 1) := by
        rw [← hmul, hsq]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    rw [hk]
    omega
  · obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
    obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    obtain ⟨-, hT, -⟩ := hD.orders_psu3 hn2 e'
    rw [hD.card, hT]
    have : (2 ^ n) ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega

end Instances

section Transport

theorem mem_normalizer_map_subtype189 {Y : Type} [Group Y] {X : Subgroup Y} {x : Y} (hx : x ∈ X)
    (U : Subgroup ↥X) :
    x ∈ Subgroup.normalizer ((U.map X.subtype : Subgroup Y) : Set Y) ↔
      (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalizer (U : Set ↥X) := by
  have hle : U.map X.subtype ≤ X := Subgroup.map_subtype_le U
  have e : (U.map X.subtype).subgroupOf X = U :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective U
  have h1 : (⟨x, hx⟩ : ↥X) ∈
      (Subgroup.normalizer ((U.map X.subtype : Subgroup Y) : Set Y)).subgroupOf X ↔
      x ∈ Subgroup.normalizer ((U.map X.subtype : Subgroup Y) : Set Y) := Subgroup.mem_subgroupOf
  rw [← h1, Subgroup.subgroupOf_normalizer_eq hle, e]

theorem exists_typeLevel_swap189 {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y} [X.Normal]
    {x σ : Y} (hx : x ∈ X) (hσx : σ * x = x * σ) {U U' : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) (hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' X)
    (hswap : U.map (MulAut.conj σ).toMonoidHom = U') :
    ∃ U₀ U₀' : Sylow 2 ↥X, (U₀ : Subgroup ↥X).map X.subtype = U ∧
      (U₀' : Subgroup ↥X).map X.subtype = U' ∧
      (MulAut.conjNormal σ : MulAut ↥X) ⟨x, hx⟩ = ⟨x, hx⟩ ∧
      (MulAut.conjNormal σ : MulAut ↥X) • U₀ = U₀' := by
  obtain ⟨U₀, hU₀⟩ := hU
  obtain ⟨U₀', hU₀'⟩ := hU'
  refine ⟨U₀, U₀', hU₀, hU₀', ?_, ?_⟩
  · apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    calc σ * x * σ⁻¹ = x * σ * σ⁻¹ := by rw [hσx]
      _ = x := by group
  · apply Sylow.ext
    ext u
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_smul_iff]
    have h1 : ∀ w : ↥X, w ∈ (U₀ : Subgroup ↥X) ↔ (w : Y) ∈ U := fun w => by
      rw [← hU₀]
      exact (Subgroup.mem_map_iff_mem X.subtype_injective).symm
    have h2 : ∀ w : ↥X, w ∈ (U₀' : Subgroup ↥X) ↔ (w : Y) ∈ U' := fun w => by
      rw [← hU₀']
      exact (Subgroup.mem_map_iff_mem X.subtype_injective).symm
    rw [h1, h2, ← hswap, Subgroup.mem_map_equiv]
    have : (((MulAut.conjNormal σ : MulAut ↥X)⁻¹ u : ↥X) : Y) = (MulAut.conj σ).symm (u : Y) := by
      rw [← map_inv, MulAut.conjNormal_apply, MulAut.conj_symm_apply]
      simp
    rw [this]

end Transport

theorem uniqueSylowOver189_of_isBender {Y : Type} [Group Y]
    [Finite Y] {X : Subgroup Y} (hX : CFSG.Open.fusionIsBenderGroup ↥X) :
    UniqueSylowOver189 X := by
  intro R hRX hR hR1
  have hR₀ : IsPGroup 2 (R.subgroupOf X) := hR.comap_subtype
  have hR₁ : R.subgroupOf X ≠ ⊥ := by
    intro h
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRX hr⟩ : ↥X) ∈ R.subgroupOf X := hr
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨U₀, hU₀, huniq⟩ := exists_unique_sylow189
    (fun T => CFSG.Goldschmidt.G3a.exists_borelSetup hX T) hR₀ hR₁
  have hmem : ∀ V₀ : Sylow 2 ↥X, R ≤ V₀.map X.subtype ↔ R.subgroupOf X ≤ V₀ := by
    intro V₀
    constructor
    · intro h u hu
      have := h hu
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp this
      have : w = u := Subtype.ext hwu
      rwa [← this]
    · intro h r hr
      exact ⟨⟨r, hRX hr⟩, h hr, rfl⟩
  refine ⟨U₀.map X.subtype, ⟨⟨U₀, rfl⟩, (hmem U₀).mpr hU₀⟩, ?_⟩
  rintro V ⟨⟨V₀, rfl⟩, hRV⟩
  rw [huniq V₀ ((hmem V₀).mp hRV)]

section Assembly

theorem exists_fixed_pair_of_borel189 {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y}
    (hB : BorelOrderThree189 ↥X) (hcard : Nat.card (Sylow 2 ↥X) % 3 = 2) {x : Y} (hx : x ∈ X)
    (hx3 : orderOf x = 3) :
    ∃ U U' : Subgroup Y, U ≠ U' ∧ CFSG.ABGLocalTools.IsSylowOf 2 U X ∧
      CFSG.ABGLocalTools.IsSylowOf 2 U' X ∧ x ∈ Subgroup.normalizer (U : Set Y) ∧
      x ∈ Subgroup.normalizer (U' : Set Y) ∧
      ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
        x ∈ Subgroup.normalizer (V : Set Y) → V = U ∨ V = U' := by
  have hx3' : orderOf (⟨x, hx⟩ : ↥X) = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  obtain ⟨U₀, U₀', hne, hxU, hxU', hfix⟩ := exists_fixed_pair189 hB hx3' hcard
  refine ⟨U₀.map X.subtype, U₀'.map X.subtype, ?_, ⟨U₀, rfl⟩, ⟨U₀', rfl⟩,
    (mem_normalizer_map_subtype189 hx _).mpr hxU, (mem_normalizer_map_subtype189 hx _).mpr hxU',
    ?_⟩
  · intro h
    exact hne (Sylow.ext (Subgroup.map_injective X.subtype_injective h))
  · rintro V ⟨V₀, rfl⟩ hV
    rcases hfix V₀ ((mem_normalizer_map_subtype189 hx _).mp hV) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem two_pow_dvd_orderOf_of_swap_of_borel189 {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup Y} [X.Normal] (hB : BorelOrderThree189 ↥X)
    (hcard : Nat.card (Sylow 2 ↥X) % 3 = 2) {Z : Type} [Group Z] [IsCyclic Z]
    (Λ : MulAut ↥X →* Z) (hΛ : Function.Surjective Λ) {k m : ℕ} (hm : Odd m)
    (hZ : Nat.card Z = 2 ^ k * m) (hinn : ∀ g : ↥X, Λ (MulAut.conj g) = 1)
    (hker : ∀ δ : MulAut ↥X, Λ δ = 1 → ∃ r : ℕ, Odd r ∧ ∃ g : ↥X, δ ^ r = MulAut.conj g)
    {x σ : Y} (hx : x ∈ X) (hx3 : orderOf x = 3) (hσx : σ * x = x * σ) {U U' : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) (hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' X)
    (hne : U ≠ U') (hxU : x ∈ Subgroup.normalizer (U : Set Y))
    (hxU' : x ∈ Subgroup.normalizer (U' : Set Y))
    (hswap : U.map (MulAut.conj σ).toMonoidHom = U') : 2 ^ k ∣ orderOf σ := by
  obtain ⟨U₀, U₀', rfl, rfl, hθx, hθU⟩ := exists_typeLevel_swap189 hx hσx hU hU' hswap
  have hx3' : orderOf (⟨x, hx⟩ : ↥X) = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  have hne₀ : U₀ ≠ U₀' := fun h => hne (by rw [h])
  have h := two_pow_dvd_orderOf_of_swap189 hB Λ hΛ hm hZ hinn hker hx3' hcard hne₀
    ((mem_normalizer_map_subtype189 hx _).mp hxU) ((mem_normalizer_map_subtype189 hx _).mp hxU')
    hθx hθU
  exact h.trans ((orderOf_map_dvd (Λ.comp (MulAut.conjNormal (H := X))) σ))

end Assembly

end CFSG.RankThree.PartTwo.Sec18
