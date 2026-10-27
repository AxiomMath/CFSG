module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312KG
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.GH74.KGroups.L3EpsUniSyl

public section

namespace CFSG.Quasithin.H13.InspA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Pointwise

structure ExclInputs : Prop where
  m12Card : Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 = 95040
  szThree : ∀ (X : Type) [Group X] (n : ℕ), CFSG.Blueprint.SuzukiModel X 2 n → ¬ 3 ∣ Nat.card X

section Quot

variable {P B W S : Type*} [Group P] [Group B] [Group W] [Group S]

theorem exists_surjective_of_solvable_kernels (α : P →* B) (hα : Function.Surjective α)
    (hαk : Group.IsSolvable α.ker) (β : P →* W) (hβ : Function.Surjective β) [IsSimpleGroup W]
    (hW : ∃ a b : W, a * b ≠ b * a) (γ : B →* S) (hγ : Function.Surjective γ)
    (hγk : Group.IsSolvable γ.ker) : ∃ g : S →* W, Function.Surjective g := by
  set δ := γ.comp α with hδdef
  have hδ : Function.Surjective δ := hγ.comp hα
  have hle : δ.ker ≤ β.ker := ker_le_ker_of_isSolvable β hβ hW δ (isSolvable_ker_comp α hαk γ hγk)
  refine ⟨(QuotientGroup.lift δ.ker β hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective δ hδ).symm.toMonoidHom, fun w => ?_⟩
  obtain ⟨x, rfl⟩ := hβ w
  refine ⟨δ x, ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective δ hδ).symm (δ x) =
      (QuotientGroup.mk x : P ⧸ δ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1]
  rfl

theorem card_dvd_of_solvable_kernels [Finite S] (α : P →* B) (hα : Function.Surjective α)
    (hαk : Group.IsSolvable α.ker) (β : P →* W) (hβ : Function.Surjective β) [IsSimpleGroup W]
    (hW : ∃ a b : W, a * b ≠ b * a) (γ : B →* S) (hγ : Function.Surjective γ)
    (hγk : Group.IsSolvable γ.ker) : Nat.card W ∣ Nat.card S := by
  obtain ⟨g, hg⟩ := exists_surjective_of_solvable_kernels α hα hαk β hβ hW γ hγ hγk
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

end Quot

section TwoParts

theorem ordProj_two_eq_two {n : ℕ} (h : n % 4 = 2) : ordProj[2] n = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (2 * k + 1) := ⟨n / 4, by omega⟩
  rw [Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by omega), pow_one]

theorem ordProj_two_of_eq_mul {n k m : ℕ} (h : n = 2 ^ k * m) (hm : m % 2 = 1) :
    ordProj[2] n = 2 ^ k := by
  rw [h, Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by omega), add_zero]

theorem ordProj_two_eq_four {n : ℕ} (h : n % 8 = 4) : ordProj[2] n = 4 :=
  ordProj_two_of_eq_mul (k := 2) (m := n / 4) (by omega) (by omega)

theorem ordProj_two_eq_eight {n : ℕ} (h : n % 16 = 8) : ordProj[2] n = 8 :=
  ordProj_two_of_eq_mul (k := 3) (m := n / 8) (by omega) (by omega)

theorem ordProj_two_card_L2_of_mod_eight {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ordProj[2] (q * (q ^ 2 - 1) / 2) = 4 := by
  apply ordProj_two_eq_four
  have h16 : q ^ 2 % 16 = 9 := by
    have : q % 16 = 3 ∨ q % 16 = 11 ∨ q % 16 = 5 ∨ q % 16 = 13 := by omega
    rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
  have h1 : 1 ≤ q ^ 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k, q ^ 2 - 1 = 16 * k + 8 := ⟨(q ^ 2 - 1) / 16, by omega⟩
  rw [hk]
  have hq2 : q % 2 = 1 := by omega
  obtain ⟨j, rfl⟩ : ∃ j, q = 2 * j + 1 := ⟨q / 2, by omega⟩
  have e : (2 * j + 1) * (16 * k + 8) / 2 = (2 * j + 1) * (8 * k + 4) := by
    rw [show (2 * j + 1) * (16 * k + 8) = 2 * ((2 * j + 1) * (8 * k + 4)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [e]
  have : (2 * j + 1) * (8 * k + 4) = 8 * (2 * j * k + k + j) + 4 := by ring
  omega

theorem ordProj_two_card_L2_of_sq_mod {q : ℕ} (hq : q ^ 2 % 32 = 17) :
    ordProj[2] (q * (q ^ 2 - 1) / 2) = 8 := by
  apply ordProj_two_eq_eight
  have h1 : 1 ≤ q ^ 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k, q ^ 2 - 1 = 32 * k + 16 := ⟨(q ^ 2 - 1) / 32, by omega⟩
  have hq2 : q % 2 = 1 := by
    by_contra h
    have : q % 2 = 0 := by omega
    have : q ^ 2 % 2 = 0 := by simp [Nat.pow_mod, this]
    omega
  rw [hk]
  obtain ⟨j, rfl⟩ : ∃ j, q = 2 * j + 1 := ⟨q / 2, by omega⟩
  have e : (2 * j + 1) * (32 * k + 16) / 2 = (2 * j + 1) * (16 * k + 8) := by
    rw [show (2 * j + 1) * (32 * k + 16) = 2 * ((2 * j + 1) * (16 * k + 8)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [e]
  have : (2 * j + 1) * (16 * k + 8) = 16 * (2 * j * k + k + j) + 8 := by ring
  omega

theorem sq_mod_of_mod_sixteen {q : ℕ} (hq : q % 16 = 7 ∨ q % 16 = 9) : q ^ 2 % 32 = 17 := by
  have : q % 32 = 7 ∨ q % 32 = 23 ∨ q % 32 = 9 ∨ q % 32 = 25 := by omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

theorem sq_sq_mod_of_mod_eight {p : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) : (p ^ 2) ^ 2 % 32 = 17 := by
  have : p % 32 = 3 ∨ p % 32 = 11 ∨ p % 32 = 19 ∨ p % 32 = 27 ∨ p % 32 = 5 ∨ p % 32 = 13 ∨
      p % 32 = 21 ∨ p % 32 = 29 := by omega
  rw [← pow_mul]
  rcases this with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, h]

theorem ordProj_two_card_L2_even (n : ℕ) (hn : 1 ≤ n) :
    ordProj[2] (2 ^ n * ((2 ^ n) ^ 2 - 1)) = 2 ^ n := by
  refine ordProj_two_of_eq_mul rfl ?_
  have : 2 ≤ (2 ^ n) ^ 2 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    nlinarith
  have h2 : (2 ^ n) ^ 2 % 2 = 0 := by
    rw [Nat.pow_mod]
    simp [Nat.pow_mod, show n ≠ 0 by omega]
  omega

end TwoParts

section Orders

variable {W : Type} [Group W]

theorem card_of_isL2_odd {p e : ℕ} (hp2 : p ≠ 2) (h : F6.IsL2 p e W) :
    Nat.card W = p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound W 2 p e h).1
  have hp := h.1.1
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [hb, hg, show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton]
  norm_num

theorem card_of_isPSL_two_two {n : ℕ} (h : IsPSL 2 2 n W) :
    Nat.card W = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound W 2 2 n h).1
  have hn : 1 ≤ n := h.1.2.1
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have : (2 ^ n - 1) % 2 = 1 := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
      have h2 : 2 ^ n % 2 = 0 := by simp [Nat.pow_mod, show n ≠ 0 by omega]
      omega
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr this)
  rw [hb, hg, show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton]
  norm_num

end Orders

structure F618Orders (W : Type) [Group W] : Prop where
  three_dvd : 3 ∣ Nat.card W
  card_pos : 0 < Nat.card W
  not_dvd : ¬ Nat.card W ∣ 120

section F618

variable {W : Type} [Group W]

theorem f618L2_props {p e : ℕ} (hp : p.Prime) (he1 : 1 ≤ e) (he2 : e ≤ 2) (hL : F6.IsL2 p e W)
    (hc : (e = 1 ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∨ p ^ e % 16 = 7 ∨ p ^ e % 16 = 9 ∨
      (e = 2 ∧ (p % 8 = 3 ∨ p % 8 = 5))) :
    p ≠ 2 ∧ 7 ≤ p ^ e ∧ Nat.card W = p ^ e * ((p ^ e) ^ 2 - 1) / 2 ∧
      (ordProj[2] (Nat.card W) = 4 ∨ ordProj[2] (Nat.card W) = 8) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hc with ⟨-, h | h⟩ | h | h | ⟨-, h | h⟩ <;> norm_num at h
    · rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl <;> norm_num at h
    · rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl <;> norm_num at h
  have hcard := card_of_isL2_odd hp2 hL
  refine ⟨hp2, ?_, hcard, ?_⟩
  · rcases hc with ⟨rfl, h⟩ | h | h | ⟨rfl, h⟩
    · rw [pow_one]; omega
    · omega
    · omega
    · have : 3 ≤ p := by omega
      nlinarith
  · rw [hcard]
    rcases hc with ⟨rfl, h⟩ | h | h | ⟨rfl, h⟩
    · left
      rw [pow_one]
      exact ordProj_two_card_L2_of_mod_eight (by omega)
    · exact Or.inr (ordProj_two_card_L2_of_sq_mod (sq_mod_of_mod_sixteen (Or.inl h)))
    · exact Or.inr (ordProj_two_card_L2_of_sq_mod (sq_mod_of_mod_sixteen (Or.inr h)))
    · exact Or.inr (ordProj_two_card_L2_of_sq_mod (sq_sq_mod_of_mod_eight h))

theorem le_card_L2 {q : ℕ} (hq : 7 ≤ q) : 168 ≤ q * (q ^ 2 - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : 48 ≤ q ^ 2 - 1 := by
    have : 49 ≤ q ^ 2 := by nlinarith
    omega
  calc 168 * 2 = 7 * 48 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq h1

theorem f618L3_props [IsSimpleGroup W] {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hS : F6.IsSLEps3 p W) :
    ((p % 4 = 1 ∧ IsPSL 3 p 1 W) ∨ (p % 4 = 3 ∧ IsPSU 3 p 1 W)) ∧ 3 ∣ Nat.card W ∧
      ordProj[2] (Nat.card W) = 32 := by
  have hs : IsSimpleGroup W := inferInstance
  obtain ⟨hp, K, _, _, hK⟩ := hS
  have hp2 : p ≠ 2 := by omega
  have hmodel : (p % 4 = 1 ∧ IsPSL 3 p 1 W) ∨ (p % 4 = 3 ∧ IsPSU 3 p 1 W) := by
    rcases hK with ⟨h1, h2, hf | hf⟩ | ⟨h1, h2, hf | hf⟩
    · obtain ⟨e⟩ := hf
      exact Or.inl ⟨h1, L3Eps.isPSL_of_mulEquiv_statedSL hp h2 hs e⟩
    · exact Or.inl ⟨h1, ⟨hp, le_rfl, by norm_num, by simp, by simp⟩, K, inferInstance,
        inferInstance, by rw [pow_one, h2], hf⟩
    · obtain ⟨e⟩ := hf
      exact Or.inr ⟨h1, L3Eps.isPSU_of_mulEquiv_statedSU hp (by omega) h2 hs e⟩
    · obtain ⟨f⟩ := hf
      refine Or.inr ⟨h1, ⟨hp, le_rfl, le_rfl, ?_⟩, K, inferInstance, inferInstance,
        by rw [pow_one, h2], ⟨f.trans (L3Eps.statedProjSUCongr (pow_one p).symm)⟩⟩
      simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
      omega
  refine ⟨hmodel, ?_, ?_⟩
  · rcases hmodel with ⟨-, h⟩ | ⟨-, h⟩
    · exact F134.three_dvd_card_of_statedPSL_three h
    · exact F134.three_dvd_card_of_statedPSU_three h
  · rcases hmodel with ⟨h4, h⟩ | ⟨h4, h⟩
    · rw [(CFSG.GH74.KGroups.L3Eps.lin_model_card hp2 h).2, pow_one,
        ordProj_two_eq_four (n := p - 1) (by omega), ordProj_two_eq_two (n := p + 1) (by omega)]
      norm_num
    · rw [(CFSG.GH74.KGroups.L3Eps.uni_model_card hp2 h).2, pow_one,
        ordProj_two_eq_two (n := p - 1) (by omega), ordProj_two_eq_four (n := p + 1) (by omega)]
      norm_num

theorem f618Orders (hE : ExclInputs) [IsSimpleGroup W] (h : F618SimpleType W) : F618Orders W := by
  rcases h with (⟨p, e, hp, he1, he2, hL, hc⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | hM) | ⟨p, hp8, hS⟩
  · obtain ⟨hp2, hq7, hcard, -⟩ := f618L2_props hp he1 he2 hL hc
    have h168 := le_card_L2 hq7
    rw [← hcard] at h168
    refine ⟨F134.three_dvd_card_of_statedPSL_two hL, by omega, fun hd => ?_⟩
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  · have hc : Nat.card W = 360 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    refine ⟨by rw [hc]; norm_num, by rw [hc]; norm_num, by rw [hc]; norm_num⟩
  · have hc : Nat.card W = 2520 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    refine ⟨by rw [hc]; norm_num, by rw [hc]; norm_num, by rw [hc]; norm_num⟩
  · obtain ⟨f⟩ := hM
    have hc : Nat.card W = 95040 := by rw [Nat.card_congr f.toEquiv, hE.m12Card]
    refine ⟨by rw [hc]; norm_num, by rw [hc]; norm_num, by rw [hc]; norm_num⟩
  · obtain ⟨-, h3, h32⟩ := f618L3_props hp8 hS
    have hpos : 0 < Nat.card W := by
      by_contra h0
      have : Nat.card W = 0 := by omega
      rw [this] at h32
      simp at h32
    refine ⟨h3, hpos, fun hd => ?_⟩
    have h1 : 32 ∣ Nat.card W := h32 ▸ Nat.ordProj_dvd (Nat.card W) 2
    have := dvd_trans h1 hd
    norm_num at this

theorem eq_of_two_pow_eq {n k : ℕ} (h : 2 ^ n = 2 ^ k) : n = k :=
  Nat.pow_right_injective le_rfl h

theorem cube_dvd_card_mul_three {p : ℕ}
    (h : IsPSL 3 p 1 W ∨ IsPSU 3 p 1 W) : p ^ 3 ∣ Nat.card W * 3 := by
  rcases h with h | h
  · have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound W 3 p 1
      h).1
    set g := Nat.gcd 3 (p ^ 1 - 1) with hg
    set N := (p ^ 1) ^ (3 * (3 - 1) / 2) * ∏ j ∈ Finset.Icc 2 3, ((p ^ 1) ^ j - 1) with hN
    have hgN : g ∣ N := by
      refine dvd_trans (Nat.gcd_dvd_right 3 (p ^ 1 - 1)) (Dvd.dvd.mul_left ?_ _)
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (show 2 ∈ Finset.Icc 2 3 by decide))
      simpa [pow_one] using Nat.sub_dvd_pow_sub_pow p 1 2
    have hWN : Nat.card W * g = N := by rw [hb]; exact Nat.div_mul_cancel hgN
    have hp3 : p ^ 3 ∣ N := by
      rw [hN, show 3 * (3 - 1) / 2 = 3 by norm_num, pow_one]
      exact dvd_mul_right _ _
    have hg3 : g ∣ 3 := Nat.gcd_dvd_left 3 _
    exact dvd_trans (hWN ▸ hp3) (mul_dvd_mul_left _ hg3)
  · have hb := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound W 3 p 1
      h).1
    set g := Nat.gcd 3 (p ^ 1 + 1) with hg
    have hp3 : ((p ^ 3 : ℕ) : ℤ) ∣ (Nat.card W : ℤ) * (g : ℤ) := by
      rw [hb, show 3 * (3 - 1) / 2 = 3 by norm_num, pow_one]
      push_cast
      exact dvd_mul_right _ _
    have hg3 : g ∣ 3 := Nat.gcd_dvd_left 3 _
    have h1 : p ^ 3 ∣ Nat.card W * g := by exact_mod_cast hp3
    exact dvd_trans h1 (mul_dvd_mul_left _ hg3)

theorem not_f618_of_isPSL_two_two (hE : ExclInputs) [IsSimpleGroup W] {n : ℕ}
    (hS : IsPSL 2 2 n W) (hF : F618SimpleType W) : False := by
  have hn : 1 ≤ n := hS.1.2.1
  have hcard := card_of_isPSL_two_two hS
  have h2 : ordProj[2] (Nat.card W) = 2 ^ n := by rw [hcard]; exact ordProj_two_card_L2_even n hn
  rcases hF with (⟨p, e, hp, he1, he2, hL, hc⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | hM) | ⟨p, hp8, hT⟩
  · obtain ⟨-, hq7, hcardL, h48⟩ := f618L2_props hp he1 he2 hL hc
    have h168 := le_card_L2 hq7
    rw [← hcardL] at h168
    rcases h48 with h | h
    · rw [h2, show (4 : ℕ) = 2 ^ 2 by norm_num] at h
      obtain rfl := eq_of_two_pow_eq h
      rw [hcard] at h168
      norm_num at h168
    · rw [h2, show (8 : ℕ) = 2 ^ 3 by norm_num] at h
      obtain rfl := eq_of_two_pow_eq h
      have h504 : p ^ e * ((p ^ e) ^ 2 - 1) / 2 = 504 := by rw [← hcardL, hcard]; norm_num
      have hq10 : p ^ e ≤ 10 := by
        by_contra hq
        have : 660 ≤ p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
          rw [Nat.le_div_iff_mul_le (by norm_num)]
          have h1 : 120 ≤ (p ^ e) ^ 2 - 1 := by
            have : 121 ≤ (p ^ e) ^ 2 := by nlinarith
            omega
          calc 660 * 2 = 11 * 120 := by norm_num
            _ ≤ p ^ e * ((p ^ e) ^ 2 - 1) := Nat.mul_le_mul (by omega) h1
        omega
      interval_cases (p ^ e) <;> norm_num at h504
  · have hc : Nat.card W = 360 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    rw [hc, ordProj_two_of_eq_mul (k := 3) (m := 45) (by norm_num) (by norm_num)] at h2
    obtain rfl := eq_of_two_pow_eq h2.symm
    rw [hc] at hcard
    norm_num at hcard
  · have hc : Nat.card W = 2520 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    rw [hc, ordProj_two_of_eq_mul (k := 3) (m := 315) (by norm_num) (by norm_num)] at h2
    obtain rfl := eq_of_two_pow_eq h2.symm
    rw [hc] at hcard
    norm_num at hcard
  · obtain ⟨f⟩ := hM
    have hc : Nat.card W = 95040 := by rw [Nat.card_congr f.toEquiv, hE.m12Card]
    rw [hc, ordProj_two_of_eq_mul (k := 6) (m := 1485) (by norm_num) (by norm_num)] at h2
    obtain rfl := eq_of_two_pow_eq h2.symm
    rw [hc] at hcard
    norm_num at hcard
  · obtain ⟨hmodel, -, h32⟩ := f618L3_props hp8 hT
    rw [h32, show (32 : ℕ) = 2 ^ 5 by norm_num] at h2
    obtain rfl := eq_of_two_pow_eq h2.symm
    have hcube := cube_dvd_card_mul_three (hmodel.imp (fun h => h.2) (fun h => h.2))
    rw [hcard] at hcube
    norm_num at hcube
    have hp3 : 3 ≤ p := by omega
    have hle : p ^ 3 ≤ 98208 := Nat.le_of_dvd (by norm_num) hcube
    have hp46 : p ≤ 46 := by
      by_contra hp
      have : 47 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
      norm_num at this
      omega
    interval_cases p <;> norm_num at hcube

end F618

@[expose] def CoversF618 {Q : Type} [Group Q] (B : Subgroup Q) : Prop :=
  ∃ (P : Type) (_ : Group P) (W : Type) (_ : Group W) (α : P →* ↥B) (β : P →* W),
    Function.Surjective α ∧ Group.IsSolvable ↥α.ker ∧ Function.Surjective β ∧
      Group.IsSolvable ↥β.ker ∧ IsSimpleGroup W ∧ F618SimpleType W

section Excluded

theorem exists_noncomm_of_f618Orders {W : Type} [Group W] [IsSimpleGroup W] (h : F618Orders W) :
    ∃ a b : W, a * b ≠ b * a := by
  have : Finite W := Nat.finite_of_card_ne_zero h.card_pos.ne'
  refine CFSG.Quasithin.A314.exists_noncomm_of_simple inferInstance fun hp => ?_
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h.three_dvd
  exact h.not_dvd (by rw [← h3]; norm_num)

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

omit [Finite Q] in
theorem false_of_cover (hE : ExclInputs) (hC : CoversF618 B) {S : Type} [Group S] [Finite S]
    (γ : ↥B →* S) (hγ : Function.Surjective γ) (hγk : Group.IsSolvable γ.ker)
    (hS : Nat.card S ∣ 120 ∨ ¬ 3 ∣ Nat.card S) : False := by
  obtain ⟨P, _, W, _, α, β, hα, hαk, hβ, hβk, hWs, hF⟩ := hC
  have hO := f618Orders hE hF
  have hd := card_dvd_of_solvable_kernels α hα hαk β hβ (exists_noncomm_of_f618Orders hO) γ hγ hγk
  rcases hS with hS | hS
  · exact hO.not_dvd (dvd_trans hd hS)
  · exact hS (dvd_trans hO.three_dvd hd)

theorem isSolvable_pCore_two : Group.IsSolvable ↥(CFSG.pCore 2 ↥B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥B) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).isNilpotent
  infer_instance

theorem false_of_c2 (hE : ExclInputs) (hC : CoversF618 B) (h : A312C2 B L) : False := by
  obtain ⟨⟨n, hS⟩, -, -⟩ := h
  obtain ⟨P, _, W, _, α, β, hα, hαk, hβ, hβk, hWs, hF⟩ := hC
  have hO := f618Orders hE hF
  have : IsSimpleGroup (ModO2 B) := isSimpleGroup_of_isPSL hS
  obtain ⟨e⟩ := nonempty_mulEquiv_of_solvable_kernels α hα hαk β hβ hβk
    (exists_noncomm_of_f618Orders hO) (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact isSolvable_pCore_two)
    (exists_noncomm_of_isPSL hS)
  exact not_f618_of_isPSL_two_two hE (isPSL_of_mulEquiv e hS) hF

theorem false_of_c3 (hE : ExclInputs) (hC : CoversF618 B) (h : A312C3 B L) : False := by
  obtain ⟨f, hS, -, -⟩ := h
  exact false_of_cover hE hC (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact isSolvable_pCore_two)
    (Or.inr (hE.szThree _ f hS))

theorem false_of_isAlt_five (hE : ExclInputs) (hC : CoversF618 B) (hB : IsAlt 5 ↥B) : False := by
  obtain ⟨e⟩ := hB
  refine false_of_cover hE hC e.toMonoidHom e.surjective ?_ (Or.inl ?_)
  · have : Subsingleton ↥e.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      infer_instance
    infer_instance
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide

theorem false_of_c8_right (hE : ExclInputs) (hC : CoversF618 B) (hB : IsAlt 5 ↥B) : False :=
  false_of_isAlt_five hE hC hB

theorem false_of_c15 (hE : ExclInputs) (hC : CoversF618 B) (h : A312C15 B L) : False :=
  false_of_isAlt_five hE hC h.1

theorem false_of_c16 (hE : ExclInputs) (hC : CoversF618 B) (h : A312C16 B L) : False := by
  obtain ⟨⟨V, hVn, hV, ⟨e⟩⟩, -⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVs : Group.IsSolvable ↥V := by
    have hp : IsPGroup 2 ↥V := IsPGroup.of_card hV.2
    have : Group.IsNilpotent ↥V := hp.isNilpotent
    infer_instance
  refine false_of_cover hE hC (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)
    (by rw [QuotientGroup.ker_mk']; exact hVs) (Or.inl ?_)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide

omit [Finite Q] in
theorem false_of_sup_quotient (hE : ExclInputs) (hC : CoversF618 B) {OL : Subgroup Q}
    (hBN : B ≤ Subgroup.normalizer (OL : Set Q)) (hOLs : Group.IsSolvable ↥OL)
    {N : Subgroup ↥(B ⊔ OL)} [N.Normal] (hN : N = OL.subgroupOf (B ⊔ OL))
    (hSL : IsSL2 5 (↥(B ⊔ OL) ⧸ N)) : False := by
  subst hN
  let γ : ↥B →* ↥(B ⊔ OL) ⧸ OL.subgroupOf (B ⊔ OL) :=
    (QuotientGroup.mk' (OL.subgroupOf (B ⊔ OL))).comp (Subgroup.inclusion le_sup_left)
  have hγ : Function.Surjective γ := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : Q) ∈ ((B : Set Q) * (OL : Set Q)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right B OL hBN]
        exact y.2
      obtain ⟨b, hb, o, ho, hbo⟩ := Set.mem_mul.mp hy
      refine ⟨⟨b, hb⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨b, hb⟩) = QuotientGroup.mk y
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e1 : (((Subgroup.inclusion le_sup_left ⟨b, hb⟩ : ↥(B ⊔ OL))⁻¹ * y : ↥(B ⊔ OL)) :
          Q) = o := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, ← hbo]
        group
      rw [e1]
      exact ho
  have hγk : Group.IsSolvable γ.ker := by
    have hmem : ∀ x : ↥γ.ker, ((x : ↥B) : Q) ∈ OL := by
      intro x
      have h1 : γ x = 1 := x.2
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_subgroupOf] at h2
      exact h2
    let f : ↥γ.ker →* ↥OL :=
      { toFun := fun x => ⟨((x : ↥B) : Q), hmem x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨e⟩ := hSL
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (↥(B ⊔ OL) ⧸ OL.subgroupOf (B ⊔ OL)) := Finite.of_equiv _ e.symm.toEquiv
  have h120 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
    norm_num
  refine false_of_cover hE hC γ hγ hγk (Or.inl ?_)
  rw [Nat.card_congr e.toEquiv, h120]

omit [Finite Q] in
theorem le_normalizer_oddCore (hBL : B ≤ L) :
    B ≤ Subgroup.normalizer (((CFSG.oddCore ↥L).map L.subtype : Subgroup Q) : Set Q) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨⟨b, hBL hb⟩ * o * ⟨b, hBL hb⟩⁻¹,
      (inferInstance : (CFSG.oddCore ↥L).Normal).conj_mem o ho _, rfl⟩
  · rintro ⟨o, ho, hox⟩
    refine ⟨⟨b, hBL hb⟩⁻¹ * o * ⟨b, hBL hb⟩, ?_, ?_⟩
    · have := (inferInstance : (CFSG.oddCore ↥L).Normal).conj_mem o ho ⟨b, hBL hb⟩⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hox ⊢
      rw [hox]
      group

theorem isSolvable_oddCore_map : Group.IsSolvable ↥((CFSG.oddCore ↥L).map L.subtype) := by
  have := CFSG.Quasithin.A312.oddCore_isSolvable ↥L
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((CFSG.oddCore ↥L).equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom)
    ((CFSG.oddCore ↥L).equivMapOfInjective L.subtype L.subtype_injective).symm.injective

end Excluded

end CFSG.Quasithin.H13.InspA312
