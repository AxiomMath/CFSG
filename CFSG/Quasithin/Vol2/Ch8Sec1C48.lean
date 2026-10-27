module

public import CFSG.Quasithin.Background.C4Statement
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J1
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Orders

variable {X Y : Type*} [Group X] [Group Y]

theorem card_dvd_of_surjective [Finite X] (ψ : X →* Y) (hψ : Function.Surjective ψ) :
    Nat.card Y ∣ Nat.card X := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv,
    ψ.ker.card_eq_card_quotient_mul_card_subgroup]
  exact Dvd.intro _ rfl

private theorem card_eq_of_surjective_of_isSimpleGroup [Finite X] [IsSimpleGroup X] [Nontrivial Y]
    (ψ : X →* Y) (hψ : Function.Surjective ψ) : Nat.card X = Nat.card Y := by
  have hinj : Function.Injective ψ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ψ).1 h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨x, rfl⟩ := hψ y
      exact hy (ψ.mem_ker.1 (h ▸ Subgroup.mem_top x))
  exact Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hψ⟩)

theorem card_modO2_eq {G : Type} [Group G] {L : Subgroup G} {A : Type*} [Group A]
    (α : ↥L →* A) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (ModO2 L) = Nat.card A := by
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card]
  have := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at this
  have h720 : (6 : ℕ).factorial = 720 := by decide
  rw [h720] at this
  omega

private theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card]
  have := two_mul_card_alternatingGroup (α := Fin 7)
  rw [Fintype.card_perm, Fintype.card_fin] at this
  have h5040 : (7 : ℕ).factorial = 5040 := by decide
  rw [h5040] at this
  omega

theorem card_psl_two {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 2 K)) =
      Nat.card K * (Nat.card K ^ 2 - 1) / Nat.gcd 2 (Nat.card K - 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)]
  simp

theorem psl_two_ge (q : ℕ) : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) :=
  Nat.div_le_div_left (Nat.gcd_le_left _ (by norm_num)) (Nat.gcd_pos_of_pos_left _ (by norm_num))

end Orders

section Simple

variable {X : Type} [Group X]

theorem psl_two_two_card_ne {n : ℕ} (h : IsPSL 2 2 n X) :
    Nat.card X ≠ 20160 ∧ Nat.card X ≠ 443520 := by
  obtain ⟨⟨-, hf, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_psl_two, hK]
  have hlow := psl_two_ge (2 ^ n)
  by_cases hn : n < 19
  · have key : ∀ n < 19, (2 ^ n * ((2 ^ n) ^ 2 - 1) / Nat.gcd 2 (2 ^ n - 1) ≠ 20160 ∧
        2 ^ n * ((2 ^ n) ^ 2 - 1) / Nat.gcd 2 (2 ^ n - 1) ≠ 443520) := by decide
    exact key n hn
  · have h19 : 2 ^ 19 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ 19 * ((2 ^ 19) ^ 2 - 1) / 2 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) / 2 := by
      apply Nat.div_le_div_right
      apply Nat.mul_le_mul h19
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h19 2) 1
    have h2 : 443520 < 2 ^ 19 * ((2 ^ 19) ^ 2 - 1) / 2 := by norm_num
    constructor <;> omega

theorem psl_two_odd_card_ne {p : ℕ} (h : IsPSL 2 p 1 X) :
    Nat.card X ≠ 20160 ∧ Nat.card X ≠ 443520 := by
  obtain ⟨⟨hp, -, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_psl_two, hK, pow_one]
  have hlow := psl_two_ge p
  by_cases hn : p < 122
  · have key : ∀ p < 122, (p * (p ^ 2 - 1) / Nat.gcd 2 (p - 1) ≠ 20160 ∧
        p * (p ^ 2 - 1) / Nat.gcd 2 (p - 1) ≠ 443520) := by decide
    exact key p hn
  · have h1 : 122 * (122 ^ 2 - 1) / 2 ≤ p * (p ^ 2 - 1) / 2 := by
      apply Nat.div_le_div_right
      apply Nat.mul_le_mul (by omega)
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1
    have h2 : 443520 < 122 * (122 ^ 2 - 1) / 2 := by norm_num
    constructor <;> omega

theorem psl_five_two_card (h : IsPSL 5 2 1 X) : Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

theorem sz_card_ne
    {n : ℕ} (h : IsSz n X) : Nat.card X ≠ 20160 ∧ Nat.card X ≠ 443520 := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  by_cases ha : a < 5
  · have key : ∀ a < 5, ((2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) ≠ 20160 ∧ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) ≠ 443520) := by decide
    exact key a ha
  · have h1 : 2 ^ 11 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 ^ 11) ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
      have h3 : 1 ≤ 2 ^ (2 * a + 1) - 1 := by
        have : 2 ≤ 2 ^ (2 * a + 1) := le_trans (by norm_num) h1
        omega
      calc (2 ^ 11) ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := Nat.le_mul_of_pos_right _ h3
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
    constructor <;> intro h <;> rw [h] at h2 <;> norm_num at h2

end Simple

variable {G : Type} [Group G] [Finite G]

theorem false_of_c48Conclusion
    {H R M L V : Subgroup G} {Y : Type*} [Group Y] [Finite Y]
    (ψ : ModO2 L →* Y) (hψ : Function.Surjective ψ)
    (hY : Nat.card Y = 20160 ∨ Nat.card Y = 443520)
    (hV : Nat.card V = 2 ^ 10 ∨ Nat.card V = 2 ^ 11) (h : C48Conclusion H R M L V) : False := by
  have : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rcases hY with h | h <;> rw [h] <;> norm_num
  have hle : Nat.card Y ≤ Nat.card (ModO2 L) := Nat.card_le_card_of_surjective ψ hψ
  have hYge : 20160 ≤ Nat.card Y := by rcases hY with h | h <;> omega
  have hsimple : ∀ [IsSimpleGroup (ModO2 L)], Nat.card (ModO2 L) = 20160 ∨
      Nat.card (ModO2 L) = 443520 := by
    intro _
    rw [card_eq_of_surjective_of_isSimpleGroup ψ hψ]
    exact hY
  obtain ⟨-, K, -, -, -, hcases⟩ := h
  rcases hcases with h10 | ⟨hc, -, -, -⟩
  ·
    obtain ⟨-, hL, -⟩ := h10
    rcases hL with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, -, -, hp⟩
    · have := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hn).2
      have h1 := hsimple
      have h2 := psl_two_two_card_ne hn
      omega
    · have := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n hn).2
      have h1 := hsimple
      have h2 := sz_card_ne hn
      omega
    · obtain ⟨e⟩ := hJ
      have hd := card_dvd_of_surjective ψ hψ
      rw [Nat.card_congr e.toEquiv] at hd
      change Nat.card Y ∣ Nat.card NativeSporadic.J1 at hd
      rw [CFSG.Sporadic.J1.card_J1] at hd
      rcases hY with h | h <;> rw [h] at hd <;> norm_num at hd
    · have := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hp).2
      have h1 := hsimple
      have h2 := psl_two_odd_card_ne hp
      omega
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  ·
    obtain ⟨n, hn, -⟩ := h1
    have := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hn).2
    have h1 := hsimple
    have h2 := psl_two_two_card_ne hn
    omega
  ·
    obtain ⟨m, hm, -, hmod⟩ := h2
    rcases hmod with ⟨k, -, α, -, -, -, -, β, hβs, hβk, -⟩ | ⟨rfl, -, α, -, -, β, hβs, hβk, -⟩
    · have hinj : Function.Injective β := by
        rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
      have hc : Nat.card ↥V = (2 ^ m) ^ k := by
        rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩),
          Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fun, Nat.card_zmod,
          Nat.card_fin, Nat.card_fin]
      rw [hc, ← pow_mul] at hV
      rcases hV with h | h <;> have := Nat.pow_right_injective (le_refl 2) h <;>
        rcases hm with rfl | rfl <;> omega
    · have hinj : Function.Injective β := by
        rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
      have hc : Nat.card ↥V ≤ 2 ^ 8 := by
        rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩),
          Nat.card_congr Multiplicative.toAdd]
        calc Nat.card (AltHeart 8) ≤ Nat.card ↥(evenWeight 8) :=
              Nat.card_le_card_of_surjective _ (QuotientAddGroup.mk_surjective)
          _ ≤ Nat.card (Fin 8 → ZMod 2) := Nat.card_le_card_of_injective _ Subtype.val_injective
          _ = 2 ^ 8 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rcases hV with h | h <;> rw [h] at hc <;> norm_num at hc
  ·
    obtain ⟨-, -, α, hα, hker, -⟩ := h3
    rw [card_modO2_eq α hα hker, card_alternatingGroup_six] at hle
    omega
  ·
    obtain ⟨-, -, ⟨α, hα, hker⟩, -⟩ := h4
    rw [card_modO2_eq α hα hker, card_alternatingGroup_seven] at hle
    omega
  ·
    obtain ⟨-, -, ⟨-, hZ, ⟨e⟩⟩, -⟩ := h5
    have hc := (Subgroup.center (ModO2 L)).card_eq_card_quotient_mul_card_subgroup
    rw [hZ, Nat.card_congr e.toEquiv, card_alternatingGroup_six] at hc
    omega
  ·
    obtain ⟨-, -, ⟨⟨e⟩, -⟩ | ⟨hp, -⟩⟩ := h6
    · have : IsSimpleGroup (NativeSporadic.Carrier .M24) :=
        CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      have : IsSimpleGroup (ModO2 L) := e.isSimpleGroup
      have h1 := hsimple
      have h2 : Nat.card (ModO2 L) = 244823040 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Sporadic.Mathieu.card_M24
      omega
    · have := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1 hp).2
      have h1 := hsimple
      have h2 := psl_five_two_card hp
      omega
  ·
    obtain ⟨-, -, ⟨-, K', _, _, hK, ⟨e⟩⟩, -⟩ := h7
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
      Nat.prime_three le_rfl hK (by norm_num)] at hle
    have h6048 : ((3 : ℕ) ^ 1) ^ (3 * (3 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 3, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd 3 (3 ^ 1 + 1) = 6048 := by decide
    rw [h6048] at hle
    omega
  ·
    obtain ⟨-, -, α, hα, hker, -⟩ := h8
    rw [card_modO2_eq α hα hker, card_alternatingGroup_six] at hle
    omega
  ·
    obtain ⟨-, -, ⟨e⟩⟩ := h9
    have hc : Nat.card ↥V = 2 ^ 4 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    rcases hV with h | h <;> rw [h] at hc <;> norm_num at hc

end CFSG.Quasithin.H13
