module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911Bender
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911L2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
public import CFSG.GroupTheory.ProductTorusAutFix
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_isL2_torus_factor {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    Nat.card X = (2 ^ n - 1) * (2 ^ n * (2 ^ n + 1)) := by
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  rw [(CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isL2 h).2, hsq]
  ring

theorem odd_two_pow_sub_one_of_one_le {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega : n ≠ 0)).2 even_two) odd_one

theorem coprime_torus_isL2 {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1) (2 ^ n * (2 ^ n + 1)) := by
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hcopq : Nat.Coprime (2 ^ n - 1) (2 ^ n) :=
    ((Nat.coprime_self_sub_right (m := 1) (n := 2 ^ n) hq1).2
      (Nat.coprime_one_right _)).symm
  have hcop2 : Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) := by
    have h : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by omega
    rw [h, Nat.coprime_self_add_right]
    exact Nat.coprime_two_right.mpr (odd_two_pow_sub_one_of_one_le hn)
  exact hcopq.mul_right hcop2

theorem l2_prod_arith {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] {n : ℕ}
    (h₁ : IsL2 Y₁ n) (h₂ : IsL2 Y₂ n) (hn : 3 ≤ n) :
    1 < 2 ^ n - 1 ∧ Odd (2 ^ n - 1) ∧
      Nat.card Y₁ = (2 ^ n - 1) * (2 ^ n * (2 ^ n + 1)) ∧
      Nat.card Y₂ = (2 ^ n - 1) * (2 ^ n * (2 ^ n + 1)) ∧
      Nat.Coprime (2 ^ n - 1) (2 ^ n * (2 ^ n + 1)) := by
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨by omega, odd_two_pow_sub_one_of_one_le (by omega), card_isL2_torus_factor h₁,
    card_isL2_torus_factor h₂, coprime_torus_isL2 (by omega)⟩

theorem l2_prod_factor_data {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] [Finite Y₁] [Finite Y₂]
    {n : ℕ} (h₁ : IsL2 Y₁ n) (h₂ : IsL2 Y₂ n) :
    IsSimpleGroup Y₁ ∧ IsSimpleGroup Y₂ ∧ center Y₁ = ⊥ ∧ center Y₂ = ⊥ ∧
      (∀ B : Subgroup Y₁, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₁,
        (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) →
        ∀ R : Subgroup Y₁, IsPGroup 2 R → B ≤ normalizer (R : Set Y₁) →
        s ∈ normalizer (R : Set Y₁) → R = ⊥) ∧
      (∀ B : Subgroup Y₂, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₂,
        (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) →
        ∀ R : Subgroup Y₂, IsPGroup 2 R → B ≤ normalizer (R : Set Y₂) →
        s ∈ normalizer (R : Set Y₂) → R = ⊥) := by
  have hB₁ : CFSG.BenderSuzuki.IsBenderGroup Y₁ :=
    CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup
      (uc22p2214_bor_bender_L2 h₁)
  have hB₂ : CFSG.BenderSuzuki.IsBenderGroup Y₂ :=
    CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup
      (uc22p2214_bor_bender_L2 h₂)
  haveI : IsSimpleGroup Y₁ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB₁
  haveI : IsSimpleGroup Y₂ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB₂
  have hZ₁ : center Y₁ = ⊥ := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hB₁
    exact CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_isSimpleGroup
      (a := a) (b := b) (fun h => hab (commute_iff_eq a b |>.2 h))
  have hZ₂ : center Y₂ = ⊥ := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hB₂
    exact CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_isSimpleGroup
      (a := a) (b := b) (fun h => hab (commute_iff_eq a b |>.2 h))
  have hN₁ : ∀ B : Subgroup Y₁, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₁,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₁,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₁) → s ∈ normalizer (R : Set Y₁) → R = ⊥ :=
    fun B hB hodd s hs hinv R hR hBR hsR =>
      k1911_eq_bot_of_bender (Or.inl h₁) hB hodd hs hinv hR hBR hsR
  have hN₂ : ∀ B : Subgroup Y₂, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₂,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₂,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₂) → s ∈ normalizer (R : Set Y₂) → R = ⊥ :=
    fun B hB hodd s hs hinv R hR hBR hsR =>
      k1911_eq_bot_of_bender (Or.inl h₂) hB hodd hs hinv hR hBR hsR
  exact ⟨inferInstance, inferInstance, hZ₁, hZ₂, hN₁, hN₂⟩

theorem l2_prod_Q_eq_bot {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] [Finite Y₁] [Finite Y₂]
    {n : ℕ} (h₁ : IsL2 Y₁ n) (h₂ : IsL2 Y₂ n) (hn : 3 ≤ n)
    {A : Subgroup (Y₁ × Y₂)}
    (hA : CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.IsZModSq ↥A n) {t : Y₁ × Y₂}
    (ht : ∃ k : ℕ, orderOf t = 2 ^ k) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    {Q : Subgroup (MulAut (Y₁ × Y₂))} (hQ : IsPGroup 2 Q)
    (hQB : ∀ b ∈ A ⊔ zpowers t, MulAut.conj b ∈ normalizer (Q : Set (MulAut (Y₁ × Y₂)))) :
    Q = ⊥ := by
  obtain ⟨hm, hoddm, hcard₁, hcard₂, hcop⟩ := l2_prod_arith h₁ h₂ hn
  obtain ⟨hs₁, hs₂, hZ₁, hZ₂, hN₁, hN₂⟩ := l2_prod_factor_data h₁ h₂
  haveI := hs₁
  haveI := hs₂
  have hmain := CFSG.GroupTheory.prod_aut_fix_of_forall_eq_bot
    (m := 2 ^ n - 1) (c₁ := 2 ^ n * (2 ^ n + 1)) (c₂ := 2 ^ n * (2 ^ n + 1))
    hZ₁ hZ₂ hm hoddm hcard₁ hcard₂ hcop hcop hN₁ hN₂
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_eq_of_isZModSq hA) ht hinv hQ hQB
  rw [eq_bot_iff]
  intro α hα
  obtain ⟨β₁, β₂, hαeq, hβ₁, hβ₂, hfix₁, hfix₂⟩ := hmain.2.2.2 α hα
  haveI : IsMulCommutative ↥A :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isMulCommutative_of_isZModSq hA
  have hβ₁one : β₁ = 1 :=
    eq_one_of_isL2_of_fix_of_two_pow h₁ hn inferInstance hmain.1 β₁ hβ₁ hfix₁
  have hβ₂one : β₂ = 1 :=
    eq_one_of_isL2_of_fix_of_two_pow h₂ hn inferInstance hmain.2.1 β₂ hβ₂ hfix₂
  calc α = CFSG.GroupTheory.mulAutProdHom Y₁ Y₂ (β₁, β₂) := hαeq
    _ = CFSG.GroupTheory.mulAutProdHom Y₁ Y₂
        ((1 : MulAut Y₁), (1 : MulAut Y₂)) := by rw [hβ₁one, hβ₂one]
    _ = 1 := map_one (CFSG.GroupTheory.mulAutProdHom Y₁ Y₂)

theorem torusFixedConcl_l2_prod {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] [Finite Y₁] [Finite Y₂]
    {n p : ℕ} (h₁ : IsL2 Y₁ n) (h₂ : IsL2 Y₂ n) (hn : 3 ≤ n) (hp : p.Prime)
    (hpd : p ∣ 2 ^ n + 1) : TorusFixedConcl (Y₁ × Y₂) n p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hcard₁, hcard₂, -⟩ := l2_prod_arith h₁ h₂ hn
  have hpY₁ : p ∣ Nat.card Y₁ := by
    rw [hcard₁]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpd (2 ^ n)) (2 ^ n - 1)
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' p hpY₁
  have hpY₂ : p ∣ Nat.card Y₂ := by
    rw [hcard₂]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpd (2 ^ n)) (2 ^ n - 1)
  obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' p hpY₂
  intro A t hA ht hinv Q hQ hQB
  have hQbot := l2_prod_Q_eq_bot h₁ h₂ hn hA ht hinv hQ hQB
  let E : Subgroup (Y₁ × Y₂) := (zpowers y₁).prod (zpowers y₂)
  refine ⟨E, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm fun x y => ?_
      apply (Subgroup.prodEquiv (zpowers y₁) (zpowers y₂)).injective
      rw [map_mul, map_mul]
      exact mul_comm' _ _
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
      have h1 : x.1 ^ p = 1 := by
        have hd : orderOf x.1 ∣ p := by
          have := orderOf_dvd_of_mem_zpowers hx1
          rwa [hy₁] at this
        exact orderOf_dvd_iff_pow_eq_one.mp hd
      have h2 : x.2 ^ p = 1 := by
        have hd : orderOf x.2 ∣ p := by
          have := orderOf_dvd_of_mem_zpowers hx2
          rwa [hy₂] at this
        exact orderOf_dvd_iff_pow_eq_one.mp hd
      exact Prod.ext h1 h2
  · have hcardE : Nat.card E = Nat.card ((zpowers y₁) × (zpowers y₂)) :=
      Nat.card_congr (Subgroup.prodEquiv (zpowers y₁) (zpowers y₂)).toEquiv
    rw [hcardE, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hy₁, hy₂, pow_two]
  · intro α hα e he
    rw [hQbot] at hα
    have hα1 : α = 1 := by simpa using hα
    rw [hα1]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
