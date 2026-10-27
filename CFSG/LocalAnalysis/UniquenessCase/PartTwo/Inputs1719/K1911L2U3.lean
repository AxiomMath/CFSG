module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911L2Sq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911U3Sub
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroupHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_isU3_torus_factor {X : Type} [Group X] {n : ℕ} (h : IsU3 X n)
    (heven : Even n) :
    Nat.card X = (2 ^ n - 1) *
      ((2 ^ n) ^ 3 * (2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 - 2 ^ n + 1)) := by
  have hcop : Nat.Coprime 3 (2 ^ n + 1) :=
    (Nat.prime_three.coprime_iff_not_dvd).2
      (CFSG.LocalAnalysis.UniquenessCase.UC6S898.not_three_dvd_two_pow_add_one_of_even heven)
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := Nat.Coprime.gcd_eq_one hcop
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_of_isU3 h, hgcd, Nat.div_one,
    CFSG.Quasithin.Ch1Four.sq_sub_one_eq,
    CFSG.Quasithin.Ch1Four.cube_add_one_eq (Nat.one_le_two_pow (n := n))]
  ring

theorem coprime_two_pow_sub_one_sq_sub_add_one {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1) ((2 ^ n) ^ 2 - 2 ^ n + 1) := by
  have h : 2 ^ n * (2 ^ n - 1) = (2 ^ n) ^ 2 - 2 ^ n := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  have e : (2 ^ n) ^ 2 - 2 ^ n + 1 = 1 + (2 ^ n - 1) * 2 ^ n := by
    rw [← h]
    ring
  rw [e, Nat.coprime_add_mul_left_right]
  exact Nat.coprime_one_right _

theorem coprime_torus_isU3 {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1)
      ((2 ^ n) ^ 3 * (2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 - 2 ^ n + 1)) := by
  have hq : Nat.Coprime (2 ^ n - 1) (2 ^ n) := by
    rw [Nat.coprime_self_sub_left (Nat.one_le_two_pow (n := n))]
    exact Nat.coprime_one_left _
  have hp : Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) := uc22pwsu3_coprime_two_pow hn
  have hf : Nat.Coprime (2 ^ n - 1) ((2 ^ n) ^ 2 - 2 ^ n + 1) :=
    coprime_two_pow_sub_one_sq_sub_add_one hn
  exact ((hq.pow_right 3).mul_right (hp.pow_right 2)).mul_right hf

theorem exists_orderOf_fixed_of_isU3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU3 Y n)
    (hn : 3 ≤ n) (heven : Even n) {T : Subgroup Y} (hTc : IsMulCommutative T)
    (hT : Nat.card T = 2 ^ n - 1) {p : ℕ} (hp : p.Prime) (hpd : p ∣ 2 ^ n + 1) :
    ∃ y : Y, orderOf y = p ∧ ∀ β : MulAut Y, (∃ k : ℕ, orderOf β = 2 ^ k) →
      (∀ a ∈ T, β a = a) → β y = y := by
  classical
  obtain ⟨L, hL2, hTL, hLmap⟩ := exists_isL2_le_of_isU3 hY (by omega) heven hTc hT
  have hpL : p ∣ Nat.card L :=
    hpd.trans
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.two_pow_add_one_dvd_card_of_isL2_psl_two
        hL2)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨yL, hyL⟩ := exists_prime_orderOf_dvd_card' p hpL
  refine ⟨(yL : Y), ?_, ?_⟩
  · rw [orderOf_coe]; exact hyL
  · intro β hβ hfix
    obtain ⟨k, hk⟩ := hβ
    let βLhom : ↥L →* ↥L :=
      { toFun := fun x => ⟨β x.1, by
          have hx : β x.1 ∈ L.map β.toMonoidHom :=
            Subgroup.mem_map_of_mem β.toMonoidHom x.2
          rwa [hLmap β hfix] at hx⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp }
    have hβLhom_inj : Function.Injective βLhom := by
      intro x y h
      apply Subtype.ext
      exact β.injective (congrArg Subtype.val h)
    let βL : MulAut ↥L :=
      MulEquiv.ofBijective βLhom ⟨hβLhom_inj,
        Finite.surjective_of_injective hβLhom_inj⟩
    have hβL_apply : ∀ x : ↥L, (βL x : Y) = β x := fun _ => rfl
    have key : ∀ (N : ℕ) (x : ↥L), ((βL ^ N) x : Y) = (β ^ N) x := by
      intro N
      induction N with
      | zero => intro x; rfl
      | succ N ih =>
          intro x
          calc ((βL ^ (N + 1)) x : Y) = ((βL ^ N * βL) x : Y) := by rw [pow_succ]
            _ = ((βL ^ N) (βL x) : Y) := by rw [MulAut.mul_apply]
            _ = (β ^ N) (βL x) := ih (βL x)
            _ = (β ^ N) (β x) := by rw [hβL_apply]
            _ = ((β ^ N * β) x) := by rw [MulAut.mul_apply]
            _ = (β ^ (N + 1)) x := by rw [pow_succ]
    have hβpow : β ^ 2 ^ k = 1 := by
      rw [← hk]; exact pow_orderOf_eq_one β
    have hβLpow : βL ^ 2 ^ k = 1 := by
      ext x
      rw [key (2 ^ k) x, hβpow]
      rfl
    have hβLord : ∃ j : ℕ, orderOf βL = 2 ^ j := by
      have hdvd : orderOf βL ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hβLpow
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨j, hj⟩
    haveI : IsMulCommutative ↥T := hTc
    have hTcL : IsMulCommutative (T.subgroupOf L) := inferInstance
    have hTL' : Nat.card (T.subgroupOf L) = 2 ^ n - 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT]
    have hβLfix : ∀ a ∈ T.subgroupOf L, βL a = a := by
      intro a ha
      apply Subtype.ext
      rw [hβL_apply]
      exact hfix a.1 ha
    have hβLone : βL = 1 :=
      eq_one_of_isL2_of_fix_of_two_pow hL2 hn hTcL hTL' βL hβLord hβLfix
    have hy : βL yL = yL := by rw [hβLone]; rfl
    have h := congrArg Subtype.val hy
    rw [hβL_apply yL] at h
    exact h

theorem torusFixedConcl_l2_u3_prod {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] [Finite Y₁]
    [Finite Y₂] {n p : ℕ} (h₁ : IsL2 Y₁ n) (h₂ : IsU3 Y₂ n) (hn : 3 ≤ n) (heven : Even n)
    (hp : p.Prime) (hpd : p ∣ 2 ^ n + 1) : TorusFixedConcl (Y₁ × Y₂) n p := by
  classical
  have hb₁ : CFSG.BenderSuzuki.IsBenderGroup Y₁ :=
    CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup (uc22p2214_bor_bender_L2 h₁)
  have hb₂ : CFSG.BenderSuzuki.IsBenderGroup Y₂ :=
    CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup (uc22p2214_bor_bender_U3 h₂)
  haveI : IsSimpleGroup Y₁ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hb₁
  haveI : IsSimpleGroup Y₂ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hb₂
  have hZ₁ : Subgroup.center Y₁ = ⊥ :=
    CFSG.BenderSuzuki.center_eq_bot_of_isSimpleGroup_of_not_commutative inferInstance (by
      obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hb₁
      exact fun h => hab ((commute_iff_eq a b).mpr (h a b)))
  have hZ₂ : Subgroup.center Y₂ = ⊥ :=
    CFSG.BenderSuzuki.center_eq_bot_of_isSimpleGroup_of_not_commutative inferInstance (by
      obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hb₂
      exact fun h => hab ((commute_iff_eq a b).mpr (h a b)))
  intro A t hAcard ht hinv Q hQ hQB
  haveI : IsMulCommutative ↥A :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isMulCommutative_of_isZModSq hAcard
  have hAmm : Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_eq_of_isZModSq hAcard
  have hn1 : 1 ≤ n := by omega
  have hm : 1 < 2 ^ n - 1 := by
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hmodd : Odd (2 ^ n - 1) := uc22pwsu3_odd_two_pow_sub_one hn1
  have hcard₁ : Nat.card Y₁ = (2 ^ n - 1) * (2 ^ n * (2 ^ n + 1)) :=
    card_isL2_torus_factor h₁
  have hcard₂ : Nat.card Y₂ = (2 ^ n - 1) *
      ((2 ^ n) ^ 3 * (2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 - 2 ^ n + 1)) :=
    card_isU3_torus_factor h₂ heven
  have hcop₁ : Nat.Coprime (2 ^ n - 1) (2 ^ n * (2 ^ n + 1)) := coprime_torus_isL2 hn1
  have hcop₂ : Nat.Coprime (2 ^ n - 1)
      ((2 ^ n) ^ 3 * (2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 - 2 ^ n + 1)) :=
    coprime_torus_isU3 hn1
  have hN₁ : ∀ B : Subgroup Y₁, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₁,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₁,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₁) → s ∈ normalizer (R : Set Y₁) → R = ⊥ :=
    fun B hB hodd s hs hinv R hR hBR hsR =>
      k1911_eq_bot_of_bender (Or.inl h₁) hB hodd hs hinv hR hBR hsR
  have hN₂ : ∀ B : Subgroup Y₂, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₂,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₂,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₂) → s ∈ normalizer (R : Set Y₂) → R = ⊥ :=
    fun B hB hodd s hs hinv R hR hBR hsR =>
      k1911_eq_bot_of_bender (Or.inr (Or.inr h₂)) hB hodd hs hinv hR hBR hsR
  obtain ⟨hAcard₁, hAcard₂, -, hQshape⟩ :=
    CFSG.GroupTheory.prod_aut_fix_of_forall_eq_bot hZ₁ hZ₂ hm hmodd hcard₁ hcard₂ hcop₁ hcop₂
      hN₁ hN₂ hAmm ht hinv hQ hQB
  have hTcomm₁ : IsMulCommutative (A.map (MonoidHom.fst Y₁ Y₂)) := inferInstance
  have hTcomm₂ : IsMulCommutative (A.map (MonoidHom.snd Y₁ Y₂)) := inferInstance
  have hp₁ : p ∣ Nat.card Y₁ :=
    hpd.trans
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.two_pow_add_one_dvd_card_of_isL2_psl_two h₁)
  have hp₂ : p ∣ Nat.card Y₂ := by
    rw [hcard₂]
    have h2 : p ∣ (2 ^ n + 1) ^ 2 := by
      rw [pow_two]
      exact hpd.trans (dvd_mul_right _ _)
    have h3 : p ∣ (2 ^ n) ^ 3 * (2 ^ n + 1) ^ 2 := dvd_mul_of_dvd_right h2 _
    have h4 : p ∣ ((2 ^ n) ^ 3 * (2 ^ n + 1) ^ 2) * ((2 ^ n) ^ 2 - 2 ^ n + 1) :=
      dvd_mul_of_dvd_left h3 _
    exact dvd_mul_of_dvd_right h4 _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' p hp₁
  obtain ⟨y₂, hy₂, hy₂fix⟩ :=
    exists_orderOf_fixed_of_isU3 h₂ hn heven hTcomm₂ hAcard₂ hp hpd
  refine ⟨(Subgroup.zpowers y₁).prod (Subgroup.zpowers y₂), ?_, ?_, ?_⟩
  · refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
    · exact (Subgroup.prodEquiv (Subgroup.zpowers y₁) (Subgroup.zpowers y₂)).injective (by
        rw [map_mul, map_mul]
        exact mul_comm' _ _)
    · intro x hx
      have h1 : orderOf x.1 ∣ p := by
        rw [← hy₁]
        exact orderOf_dvd_of_mem_zpowers hx.1
      have h2 : orderOf x.2 ∣ p := by
        rw [← hy₂]
        exact orderOf_dvd_of_mem_zpowers hx.2
      exact Prod.ext (orderOf_dvd_iff_pow_eq_one.mp h1) (orderOf_dvd_iff_pow_eq_one.mp h2)
  · calc Nat.card ((Subgroup.zpowers y₁).prod (Subgroup.zpowers y₂))
        = Nat.card (↥(Subgroup.zpowers y₁) × ↥(Subgroup.zpowers y₂)) :=
          Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv
      _ = Nat.card (Subgroup.zpowers y₁) * Nat.card (Subgroup.zpowers y₂) := Nat.card_prod _ _
      _ = p * p := by rw [Nat.card_zpowers, Nat.card_zpowers, hy₁, hy₂]
      _ = p ^ 2 := by ring
  · intro α hα
    obtain ⟨β₁, β₂, hαeq, hβ₁ord, hβ₂ord, hβ₁fix, hβ₂fix⟩ := hQshape α hα
    have hβ₁one : β₁ = 1 :=
      eq_one_of_isL2_of_fix_of_two_pow h₁ hn hTcomm₁ hAcard₁ β₁ hβ₁ord hβ₁fix
    intro e he
    obtain ⟨a, b⟩ := e
    have hb : β₂ b = b := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp he.2
      calc β₂ b = β₂ (y₂ ^ m) := by rw [hm]
        _ = (β₂ y₂) ^ m := map_zpow β₂ y₂ m
        _ = y₂ ^ m := by rw [hy₂fix β₂ hβ₂ord hβ₂fix]
        _ = b := hm
    rw [hαeq, CFSG.GroupTheory.mulAutProdHom_apply, hβ₁one]
    exact Prod.ext rfl hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
