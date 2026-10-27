module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LD4Cent

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU)
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open Matrix (ProjGenLinGroup)

section Orders

theorem card_projSU_bounds {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (projSU 3 2 n) ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) ∧
      1 < Nat.card (projSU 3 2 n) := by
  have hGF : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have h : Nat.card (projSU 3 2 n) * Nat.gcd 3 (2 ^ n + 1) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    rw [← CFSG.PGLModel.projImage_statedSU 3 2 n]
    exact card_projImage_slPi_false_mul hGF
  have hg1 : 1 ≤ Nat.gcd 3 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq2 : 3 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  have hq3 : 9 ≤ (2 ^ n) ^ 3 + 1 := by
    have : 8 ≤ (2 ^ n) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have hq1 : 8 ≤ (2 ^ n) ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
  set N := Nat.card (projSU 3 2 n) with hN
  refine ⟨?_, ?_⟩
  · calc N = N * 1 := (mul_one N).symm
      _ ≤ N * Nat.gcd 3 (2 ^ n + 1) := Nat.mul_le_mul_left _ hg1
      _ = _ := h
  · by_contra hle
    push Not at hle
    have h1 : N * Nat.gcd 3 (2 ^ n + 1) ≤ 1 * 3 := Nat.mul_le_mul hle hg3
    rw [h] at h1
    have h2 : 8 * 3 * 9 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq1 hq2) hq3
    omega

theorem card_projSU_lt_ordG2 {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (projSU 3 2 n) < CFSG.Open.ordG2 (2 ^ n) := by
  refine lt_of_le_of_lt (card_projSU_bounds hn).1 ?_
  unfold CFSG.Open.ordG2
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set Q := 2 ^ n with hQ
  have hQ3 : 8 ≤ Q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hq 3
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hQ6 : Q ^ 6 = Q ^ 3 * Q ^ 3 := by ring
  have hQ6' : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < Q ^ 2 - 1 := by
    have : 4 ≤ Q ^ 2 := by nlinarith
    omega
  have key : Q ^ 3 * (Q ^ 3 + 1) < Q ^ 6 * (Q ^ 6 - 1) := by
    rw [hQ6]
    have h1 : Q ^ 3 + 1 ≤ Q ^ 3 * Q ^ 3 - 1 := by
      have : 8 * Q ^ 3 ≤ Q ^ 3 * Q ^ 3 := Nat.mul_le_mul_right _ hQ3
      omega
    have h2 : Q ^ 3 < Q ^ 3 * Q ^ 3 := by nlinarith
    calc Q ^ 3 * (Q ^ 3 + 1) < Q ^ 3 * Q ^ 3 * (Q ^ 3 + 1) :=
          Nat.mul_lt_mul_of_pos_right h2 (by omega)
      _ ≤ Q ^ 3 * Q ^ 3 * (Q ^ 3 * Q ^ 3 - 1) := Nat.mul_le_mul_left _ h1
  calc Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) = Q ^ 3 * (Q ^ 3 + 1) * (Q ^ 2 - 1) := by ring
    _ < Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right key hpos

end Orders

section Excl


theorem kf138TrialityG2Excl : KF138TrialityG2Excl := by
  intro n hn hn1 h3n K _ _ hK σ hσ α hstd Y hYα hYsn hYp π hπ hker
  have hn0 : 1 ≤ n := by omega
  haveI : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨eG⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hK2
  have hk : Nat.card (fixSubfield σ) = 2 ^ n := card_fixSubfield_of_cube hn0 hK hσ
  have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ) hk3
  have hZ : Subgroup.center ↥(adjointGroup .G2 (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  haveI : IsSimpleGroup ↥(adjointGroup .G2 (fixSubfield σ)) :=
    CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  have hE0 : autFix (fieldActor (t := TwistTag.D4) σ σ) =
      (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext x
    exact Iff.rfl
  obtain ⟨β, hβ⟩ := hstd
  have hcongr : ∀ γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      MulAut.congr β γ = β * γ * β⁻¹ := fun γ => MulEquiv.ext fun _ => rfl
  have hinv : ∀ γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      autFix γ⁻¹ = autFix γ := by
    intro γ
    ext x
    rw [mem_autFix, mem_autFix]
    constructor
    · intro h
      have h1 := congrArg γ h
      rw [MulAut.apply_inv_self] at h1
      exact h1.symm
    · intro h
      have h1 := congrArg (fun z => (γ⁻¹ : MulAut _) z) h
      simp only [MulAut.inv_apply_self] at h1
      exact h1.symm
  have hα' : autFix α = (autFix (fieldActor (t := TwistTag.D4) σ σ)).map β.toMonoidHom := by
    rcases hβ with h | h
    · rw [h, ← hcongr, autFix_congr]
    · rw [h, ← hcongr, autFix_congr, hinv]
  let eE : ↥(autFix α) ≃* ↥(adjointGroup .G2 (fixSubfield σ)) :=
    (MulEquiv.subgroupCongr hα').trans
      (((autFix (fieldActor (t := TwistTag.D4) σ σ)).equivMapOfInjective β.toMonoidHom
        β.injective).symm.trans ((MulEquiv.subgroupCongr hE0).trans eG))
  haveI hsE : IsSimpleGroup ↥(autFix α) := eE.isSimpleGroup
  have hEcard : Nat.card ↥(autFix α) = CFSG.Open.ordG2 (2 ^ n) := by
    rw [Nat.card_congr eE.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  have hYE : Y ≤ autFix α := fun y hy => mem_autFix.mpr (hYα y hy)
  have hbounds := card_projSU_bounds hn0
  have hlt := card_projSU_lt_ordG2 hn0
  have hsurj : Nat.card (projSU 3 2 n) ≤ Nat.card Y := Nat.card_le_card_of_surjective _ hπ
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsE hYsn with h | h
  ·
    have hY1 : Y = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : (⟨y, hYE hy⟩ : ↥(autFix α)) ∈ Y.subgroupOf (autFix α) := hy
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    rw [hY1, Subgroup.card_bot] at hsurj
    omega
  ·
    have hYeq : Y = autFix α := by
      refine le_antisymm hYE fun y hy => ?_
      have : (⟨y, hy⟩ : ↥(autFix α)) ∈ Y.subgroupOf (autFix α) := by
        rw [h]; exact Subgroup.mem_top _
      exact this
    have eY : ↥Y ≃* ↥(autFix α) := MulEquiv.subgroupCongr hYeq
    haveI : IsSimpleGroup ↥Y := eY.isSimpleGroup
    have hYcard : Nat.card ↥Y = CFSG.Open.ordG2 (2 ^ n) := by
      rw [Nat.card_congr eY.toEquiv, hEcard]
    haveI : π.ker.Normal := MonoidHom.normal_ker π
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk' | hk'
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hk'
      have := Nat.card_le_card_of_injective _ hinj
      omega
    ·
      have h1 : ∀ z : projSU 3 2 n, z = 1 := by
        intro z
        obtain ⟨y, rfl⟩ := hπ z
        have : y ∈ π.ker := by rw [hk']; exact Subgroup.mem_top y
        exact this
      have : Nat.card (projSU 3 2 n) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h1 a, h1 b]⟩, ⟨1⟩⟩
      omega


theorem kf138TrialityPGUCent : KF138TrialityPGUCent :=
  kf138TrialityPGUCent_of_g2Excl kf138TrialityG2Excl

end Excl

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
