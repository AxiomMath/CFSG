module

public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofComp
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCentTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.GH74.GLS

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem eq_of_le_sup_centralizer_of_three {J X Y A : Subgroup Γ} {e : Γ}
    (hJX : J ≤ X) (hXY : X ≤ Y)
    (hXJC : X ≤ J ⊔ Subgroup.centralizer (J : Set Γ))
    (hZ : J ⊓ Subgroup.centralizer (J : Set Γ) = ⊥)
    (hYX : Y ≤ Subgroup.normalizer (X : Set Γ))
    (hY3 : ∀ P : Subgroup Γ, P ≤ Y → Y ≤ Subgroup.normalizer (P : Set Γ) →
      ¬ 3 ∣ Nat.card P → P = ⊥)
    (hA : IsPGroup 3 A) (hAX : A ≤ Subgroup.normalizer (X : Set Γ))
    (hAJ : A ≤ Subgroup.normalizer (J : Set Γ))
    (hF : ∀ w ∈ Y, w ∈ Subgroup.centralizer (A : Set Γ) → w ^ 3 = 1 →
      w ∈ Subgroup.zpowers e)
    (he : e ∈ J) : X = J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup Γ := X ⊓ Subgroup.centralizer (J : Set Γ)
  have hAD : A ≤ Subgroup.normalizer (D : Set Γ) := fun a ha =>
    CFSG.RankThree.PartTwo.Sec14.Ronan148N.mem_normalizer_inf148 (hAX ha)
      (CFSG.RankThree.PartTwo.Sec14.Ronan148N.mem_normalizer_centralizer148 (hAJ ha))
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3D
    have hmod := CFSG.RankThree.PartTwo.Sec6.card_inf_centralizer_modEq hA hAD
    have h3C : 3 ∣ Nat.card (D ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) :=
      Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr h3D))
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3C
    have hw' : orderOf (w : Γ) = 3 := by rw [Subgroup.orderOf_coe]; exact hw
    have hw3 : (w : Γ) ^ 3 = 1 := by rw [← hw']; exact pow_orderOf_eq_one _
    have hwX : (w : Γ) ∈ X := w.2.1.1
    have hwC : (w : Γ) ∈ Subgroup.centralizer (J : Set Γ) := w.2.1.2
    have hwe : (w : Γ) ∈ Subgroup.zpowers e := hF _ (hXY hwX) w.2.2 hw3
    have hweJ : (w : Γ) ∈ J := Subgroup.zpowers_le.mpr he hwe
    have hw1 : (w : Γ) = 1 := by
      have hmem : (w : Γ) ∈ J ⊓ Subgroup.centralizer (J : Set Γ) :=
        Subgroup.mem_inf.mpr ⟨hweJ, hwC⟩
      rw [hZ] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hw1, orderOf_one] at hw'
    exact absurd hw' (by norm_num)
  have hDX : D ≤ pPrimeCoreOf 3 X := by
    refine CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf inf_le_left ?_
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3)
    intro x hx
    obtain ⟨j, hj, c, hc, rfl⟩ :=
      CFSG.RankThree.PartTwo.Sec14.Item148Res5.mem_sup_centralizer_iff.mp (hXJC hx)
    have hjN : j ∈ Subgroup.normalizer (Subgroup.centralizer (J : Set Γ) : Set Γ) :=
      CFSG.RankThree.PartTwo.Sec14.Ronan148N.mem_normalizer_centralizer148
        (Subgroup.le_normalizer hj)
    have hcN : c ∈ Subgroup.normalizer (Subgroup.centralizer (J : Set Γ) : Set Γ) :=
      Subgroup.le_normalizer hc
    exact CFSG.RankThree.PartTwo.Sec14.Ronan148N.mem_normalizer_inf148
      (Subgroup.le_normalizer hx) (mul_mem hjN hcN)
  have hPbot : pPrimeCoreOf 3 X = ⊥ := by
    refine hY3 (pPrimeCoreOf 3 X)
      ((CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 X).trans hXY)
      (hYX.trans (CFSG.RankThree.PartTwo.Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 X)) ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 X)
  have hDbot : D ≤ ⊥ := hDX.trans hPbot.le
  refine le_antisymm ?_ hJX
  intro x hx
  obtain ⟨j, hj, c, hc, hjc⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Item148Res5.mem_sup_centralizer_iff.mp (hXJC hx)
  have hc' : c = j⁻¹ * x := by rw [← hjc, inv_mul_cancel_left]
  have hcX : c ∈ X := by
    rw [hc']
    exact X.mul_mem (X.inv_mem (hJX hj)) hx
  have hcD : c ∈ D := Subgroup.mem_inf.mpr ⟨hcX, hc⟩
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hDbot hcD)
  rw [← hjc, hc1, mul_one]
  exact hj

theorem card_zpowers_sup_zpowers_le {x y : Γ} (hxy : x * y = y * x) (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup Γ) ≤ 9 := by
  have hc : Commute x y := hxy
  have hyC : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp ha)
    exact hc.zpow_left k
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set Γ) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set Γ) hyC)
  have hprod := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers x)
    (Subgroup.zpowers y) hN
  have hsurj : Function.Surjective (fun p : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y) =>
      (⟨(p.1 : Γ) * (p.2 : Γ), mul_mem (Subgroup.mem_sup_left p.1.2)
        (Subgroup.mem_sup_right p.2.2)⟩ :
          ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup Γ))) := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ (↑(Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup Γ) : Set Γ) := hg
    rw [hprod] at hg'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hg'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers] at hle
  have hx3 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx)
  have hy3 : orderOf y ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy)
  exact le_trans hle (le_trans (Nat.mul_le_mul hx3 hy3) (by norm_num))

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
