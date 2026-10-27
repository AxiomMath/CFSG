module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XOuterThree
import CFSG.Adapters.LieModelSimple
import CFSG.Timmesfeld.Orders.Classical
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

private theorem n924x_card_psl2 {Y : Type} [Group Y] {m : ℕ}
    (h : StatedClassicalModel Y .PSL 2 2 m) :
    Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hf : 1 ≤ m := h.1.2.1
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have hodd : Odd (2 ^ m - 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (n := 1) le_rfl
  have hgcd : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [h1]
  unfold CFSG.Open.ordA
  norm_num [Finset.Icc_self, hgcd]

theorem mem_of_isPGroup_three_of_isL2_normal {Z : Type} [Group Z] [Finite Z] {X : Subgroup Z}
    {m : ℕ} (hXn : X.Normal) (hX : IsL2 ↥X m) (hZ : ¬ HasE9 Z) {z : Z}
    (hz : IsPGroup 3 (Subgroup.zpowers z)) : z ∈ X := by
  classical
  haveI := hXn
  have hSC : CFSG.Blueprint.LieModel ↥X .PSL 2 2 m := hX
  have hmodel : StatedClassicalModel ↥X .PSL 2 2 m := hSC.statedClassicalModel (by decide)
  have hsimple : IsSimpleGroup ↥X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSC
  have hcard : Nat.card ↥X = 2 ^ m * ((2 ^ m) ^ 2 - 1) := n924x_card_psl2 hmodel
  have hm : 2 ≤ m := by
    have h1 : 1 ≤ m := hmodel.1.2.1
    have hne : (2, 2 ^ m) ≠ (2, 2) := hmodel.1.2.2.2.1
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hne (by norm_num)
    omega
  have hnc : ¬ IsMulCommutative ↥X := by
    intro hcomm
    haveI : IsMulCommutative ↥X := hcomm
    have hprime : (Nat.card ↥X).Prime := (Group.is_simple_iff_prime_card).mp hsimple
    rw [hcard] at hprime
    have h2m : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsq : 4 ≤ (2 ^ m) ^ 2 := by
      simpa using Nat.pow_le_pow_left h2m 2
    have ha : 2 ^ m ≠ 1 := by omega
    have hb : (2 ^ m) ^ 2 - 1 ≠ 1 := by omega
    exact Nat.not_prime_mul (a := 2 ^ m) (b := (2 ^ m) ^ 2 - 1) ha hb hprime
  have hcenter : Subgroup.center ↥X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥X) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc
  have h3card : 3 ∣ Nat.card ↥X := by
    rw [hcard]
    have hpow : (2 ^ m) ^ 2 = 4 ^ m := by
      rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      congr 1
      ring
    have h3 : 3 ∣ (2 ^ m) ^ 2 - 1 := by
      rw [hpow]
      simpa using Nat.sub_one_dvd_pow_sub_one 4 m
    exact dvd_mul_of_dvd_right h3 (2 ^ m)
  let ρ : Z →* MulAut ↥X := MulAut.conjNormal
  have hker_comm : ∀ c : Z, c ∈ ρ.ker → ∀ x : ↥X, c * (x : Z) = (x : Z) * c := by
    intro c hc x
    have h1 : ρ c = 1 := MonoidHom.mem_ker.mp hc
    have h2 : ρ c x = x := by rw [h1]; simp
    have h3 : c * (x : Z) * c⁻¹ = (x : Z) := by
      have h := congrArg Subtype.val h2
      simpa [ρ, MulAut.conjNormal_apply] using h
    calc c * (x : Z) = c * (x : Z) * c⁻¹ * c := by group
      _ = (x : Z) * c := by rw [h3]
  have hCbot : ρ.ker ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hmem : (⟨g, hg.2⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hker_comm g hg.1 y).symm
    rw [hcenter] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hC3' : ¬ 3 ∣ Nat.card ρ.ker := by
    intro hdvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ρ.ker) 3 hdvd
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3card
    have hcd : Commute (c : Z) (d : Z) :=
      (commute_iff_eq _ _).mpr (hker_comm (c : Z) c.2 d)
    have hmem : (d : Z) ∉ Subgroup.zpowers (c : Z) := by
      intro hmem
      have hmemker : (d : Z) ∈ ρ.ker := Subgroup.zpowers_le.mpr c.2 hmem
      have hbot : (d : Z) ∈ ρ.ker ⊓ X := ⟨hmemker, d.2⟩
      rw [hCbot, Subgroup.mem_bot] at hbot
      have h3eq : orderOf (d : Z) = 3 := by rw [Subgroup.orderOf_coe, hd]
      rw [hbot, orderOf_one] at h3eq
      exact absurd h3eq (by norm_num)
    exact hZ ⟨(c : Z), (d : Z), by rw [Subgroup.orderOf_coe, hc],
      by rw [Subgroup.orderOf_coe, hd], hcd, hmem⟩
  have hz3 : IsPGroup 3 (Subgroup.zpowers (ρ z)) := by
    have h := hz.map ρ
    rwa [MonoidHom.map_zpowers] at h
  have hAinner : (MulAut.conj : ↥X →* MulAut ↥X).range ≤ ρ.range := by
    rintro g ⟨x, rfl⟩
    exact ⟨(x : Z), by
      change MulAut.conjNormal (x : Z) = MulAut.conj x
      rw [MulAut.conjNormal_val]⟩
  have hNoE9A : ¬ HasE9 ↥ρ.range := by
    intro hE9
    have e := QuotientGroup.quotientKerEquivRange ρ
    have hq : HasE9 (Z ⧸ ρ.ker) :=
      HasE9.map_injective (e.symm : ↥ρ.range →* Z ⧸ ρ.ker) e.symm.injective hE9
    exact hZ (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient ρ.ker hC3' hq)
  have hzA : ρ z ∈ ρ.range := ⟨z, rfl⟩
  by_cases hinner : ρ z ∈ (MulAut.conj : ↥X →* MulAut ↥X).range
  · obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.mp hinner
    have hρx₀ : ρ (x₀ : Z) = ρ z := by
      change MulAut.conjNormal (x₀ : Z) = ρ z
      rw [MulAut.conjNormal_val, hx₀]
    let c : Z := z * (x₀ : Z)⁻¹
    have hc_ker : c ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      show ρ (z * (x₀ : Z)⁻¹) = 1
      rw [map_mul, map_inv, hρx₀, mul_inv_cancel]
    have hz_eq : z = c * (x₀ : Z) := by
      simp only [c]
      group
    have hc_comm_x₀ : Commute c (x₀ : Z) :=
      (commute_iff_eq _ _).mpr (hker_comm c hc_ker x₀)
    obtain ⟨k, hk⟩ := hz ⟨z, Subgroup.mem_zpowers z⟩
    have hkz : z ^ (3 ^ k) = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    have hzpow : z ^ (3 ^ k) = c ^ (3 ^ k) * (x₀ : Z) ^ (3 ^ k) := by
      rw [hz_eq, hc_comm_x₀.mul_pow]
    have hc_pow : c ^ (3 ^ k) = 1 := by
      have h1 : c ^ (3 ^ k) * (x₀ : Z) ^ (3 ^ k) = 1 := by
        rw [← hzpow, hkz]
      have h2 : c ^ (3 ^ k) = ((x₀ : Z) ^ (3 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hbot : c ^ (3 ^ k) ∈ ρ.ker ⊓ X :=
        ⟨ρ.ker.pow_mem hc_ker _, by rw [h2]; exact X.inv_mem (X.pow_mem x₀.2 _)⟩
      rwa [hCbot, Subgroup.mem_bot] at hbot
    have hc_dvd : orderOf c ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hc_pow
    have hcardc : orderOf c ∣ Nat.card ρ.ker := Subgroup.orderOf_dvd_natCard ρ.ker hc_ker
    have hcop3 : Nat.Coprime 3 (Nat.card ρ.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3'
    have hcop : Nat.Coprime (orderOf c) (Nat.card ρ.ker) :=
      Nat.Coprime.of_dvd_left hc_dvd (hcop3.pow_left k)
    have hc1 : c = 1 := by
      have h : orderOf c = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (dvd_refl (orderOf c)) hcardc
      exact orderOf_eq_one_iff.mp h
    rw [hz_eq, hc1, one_mul]
    exact x₀.2
  · exact absurd (hasE9_of_outer_three hX hAinner hzA hz3 hinner) hNoE9A

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
