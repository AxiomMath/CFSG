module

public import CFSG.Quasithin.Background.C124YLA7Grp
public import CFSG.Quasithin.Background.C124YLA7Off

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open CFSG.QuasithinUnique.L246.C123


theorem isKleinConj_kleinA : IsKleinConj kleinA := ⟨1, by
  ext x
  rw [_root_.CFSG.QuasithinUnique.L246.C123.mem_conjSub]
  simp⟩

section Generic

variable {U : Type} [CommGroup U] (ρ : A7 →* MulAut U)

theorem mem_kleinA_of_fix (hcard : Nat.card U = 16) (hinj : Function.Injective ρ) {σ : A7}
    (h2 : ∃ k : ℕ, σ ^ 2 ^ k = 1) (hN : σ ∈ Subgroup.normalizer (kleinA : Set A7))
    (hfix : ∀ u ∈ fixU ρ kleinA, ρ σ u = u) (h4 : 4 ≤ Nat.card (fixU ρ kleinA)) :
    σ ∈ kleinA := by
  by_contra hσK
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hKp : IsPGroup 2 kleinA := IsPGroup.of_card (n := 2) (by rw [card_kleinA]; norm_num)
  have hzp : IsPGroup 2 (Subgroup.zpowers σ) := by
    obtain ⟨k, hk⟩ := h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hzN : Subgroup.zpowers σ ≤ Subgroup.normalizer (kleinA : Set A7) :=
    Subgroup.zpowers_le.2 hN
  have hHp := hzp.to_sup_of_normal_right' hKp hzN
  obtain ⟨T, hHT, hT⟩ := exists_sylow_ge hHp
  set H : Subgroup A7 := Subgroup.zpowers σ ⊔ kleinA with hH
  have hσH : σ ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers σ)
  have hlt : kleinA < H := lt_of_le_of_ne le_sup_right fun h => hσK (by rw [h]; exact hσH)
  have hlt4 : 4 < Nat.card H := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [card_kleinA] at this
  have h4dvd : 4 ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_le (le_sup_right : kleinA ≤ H)
    rwa [card_kleinA] at this
  have hle8 : Nat.card H ≤ 8 := by
    have := Subgroup.card_le_of_le hHT
    omega
  have h8 : Nat.card H = 8 := by omega
  have hsub : fixU ρ kleinA ≤ fixU ρ H := by
    intro u hu
    have hle : H ≤ stabU ρ u := sup_le (Subgroup.zpowers_le.2 (mem_stabU.2 (hfix u hu)))
      fun k hk => mem_stabU.2 (mem_fixU.1 hu k hk)
    exact mem_fixU.2 fun h hh => mem_stabU.1 (hle hh)
  have := Subgroup.card_le_of_le hsub
  have := card_fixU_le_two ρ hcard hinj h8
  omega

theorem exists_move_Yst (hcard : Nat.card U = 16) (hinj : Function.Injective ρ)
    (h4 : 4 ≤ Nat.card (fixU ρ kleinA)) : ∃ q ∈ fixU ρ kleinA, ∃ y ∈ Yst, ρ y q ≠ q := by
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial (fixU ρ kleinA) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨q, hq⟩, hq1⟩ := exists_ne (1 : ↥(fixU ρ kleinA))
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  refine ⟨q, hq, ?_⟩
  by_contra hno
  push Not at hno
  have hle : Yst ≤ stabU ρ q := fun y hy => mem_stabU.2 (hno y hy)
  have h60 : 60 ∣ Nat.card (stabU ρ q) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_Yst] at this
  exact not_dvd_five_card_stabU ρ hcard hinj hq1' (Nat.dvd_trans (by norm_num) h60)

end Generic

end CFSG.Quasithin.C124.YL.A7
