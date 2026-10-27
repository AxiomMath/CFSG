module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sec7ctr_exists_fixed_mod {T D V : Subgroup G} (hT : IsPGroup 2 ↥T) (hD2 : IsPGroup 2 ↥D)
    (hVD : V < D) (hcomm : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ D, x ^ 2 ∈ V)
    (hTD : ∀ r ∈ T, ∀ x ∈ D, r * x * r⁻¹ ∈ D) (hTV : ∀ r ∈ T, ∀ x ∈ V, r * x * r⁻¹ ∈ V) :
    ∃ d ∈ D, d ∉ V ∧ ∀ l ∈ T, ⁅l, d⁆ ∈ V := by
  haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSec : SecHyp T D V := ⟨hVD.le, hcomm, hsq, hTD, hTV⟩
  obtain ⟨Md, _, _, κ, hκ⟩ := exists_sectionModule hSec
  haveI hMdfin : Finite Md := hκ.finite
  have hsec : Nat.card ↥D = Nat.card ↥V * Nat.card Md := natCard_eq_of_isSecMod hVD.le hκ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hD2
  have hdvd : Nat.card Md ∣ Nat.card ↥D := by
    rw [hsec]
    exact dvd_mul_left _ _
  rw [hn] at hdvd
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h1 : Nat.card Md = 1 := by rw [hm, pow_zero]
    have hlt := Subgroup.card_lt_of_lt hVD
    rw [hsec, h1, mul_one] at hlt
    exact lt_irrefl _ hlt
  have h2 : 2 ∣ Nat.card Md := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  have hzero : (0 : Md) ∈ MulAction.fixedPoints ↥T Md :=
    MulAction.mem_fixedPoints.mpr fun g => smul_zero g
  obtain ⟨b, hb, hb0⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hT Md h2 hzero
  have hfix : ∀ l : ↥T, l • b = b := MulAction.mem_fixedPoints.mp hb
  obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd b)
  have hdV : (x : G) ∉ V := by
    intro hxV
    have h1 : κ x = 1 := (hκ.ker x).mpr hxV
    rw [hx] at h1
    exact hb0 (ofAdd_eq_one.mp h1).symm
  refine ⟨(x : G), x.2, hdV, fun l hl => ?_⟩
  have hy := hκ.act ⟨l, hl⟩ x ⟨l * (x : G) * l⁻¹, hTD l hl (x : G) x.2⟩ rfl
  have key : κ ⟨l * (x : G) * l⁻¹, hTD l hl (x : G) x.2⟩ = κ x := by
    rw [hy, hx, toAdd_ofAdd]
    exact congrArg Multiplicative.ofAdd (hfix ⟨l, hl⟩)
  have h3 := (hκ.eq_iff ⟨l * (x : G) * l⁻¹, hTD l hl (x : G) x.2⟩ x).mp key
  rw [commutatorElement_def]
  exact h3

end CFSG.RankThree.GF2n.Stroth80
