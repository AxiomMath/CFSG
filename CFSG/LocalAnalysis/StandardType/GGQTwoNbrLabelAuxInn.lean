module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

private theorem qTwoNbrLabel_card_outer_centerQuot {L : Subgroup G} {m : ℕ}
    (h3 : ¬ 3 ∣ m) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) :
    Nat.card (Outer (L ⧸ Subgroup.center L)) = 2 := by
  have h4 : 4 ≤ m := qTwoLMFrameC_four_le hL
  have h := LieModel.card_outer_psu hL (by omega) (by rintro ⟨hm, -⟩; omega)
  rw [h]
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hg : Nat.gcd m 3 = 1 := by
    rw [Nat.gcd_comm]
    exact hcop.gcd_eq_one
  rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, hg]

theorem qTwoNbrLabel_inner {Bs K : Subgroup G} (hperf : commutator ↥K = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hK : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 2 1) {b : G} (hb : b ∈ Bs)
    (hb3 : b ^ 3 = 1) :
    ∃ a : ↥K, ∀ k : ↥K, b * (k : G) * b⁻¹ = ((a * k * a⁻¹ : ↥K) : G) := by
  let β : ↥Bs := ⟨b, hb⟩
  let a₀ : MulAut ↥K := ggGamma K hN β
  have hβ3 : β ^ 3 = 1 := by
    apply Subtype.ext
    exact hb3
  have ha3 : a₀ ^ 3 = 1 := by
    change (ggGamma K hN β) ^ 3 = 1
    rw [← map_pow, hβ3, map_one]
  haveI : Group.IsPerfect ↥K := ⟨hperf⟩
  have hcard_dvd : Nat.card (Outer ↥K) ∣ 2 := by
    have h1 := Subgroup.card_dvd_of_injective (centerQuotientOuterHom ↥K)
      (centerQuotient_outer_injective ↥K)
    rwa [qTwoNbrLabel_card_outer_centerQuot (L := K) (by norm_num) hK] at h1
  set c : Outer ↥K :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K) a₀ with hc
  have hc3 : c ^ 3 = 1 := by
    rw [hc]
    rw [← map_pow, ha3, map_one]
  have hc2 : c ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hcard_dvd
    rw [hk, pow_mul, pow_card_eq_one' (x := c), one_pow]
  have hc1 : c = 1 := by
    have h : c ^ 3 * (c ^ 2)⁻¹ = 1 := by rw [hc3, hc2, inv_one, mul_one]
    rw [← h]
    group
  obtain ⟨a, ha⟩ : ∃ a : ↥K, MulAut.conj a = a₀ := by
    have hmem : a₀ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
      rw [← QuotientGroup.eq_one_iff a₀]
      simpa using hc.symm.trans hc1
    exact MonoidHom.mem_range.mp (show a₀ ∈ (MulAut.conj : ↥K →* MulAut ↥K).range from hmem)
  refine ⟨a, fun k => ?_⟩
  have h1 : a₀ k = a * k * a⁻¹ := by
    rw [← ha, MulAut.conj_apply]
  calc b * (k : G) * b⁻¹ = ((a₀ k : ↥K) : G) := (ggGamma_coe K hN β k).symm
    _ = ((a * k * a⁻¹ : ↥K) : G) := by rw [h1]

end CFSG.StandardType.QTwo

end
