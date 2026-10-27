module

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.TwoA.Census.CentralSqrt

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.B.Short
open scoped commutatorElement

namespace GeneratedPerfectCover

theorem Cbar_exists_ne_comm : ∃ a b : Cbar, a * b ≠ b * a := by
  obtain ⟨-, hnt, -, -⟩ := short_centralizer_generated_quotient_simple
  obtain ⟨c, hc⟩ := exists_ne (1 : Cbar)
  have hcz : c ∉ Subgroup.center Cbar := by
    rw [center_Cbar, Subgroup.mem_bot]
    exact hc
  rw [Subgroup.mem_center_iff] at hcz
  push Not at hcz
  obtain ⟨d, hd⟩ := hcz
  exact ⟨d, c, hd⟩

theorem center_Cgen : Subgroup.center Cgen = Zstar := by
  refine le_antisymm (fun z hz => ?_) Zstar_le_center
  have hcen : kappa z ∈ Subgroup.center Cbar := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨g, rfl⟩ := kappa_surjective c
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
  rw [center_Cbar, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_kappa] at hcen
  exact hcen

theorem commutator_Cbar : commutator Cbar = ⊤ := by
  obtain ⟨-, -, hs, -⟩ := short_centralizer_generated_quotient_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Cbar) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := Cbar_exists_ne_comm
    have hc : ⁅a, b⁆ ∈ commutator Cbar := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

theorem exists_mem_commutator_inv_mul_mem_Zstar (g : Cgen) :
    ∃ n ∈ commutator Cgen, n⁻¹ * g ∈ Zstar := by
  have hmap : (commutator Cgen).map kappa = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ kappa_surjective,
      ← commutator_def, commutator_Cbar]
  have hg : kappa g ∈ (commutator Cgen).map kappa := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hng⟩ := hg
  refine ⟨n, hn, ?_⟩
  rw [← ker_kappa, MonoidHom.mem_ker, map_mul, map_inv, hng, inv_mul_cancel]

theorem commutator_Cgen :
    commutator Cgen = ⊤ := by
  have hsq := TwoA.Census.short_centralizer_central_square_root.2.2.2.2.2.1
  have hcmem := TwoA.Census.short_centralizer_central_square_root.2.2.2.2.2.2.2.2.2
  have hc2 : (⟨TwoA.Census.cSqrt, hcmem⟩ : Cgen) * ⟨TwoA.Census.cSqrt, hcmem⟩ = tStarC :=
    Subtype.ext hsq
  have hgen : ∀ g : Cgen, ∃ k : ℤ, (QuotientGroup.mk g : Cgen ⧸ commutator Cgen) =
      (QuotientGroup.mk tStarC : Cgen ⧸ commutator Cgen) ^ k := by
    intro g
    obtain ⟨n, hn, hz⟩ := exists_mem_commutator_inv_mul_mem_Zstar g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨k, ?_⟩
    have e : g = n * tStarC ^ k := by rw [hk, mul_inv_cancel_left]
    rw [e, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul,
      QuotientGroup.mk_zpow]
  have ht2 : (QuotientGroup.mk tStarC : Cgen ⧸ commutator Cgen) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, pow_two]
    have : tStarC * tStarC = 1 := Subtype.ext tStar_mul_self
    rw [this, QuotientGroup.mk_one]
  have htN : tStarC ∈ commutator Cgen := by
    obtain ⟨k, hk⟩ := hgen ⟨TwoA.Census.cSqrt, hcmem⟩
    have h1 : (QuotientGroup.mk tStarC : Cgen ⧸ commutator Cgen) =
        (QuotientGroup.mk (⟨TwoA.Census.cSqrt, hcmem⟩ : Cgen) : Cgen ⧸ commutator Cgen) ^ 2 := by
      rw [← QuotientGroup.mk_pow, pow_two, hc2]
    rw [← QuotientGroup.eq_one_iff, h1, hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ht2, one_zpow]
  have hZ : Zstar ≤ commutator Cgen := (Subgroup.zpowers_le).2 htN
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, hn, hz⟩ := exists_mem_commutator_inv_mul_mem_Zstar g
  have e : g = n * (n⁻¹ * g) := by group
  rw [e]
  exact mul_mem hn (hZ hz)

end GeneratedPerfectCover

open GeneratedPerfectCover

theorem short_centralizer_generated_perfect_cover :
    commutator Cgen = ⊤ ∧ Subgroup.center Cgen = Zstar ∧ Nat.card Zstar = 2 ∧
    Nonempty (Cgen ⧸ Subgroup.center Cgen ≃* Cbar) ∧
    Finite Cbar ∧ IsSimpleGroup Cbar ∧ (∃ a b : Cbar, a * b ≠ b * a) ∧
    ∃ m : ℕ, Odd m ∧ Nat.card Cgen = 2 ^ 42 * m := by
  obtain ⟨hfin, -, hs, -⟩ := short_centralizer_generated_quotient_simple
  exact ⟨commutator_Cgen, center_Cgen, natCard_Zstar,
    ⟨QuotientGroup.quotientMulEquivOfEq center_Cgen⟩, hfin, hs, Cbar_exists_ne_comm,
    short_centralizer_quotient_sylow_two.2.2.1⟩

end CFSG.Monster.B
