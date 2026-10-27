module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.ClassicalInvolution.SmallCases.NobqOut
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
import CFSG.Quasithin.Background.SmithB45MatM22Cls
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem isPGroup_two_outer_m22 :
    IsPGroup 2 (Outer Blueprint.NativeSporadic.M22) := by
  haveI : Finite (MulAut Blueprint.NativeSporadic.M22) := MulEquiv.finite_left
  have hle : Nat.card (Outer Blueprint.NativeSporadic.M22) ≤ 2 :=
    CFSG.ClassicalInvolution.Nobq.card_outer_le_two_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
  have hpos : 0 < Nat.card (Outer Blueprint.NativeSporadic.M22) := Nat.card_pos
  refine IsPGroup.of_card_dvd_pow (n := 1) ?_
  generalize Nat.card (Outer Blueprint.NativeSporadic.M22) = n at hle hpos
  interval_cases n <;> decide

private theorem false_of_commute_of_five_seven
    {σ τ : MulAut Blueprint.NativeSporadic.M22} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hτ : ∀ p : ℕ, p.Prime → p ∣ orderOf τ → p = 5 ∨ p = 7) (hστ : σ * τ = τ * σ) : False := by
  haveI : Finite (MulAut Blueprint.NativeSporadic.M22) := MulEquiv.finite_left
  have hout := isPGroup_two_outer_m22
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have hn1 : orderOf τ ≠ 1 := fun h => hτ1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  have hp57 := hτ p hp hpn
  have hτpo : orderOf (τ ^ (orderOf τ / p)) = p :=
    orderOf_pow_orderOf_div (orderOf_pos τ).ne' hpn
  have hτp1 : (τ ^ (orderOf τ / p)) ^ p = 1 := by
    have h := pow_orderOf_eq_one (τ ^ (orderOf τ / p))
    rwa [hτpo] at h
  have hcomm : σ * τ ^ (orderOf τ / p) = τ ^ (orderOf τ / p) * σ :=
    (Commute.pow_right (show Commute σ τ from hστ) (orderOf τ / p)).eq
  have hodd : Odd p := by rcases hp57 with rfl | rfl <;> decide
  obtain ⟨s, hs⟩ := CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hout
    (by decide : Odd (3 : ℕ)) hσ3
  obtain ⟨t, ht⟩ := CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hout hodd hτp1
  have hso : orderOf s = 3 := by
    rw [← orderOf_injective _ hinj s, hs]
    exact orderOf_eq_prime hσ3 hσ1
  have hto : orderOf t = p := by
    rw [← orderOf_injective _ hinj t, ht, hτpo]
  have hst : s * t = t * s := by
    apply hinj
    rw [map_mul, map_mul, hs, ht]
    exact hcomm
  have hcop : Nat.Coprime (orderOf s) (orderOf t) := by
    rw [hso, hto]
    rcases hp57 with rfl | rfl <;> norm_num
  have hord : orderOf (s * t) = 3 * p := by
    rw [(show Commute s t from hst).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hso, hto]
  have hmem := CFSG.Quasithin.B45Mat.M22.orderOf_mem_of_isPRegular (s * t) (by
    change Nat.Coprime (orderOf (s * t)) 2
    rw [hord]
    rcases hp57 with rfl | rfl <;> norm_num)
  rw [hord] at hmem
  rcases hp57 with rfl | rfl <;> simp at hmem

theorem res3NoDatumM22_holds :
    Res3NoDatumM22 := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  haveI : Group.IsPerfect J := hq.1
  let Φ : MulAut J →* MulAut Blueprint.NativeSporadic.M22 :=
    (MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J)
  have hΦ : Function.Injective Φ :=
    (MulAut.congr e).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective J)
  refine false_of_commute_of_five_seven (σ := Φ c) (τ := Φ g) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hd.c_pow, map_one]
  · exact fun h => hd.c_ne_one (hΦ (h.trans (map_one Φ).symm))
  · exact fun h => hd.g_ne_one (hΦ (h.trans (map_one Φ).symm))
  · intro p hp hpd
    rw [orderOf_injective Φ hΦ g] at hpd
    exact hd.g_primes p hp hpd
  · rw [← map_mul, ← map_mul, hd.comm.eq]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
