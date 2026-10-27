module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.ClassicalInvolution.Q3.TL4G23Inner
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.RankThree.Chevalley.G2CyclotomicTori
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.Blueprint.Chevalley CFSG.ComponentClassification
open CFSG.ClassicalInvolution.Q3.Q3NM (mem_innSubgroup_iff)


private theorem conj_injective_adjointG2 (K : Type) [Field K] [Finite K] :
    Function.Injective
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ Subgroup.center (adjointGroup Tag.G2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun a : MulAut (adjointGroup Tag.G2 K) => a y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hx'

private theorem card_adjointG2_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    Nat.card (adjointGroup Tag.G2 K) = 4245696 := by
  rw [(CFSG.LieType.Chevalley.exact_G2_finite_order K hK).1]
  norm_num

private theorem false_of_commute_three_seven {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {s t : adjointGroup Tag.G2 K} (hs : orderOf s = 3) (ht : orderOf t = 7)
    (hst : Commute s t) : False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have hd : ((7 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1 := by
    norm_num [hK]
  obtain ⟨T, -, -, -, -, hx⟩ :=
    CFSG.RankThree.Chevalley.odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hodd
      (-1) (Or.inl rfl) 7 hd (by norm_num : Nat.Prime 7) (by norm_num : 3 < 7) (dvd_refl 7)
  have hcent := (hx t ht).2.2.2.1
  have hmem : s ∈ Subgroup.centralizer ({t} : Set (adjointGroup Tag.G2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst.eq
  have hdvd := Subgroup.orderOf_dvd_natCard
    (Subgroup.centralizer ({t} : Set (adjointGroup Tag.G2 K))) hmem
  rw [hs, hcent] at hdvd
  omega

private theorem false_of_commute_g2_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {σ τ : MulAut (adjointGroup Tag.G2 K)} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hτp : ∀ p : ℕ, p.Prime → p ∣ orderOf τ → p = 5 ∨ p = 7) (hτ1 : τ ≠ 1)
    (hστ : σ * τ = τ * σ) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hσodd : Odd (orderOf σ) := by rw [hσo]; decide
  have hτodd : Odd (orderOf τ) := by
    rw [Nat.odd_iff]
    by_contra h2
    rcases hτp 2 Nat.prime_two (by omega) with h | h <;> omega
  obtain ⟨s, hs⟩ := mem_innSubgroup_iff.mp
    (CFSG.ClassicalInvolution.Q3.TL4.mem_innSubgroup_of_odd_orderOf_g2_three hK σ hσodd)
  obtain ⟨t, ht⟩ := mem_innSubgroup_iff.mp
    (CFSG.ClassicalInvolution.Q3.TL4.mem_innSubgroup_of_odd_orderOf_g2_three hK τ hτodd)
  have hinj := conj_injective_adjointG2 K
  have hso : orderOf s = 3 := by rw [← orderOf_injective _ hinj s, hs, hσo]
  have hto : orderOf t = orderOf τ := by rw [← orderOf_injective _ hinj t, ht]
  have hst : s * t = t * s := hinj (by rw [map_mul, map_mul, hs, ht]; exact hστ)
  have ht1 : t ≠ 1 := fun h => hτ1 (by rw [← ht, h, map_one])
  have hcard := card_adjointG2_three hK
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (fun h => ht1 (orderOf_eq_one_iff.mp h))
  have h7 : 7 ∣ orderOf t := by
    rcases hτp p hp (by rw [← hto]; exact hpt) with rfl | rfl
    · have := hpt.trans (orderOf_dvd_natCard t)
      rw [hcard] at this
      omega
    · exact hpt
  have hpos : 0 < orderOf t :=
    Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard t) (by rw [hcard]; norm_num)
  exact false_of_commute_three_seven hK hso (orderOf_pow_orderOf_div hpos.ne' h7)
    (Commute.pow_right (show Commute s t from hst) _)

theorem res3NoDatumG23_holds : Res3NoDatumG23 := by
  rintro J _ _ _ hq hX c g V U hd
  haveI : Group.IsPerfect J := hq.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_adjointGroup_G2 hX
  rw [pow_one] at hK
  let Φ : MulAut J →* MulAut (adjointGroup Tag.G2 K) :=
    (MulAut.congr e).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom J)
  have hΦ : Function.Injective Φ :=
    (MulAut.congr e).injective.comp (PerfectAutomorphisms.centerQuotientHom_injective J)
  refine false_of_commute_g2_three hK (σ := Φ c) (τ := Φ g) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hd.c_pow, map_one]
  · exact fun h => hd.c_ne_one (hΦ (h.trans (map_one Φ).symm))
  · intro p hp hpd
    rw [orderOf_injective Φ hΦ g] at hpd
    exact hd.g_primes p hp hpd
  · exact fun h => hd.g_ne_one (hΦ (h.trans (map_one Φ).symm))
  · rw [← map_mul, ← map_mul, hd.comm.eq]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
