module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.NoFifteen
import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Centralizer
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCharThree
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSporadicStandard.HSStd.InvCent (orderOf_ne_fifteen_projSU_four_three)

private theorem injective_conj_of_simple {S : Type*} [Group S] [IsSimpleGroup S] {a b : S}
    (hab : a * b ≠ b * a) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · have hb : b ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top b
      exact absurd (Subgroup.mem_center_iff.mp hb a) hab
  intro x y hxy
  have h1 : x⁻¹ * y ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h2 := congrArg (fun φ : MulAut S => φ z) hxy
    simp only [MulAut.conj_apply] at h2
    calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
      _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h2]
      _ = x⁻¹ * y * z := by group
  rw [hZ, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

private theorem exists_conj_of_not_two_dvd {α : MulAut (projSU 4 3 1)} (hα : ¬ 2 ∣ orderOf α) :
    ∃ a : projSU 4 3 1, MulAut.conj a = α := by
  have hout : Nat.card (Outer (projSU 4 3 1)) ∣ 2 ^ 3 :=
    (Sec4.card_outer_projSU_dvd 4 3 1 le_rfl (by norm_num) (by norm_num)).trans (by norm_num)
  have hcop : (orderOf α).Coprime (Nat.card (Outer (projSU 4 3 1))) :=
    Nat.Coprime.coprime_dvd_right hout
      (Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hα).symm)
  exact CFSG.OddStandard.AltStdSec.SwapPartner.mem_inner_of_coprime_orderOf_outer hcop

private theorem false_of_commute {S : Type*} [Group S]
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hinn : ∀ α : MulAut S, ¬ 2 ∣ orderOf α → ∃ a : S, MulAut.conj a = α)
    (h15 : ∀ x : S, orderOf x ≠ 15) (h21 : ∀ x : S, orderOf x ≠ 21)
    {σ τ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hτ2 : ¬ 2 ∣ orderOf τ)
    (hτp : ∀ p : ℕ, p.Prime → p ∣ orderOf τ → p = 5 ∨ p = 7) (hστ : σ * τ = τ * σ) : False := by
  have hσ2 : ¬ 2 ∣ orderOf σ := fun h => by
    have := h.trans (orderOf_dvd_of_pow_eq_one hσ3)
    omega
  obtain ⟨s, rfl⟩ := hinn σ hσ2
  obtain ⟨t, rfl⟩ := hinn τ hτ2
  rw [orderOf_injective _ hinj t] at hτ2 hτp
  have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hσ3, map_one])
  have hs1 : s ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have ht1 : t ≠ 1 := fun h => hτ1 (by rw [h, map_one])
  have hst : Commute s t := hinj (by rw [map_mul, map_mul]; exact hστ)
  have hos : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hn0 : orderOf t ≠ 0 := fun h => hτ2 (by rw [h]; exact dvd_zero 2)
  have hn1 : orderOf t ≠ 1 := fun h => ht1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpp, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ orderOf t :=
    ⟨(orderOf t).minFac, Nat.minFac_prime hn1, Nat.minFac_dvd _⟩
  obtain ⟨t', ht'o, hst'⟩ : ∃ t' : S, orderOf t' = p ∧ Commute s t' :=
    ⟨t ^ (orderOf t / p), orderOf_pow_orderOf_div hn0 hpd, hst.pow_right _⟩
  have hp57 := hτp p hpp hpd
  have hcop : (orderOf s).Coprime (orderOf t') := by
    rw [hos, ht'o]
    rcases hp57 with h | h <;> rw [h] <;> decide
  have hord : orderOf (s * t') = 3 * p := by
    rw [hst'.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hos, ht'o]
  rcases hp57 with h | h
  · exact h15 (s * t') (by omega)
  · exact h21 (s * t') (by omega)

theorem res3NoDatumU43_holds : Res3NoDatumU43 := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  haveI : Group.IsPerfect J := hq.1
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hq.2.1
  haveI : IsSimpleGroup (projSU 4 3 1) := e.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hq.2.2
  have hinj : Function.Injective (MulAut.conj : projSU 4 3 1 →* MulAut (projSU 4 3 1)) :=
    injective_conj_of_simple (a := e a) (b := e b) fun h =>
      hab (e.injective (by rw [map_mul, map_mul]; exact h))
  let Φ : MulAut J →* MulAut (projSU 4 3 1) :=
    (MulAut.congr e).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom J)
  have hΦ : Function.Injective Φ :=
    (MulAut.congr e).injective.comp (PerfectAutomorphisms.centerQuotientHom_injective J)
  have hog : orderOf (Φ g) = orderOf g := orderOf_injective Φ hΦ g
  refine false_of_commute hinj (fun _ hα => exists_conj_of_not_two_dvd hα)
    orderOf_ne_fifteen_projSU_four_three
    (fun x hx => Sec21.Item223CensusResProof.noOrderMersenne223_U43 x 3 (by norm_num)
      (by decide) (by norm_num [hx]))
    (σ := Φ c) (τ := Φ g) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hd.c_pow, map_one]
  · exact fun h => hd.c_ne_one (hΦ (h.trans (map_one Φ).symm))
  · exact fun h => hd.g_ne_one (hΦ (h.trans (map_one Φ).symm))
  · rw [hog]
    exact hd.not_two_dvd
  · intro p hp hpd
    rw [hog] at hpd
    exact hd.g_primes p hp hpd
  · rw [← map_mul, ← map_mul, hd.comm.eq]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
