module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.KE6

open scoped Pointwise commutatorElement

theorem commutator_sup_le_of_comm {Γ : Type*} [Group Γ] {H Q : Subgroup Γ}
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHN : H ≤ Subgroup.normalizer (Q : Set Γ)) :
    ⁅H ⊔ Q, H ⊔ Q⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right H Q hHN
  have hHQ : ∀ x ∈ H ⊔ Q, ∃ h ∈ H, ∃ q ∈ Q, x = h * q := fun x hx => by
    have : x ∈ (H : Set Γ) * (Q : Set Γ) := by
      rw [← hmul]
      exact hx
    obtain ⟨h, hh, q, hq, hxq⟩ := this
    exact ⟨h, hh, q, hq, hxq.symm⟩
  obtain ⟨h₁, hh₁, q₁, hq₁, rfl⟩ := hHQ a ha
  obtain ⟨h₂, hh₂, q₂, hq₂, rfl⟩ := hHQ b hb
  have hc : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.1 (hHN hh) q).1 hq
  have hF1 : h₁ * (q₁ * (h₂ * (q₂ * q₁⁻¹ * q₂⁻¹) * h₂⁻¹)) * h₁⁻¹ ∈ Q :=
    hc h₁ hh₁ _ (mul_mem hq₁ (hc h₂ hh₂ _ (mul_mem (mul_mem hq₂ (inv_mem hq₁)) (inv_mem hq₂))))
  have hF2' : h₁ * h₂ * q₂ * h₁⁻¹ * q₂⁻¹ * h₂⁻¹ ∈ Q := by
    rw [hHc h₁ hh₁ h₂ hh₂]
    have : h₂ * h₁ * q₂ * h₁⁻¹ * q₂⁻¹ * h₂⁻¹ = h₂ * ((h₁ * q₂ * h₁⁻¹) * q₂⁻¹) * h₂⁻¹ := by group
    rw [this]
    exact hc h₂ hh₂ _ (mul_mem (hc h₁ hh₁ _ hq₂) (inv_mem hq₂))
  have e : ⁅h₁ * q₁, h₂ * q₂⁆ = (h₁ * (q₁ * (h₂ * (q₂ * q₁⁻¹ * q₂⁻¹) * h₂⁻¹)) * h₁⁻¹) *
      (h₁ * h₂ * q₂ * h₁⁻¹ * q₂⁻¹ * h₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hF1 hF2'

theorem perfectResidual_map_eq {D Γ : Type*} [Group D] [Group Γ] (ψ : D →* Γ)
    (hψ : Function.Injective ψ) (P : Subgroup Γ) (hPr : P ≤ ψ.range) (hPp : ⁅P, P⁆ = P)
    (hD2 : ⁅⁅ψ.range, ψ.range⁆, ⁅ψ.range, ψ.range⁆⁆ ≤ P) :
    (CFSG.perfectResidual D).map ψ = P := by
  apply le_antisymm
  · refine le_trans (Subgroup.map_mono (?_ : CFSG.perfectResidual D ≤ derivedSeries D 2)) ?_
    · exact iInf_le _ 2
    · have h2 : (derivedSeries D 2).map ψ = ⁅⁅ψ.range, ψ.range⁆, ⁅ψ.range, ψ.range⁆⁆ := by
        rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
          Subgroup.map_commutator, ← MonoidHom.range_eq_map]
      rw [h2]
      exact hD2
  · intro p hp
    obtain ⟨d, rfl⟩ := hPr hp
    refine ⟨d, ?_, rfl⟩
    set PD : Subgroup D := P.comap ψ with hPD
    have hmapPD : PD.map ψ = P := by
      rw [hPD, Subgroup.map_comap_eq]
      exact inf_of_le_right hPr
    have hPDperf : ⁅PD, PD⁆ = PD := by
      apply Subgroup.map_injective hψ
      rw [Subgroup.map_commutator, hmapPD, hPp]
    have hle : ∀ n, PD ≤ derivedSeries D n := by
      intro n
      induction n with
      | zero => exact le_top
      | succ n ih =>
        rw [derivedSeries_succ]
        calc PD = ⁅PD, PD⁆ := hPDperf.symm
          _ ≤ ⁅derivedSeries D n, derivedSeries D n⁆ := Subgroup.commutator_mono ih ih
    have hdPD : d ∈ PD := hp
    have hdr : d ∈ CFSG.perfectResidual D := by
      rw [CFSG.perfectResidual, Subgroup.mem_iInf]
      exact fun n => hle n hdPD
    exact hdr

theorem odd_card_of_conj {C Γ : Type*} [Group C] [Finite C] [Group Γ] (f : C →* Γ)
    (hf : Function.Injective f) (T : Subgroup Γ) (hT : Odd (Nat.card T))
    (S : Subgroup (MulAut C))
    (hS : ∀ η ∈ S, ∃ t ∈ T, ∀ d : C, f (η d) = t * f d * t⁻¹) : Odd (Nat.card S) := by
  classical
  by_contra hnodd
  have h2 : 2 ∣ Nat.card S := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨η, hη⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨t, htT, ht⟩ := hS η η.2
  have hpow : ∀ k : ℕ, ∀ d : C, f (((η : MulAut C) ^ k) d) = t ^ k * f d * (t ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
      intro d
      rw [pow_succ, MulAut.mul_apply, ih, ht d]
      group
  have hm : Odd (orderOf t) := by
    have h1 : orderOf (⟨t, htT⟩ : T) ∣ Nat.card T := orderOf_dvd_natCard _
    have h3 : orderOf (⟨t, htT⟩ : T) = orderOf t := by
      rw [← Subgroup.orderOf_coe]
    rw [h3] at h1
    exact Odd.of_dvd_nat hT h1
  have hη1 : (η : MulAut C) ^ (orderOf t) = 1 := by
    ext d
    apply hf
    rw [hpow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hord : orderOf (η : MulAut C) ∣ orderOf t := orderOf_dvd_of_pow_eq_one hη1
  have h4 : orderOf (η : MulAut C) = 2 := by
    rw [← Subgroup.orderOf_coe] at hη
    exact hη
  rw [h4] at hord
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hord)

end CFSG.RankThree.PartOne.KE6
