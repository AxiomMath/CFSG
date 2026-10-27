module

public import CFSG.LieType.SteinbergBRSmallAltSylow

public section

namespace CFSG.Quasithin.EmbedLoc

open Equiv Subgroup CFSG.LieType.SteinbergBR.SmallAlt
  CFSG.ComponentClassification.OuterAutomorphisms

abbrev Alt7 : Type := alternatingGroup (Fin 7)

theorem mem_conj_sylow {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) (g y : G) :
    y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]⟩

theorem normalizer_sylow_alt7 (D : Sylow 2 Alt7) {x : Alt7}
    (hx : x ∈ normalizer ((D : Subgroup Alt7) : Set Alt7)) : x ∈ (D : Subgroup Alt7) := by
  obtain ⟨P, hP⟩ := exists_selfNormalizing_seven
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Alt7 P D
  have hxn : g⁻¹ * x * g ∈ normalizer ((P : Subgroup Alt7) : Set Alt7) := by
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    have h1 := hx (g * y * g⁻¹)
    rw [mem_conj_sylow, mem_conj_sylow] at h1
    simpa [mul_assoc] using h1
  have hP' : normalizer ((P : Subgroup Alt7) : Set Alt7) = (P : Subgroup Alt7) := hP
  rw [hP'] at hxn
  exact (mem_conj_sylow P g x).2 hxn

theorem eq_one_of_odd_of_two_power {M : Type*} [Monoid M] {m : M} (hodd : Odd (orderOf m))
    {k : ℕ} (hk : m ^ (2 ^ k) = 1) : m = 1 := by
  have h1 : orderOf m ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : Nat.Coprime (orderOf m) (2 ^ k) := Nat.Coprime.pow_right k hodd.coprime_two_right
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem alt7_aut_eq_one_of_odd (σ : MulAut Alt7) (hodd : Odd (orderOf σ)) (D : Sylow 2 Alt7)
    (hσ : ∀ x : Alt7, x ∈ (D : Subgroup Alt7) ↔ σ x ∈ (D : Subgroup Alt7)) : σ = 1 := by
  have hq : (QuotientGroup.mk σ : Outer Alt7) = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_outer_seven (QuotientGroup.mk σ : Outer Alt7)
    have hdvd : orderOf (QuotientGroup.mk σ : Outer Alt7) ∣ orderOf σ :=
      orderOf_map_dvd (QuotientGroup.mk' (inner Alt7)) σ
    exact eq_one_of_odd_of_two_power (hodd.of_dvd_nat hdvd) hk
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff σ).mp hq
  have hcN : c ∈ normalizer ((D : Subgroup Alt7) : Set Alt7) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := hσ x
    rw [← hc] at this
    simpa [MulAut.conj_apply] using this
  have hcD : c ∈ (D : Subgroup Alt7) := normalizer_sylow_alt7 D hcN
  obtain ⟨k, hk⟩ := D.isPGroup' ⟨c, hcD⟩
  have hck : c ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine eq_one_of_odd_of_two_power hodd (k := k) ?_
  rw [← hc, ← map_pow, hck, map_one]

end CFSG.Quasithin.EmbedLoc
