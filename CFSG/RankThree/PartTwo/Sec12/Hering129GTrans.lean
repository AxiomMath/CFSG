module

import CFSG.RankThree.PartTwo.KFacts.KS14GL33
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem sl23_unique_involution (g h : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hg : g ^ 2 = 1) (hg1 : g ≠ 1) (hh : h ^ 2 = 1) (hh1 : h ≠ 1) : g = h := by
  revert g h
  decide

theorem sl23_exists_involution :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), g ^ 2 = 1 ∧ g ≠ 1 := by
  decide

theorem transitive_of_sl23 {E : Type} [Group E] [Finite E] (Γ : Subgroup (MulAut E))
    (hΓ : Nonempty (Γ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (Ω : Set E) (hΩ : Ω.ncard = 8) (hinv : ∀ γ ∈ Γ, ∀ w ∈ Ω, γ w ∈ Ω)
    (hfaith : ∀ γ ∈ Γ, (∀ w ∈ Ω, γ w = w) → γ = 1) :
    ∀ u ∈ Ω, ∀ v ∈ Ω, ∃ γ ∈ Γ, γ u = v := by
  obtain ⟨e⟩ := hΓ
  have hcard : Nat.card Γ = 24 := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_SL_two_three
  haveI : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨g₀, hg₀2, hg₀1⟩ := sl23_exists_involution
  set z : Γ := e.symm g₀ with hz
  have hez : e z = g₀ := by rw [hz]; exact e.apply_symm_apply g₀
  have hz1 : z ≠ 1 := by
    intro h; apply hg₀1; rw [← hez, h, map_one]
  have huniq : ∀ g : Γ, g ^ 2 = 1 → g ≠ 1 → g = z := by
    intro g hg2 hg1
    apply e.injective
    refine sl23_unique_involution _ _ ?_ ?_ (by rw [hez]; exact hg₀2) (by rw [hez]; exact hg₀1)
    · rw [← map_pow, hg2, map_one]
    · intro h; apply hg1; exact e.injective (by rw [h, map_one])
  obtain ⟨w, hwΩ, hzw⟩ : ∃ w ∈ Ω, (z : MulAut E) w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hz1 (Subtype.ext (hfaith z z.2 hcon))
  set S := MulAction.stabilizer Γ w with hS
  have hSodd : ¬ 2 ∣ Nat.card S := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2
    have hs2 : (s : Γ) ^ 2 = 1 := by
      have : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
      exact congrArg Subtype.val this
    have hs1 : (s : Γ) ≠ 1 := by
      intro h1
      have : s = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hs
      exact absurd hs (by norm_num)
    have hsz := huniq _ hs2 hs1
    have hsw : (s : Γ) • w = w := s.2
    rw [hsz] at hsw
    exact hzw hsw
  have hSdvd : Nat.card S ∣ 24 := hcard ▸ Subgroup.card_subgroup_dvd_card S
  have hS13 : Nat.card S = 1 ∨ Nat.card S = 3 := by
    have hle : Nat.card S ≤ 24 := Nat.le_of_dvd (by norm_num) hSdvd
    interval_cases h : Nat.card S <;>
      first | omega | (exfalso; revert hSdvd hSodd; decide) | simp_all
  have hidx : S.index = Nat.card (MulAction.orbit Γ w) := by
    rw [hS, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have horb := Subgroup.index_mul_card S
  rw [hidx, hcard] at horb
  have hsub : (MulAction.orbit Γ w : Set E) ⊆ Ω := by
    rintro _ ⟨γ, rfl⟩
    exact hinv γ γ.2 w hwΩ
  have hle : (MulAction.orbit Γ w : Set E).ncard ≤ 8 := by
    rw [← hΩ]
    exact Set.ncard_le_ncard hsub (Set.toFinite Ω)
  have hoc : (MulAction.orbit Γ w : Set E).ncard = Nat.card (MulAction.orbit Γ w) :=
    (Nat.card_coe_set_eq _).symm
  have h8 : (MulAction.orbit Γ w : Set E).ncard = 8 := by
    rcases hS13 with h | h <;> rw [h] at horb <;> omega
  have heq : (MulAction.orbit Γ w : Set E) = Ω :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h8, hΩ]) (Set.toFinite Ω)
  intro u hu v hv
  rw [← heq] at hu hv
  obtain ⟨α, rfl⟩ := hu
  obtain ⟨β, rfl⟩ := hv
  refine ⟨((β * α⁻¹ : Γ) : MulAut E), (β * α⁻¹).2, ?_⟩
  change ((β * α⁻¹ : Γ) • (α • w) : E) = β • w
  rw [smul_smul]
  simp

end CFSG.RankThree.PartTwo.Sec12.Hering129G
