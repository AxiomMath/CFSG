module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.E9AutFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem not_three_dvd_card_mulAut_of_card_three
    {Z : Type} [Group Z] (hZ : Nat.card Z = 3) :
    ¬ 3 ∣ Nat.card (MulAut Z) := by
  haveI : Fact (Nat.card Z).Prime := ⟨by rw [hZ]; norm_num⟩
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  haveI : IsCyclic Z := isCyclic_of_prime_card rfl
  rw [IsCyclic.card_mulAut, hZ, Nat.totient_prime Nat.prime_three]
  norm_num

theorem le_centralizer_center_of_isPGroup
    {G : Type} [Group G] {P Z : Subgroup G}
    (hP3 : IsPGroup 3 P)
    (hPN : P ≤ Subgroup.normalizer (Z : Set G))
    (hZcard : Nat.card ↥Z = 3) :
    P ≤ Subgroup.centralizer (Z : Set G) := by
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  intro p hp
  let ρ : P →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  have hρ : ∀ (q : P) (z : ↥Z),
      ((ρ q z : ↥Z) : G) = (q : G) * (z : G) * (q : G)⁻¹ := by
    intro q z
    simp [ρ]
  have hρ1 : ρ ⟨p, hp⟩ = 1 := by
    have hzp : IsPGroup 3 (Subgroup.zpowers (⟨p, hp⟩ : P)) :=
      hP3.to_subgroup (Subgroup.zpowers ⟨p, hp⟩)
    have hmap : IsPGroup 3 (Subgroup.zpowers (ρ ⟨p, hp⟩)) := by
      have h := IsPGroup.map hzp ρ
      rwa [MonoidHom.map_zpowers] at h
    exact MulAut.eq_one_of_isPGroup_of_not_dvd_card (p := 3) (by norm_num)
      (not_three_dvd_card_mulAut_of_card_three hZcard) hmap
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h : (p : G) * z * (p : G)⁻¹ = z := by
    have h' := congrArg (fun σ : MulAut ↥Z => ((σ ⟨z, hz⟩ : ↥Z) : G)) hρ1
    rw [hρ, MulAut.one_apply] at h'
    simpa using h'
  calc z * p = (p * z * p⁻¹) * p := by rw [h]
    _ = p * z := by group

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
