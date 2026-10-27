module

public import CFSG.RankThree.PartTwo.Sec4.Item47Lift

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

section Abstract

variable {X Y : Type*} [Group X] [Group Y]

theorem mulAut_congr_apply (e : X ≃* Y) (α : MulAut X) (y : Y) :
    MulAut.congr e α y = e (α (e.symm y)) :=
  rfl

@[expose] def IsLocalWitness (α : MulAut X) (y₁ y₂ : X) (U : Subgroup X) : Prop :=
  α y₁ = y₁ ∧ α y₂ = y₂ ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ y₁ * y₂ = y₂ * y₁ ∧ y₁ ≠ 1 ∧
    y₂ ∉ Subgroup.zpowers y₁ ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧ (∀ u ∈ U, y₁ * u * y₁⁻¹ ∈ U) ∧
    (∀ u ∈ U, y₂ * u * y₂⁻¹ ∈ U) ∧ ∀ u ∈ U, α u ∈ U

@[expose] def HasLocalWitness (α : MulAut X) : Prop :=
  ∃ (y₁ y₂ : X) (U : Subgroup X), IsLocalWitness α y₁ y₂ U

theorem IsLocalWitness.congr {α : MulAut X} {y₁ y₂ : X} {U : Subgroup X}
    (h : IsLocalWitness α y₁ y₂ U) (e : X ≃* Y) :
    IsLocalWitness (MulAut.congr e α) (e y₁) (e y₂) (U.map e.toMonoidHom) := by
  obtain ⟨h₁, h₂, h₁3, h₂3, hc, h₁1, h₂₁, hU2, hU1, hUy₁, hUy₂, hUα⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hU2.map _, ?_, ?_, ?_, ?_⟩
  · rw [mulAut_congr_apply, MulEquiv.symm_apply_apply, h₁]
  · rw [mulAut_congr_apply, MulEquiv.symm_apply_apply, h₂]
  · rw [← map_pow, h₁3, map_one]
  · rw [← map_pow, h₂3, map_one]
  · rw [← map_mul, hc, map_mul]
  · intro h
    exact h₁1 (e.injective (h.trans (map_one e).symm))
  · rintro ⟨k, hk⟩
    apply h₂₁
    refine ⟨k, e.injective ?_⟩
    rw [map_zpow]
    exact hk
  · intro h
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : e u ∈ U.map e.toMonoidHom := ⟨u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (e.injective (this.trans (map_one e).symm))
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨y₁ * u * y₁⁻¹, hUy₁ u hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨y₂ * u * y₂⁻¹, hUy₂ u hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨α u, hUα u hu, ?_⟩
    rw [mulAut_congr_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem HasLocalWitness.congr {α : MulAut X} (h : HasLocalWitness α) (e : X ≃* Y) :
    HasLocalWitness (MulAut.congr e α) := by
  obtain ⟨y₁, y₂, U, h⟩ := h
  exact ⟨_, _, _, h.congr e⟩

theorem hasLocalWitness_congr_iff {α : MulAut X} (e : X ≃* Y) :
    HasLocalWitness (MulAut.congr e α) ↔ HasLocalWitness α := by
  refine ⟨fun h => ?_, fun h => h.congr e⟩
  have h' := h.congr e.symm
  have hα : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext x
    rw [mulAut_congr_apply, mulAut_congr_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
  rwa [hα] at h'

theorem mulAut_congr_eq_conj (d α : MulAut X) : MulAut.congr d α = d * α * d⁻¹ := by
  ext x
  rfl

theorem HasLocalWitness.conj {α : MulAut X} (h : HasLocalWitness α) (d : MulAut X) :
    HasLocalWitness (d * α * d⁻¹) := by
  rw [← mulAut_congr_eq_conj]
  exact h.congr d

end Abstract

section Exclusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_hasLocalWitness (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : a ^ 3 = 1) (hout : ¬ IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, ha⟩)))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hw : HasLocalWitness (thetaQuotMulAut L (compAction L ⟨a, ha⟩))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 3 h3
  have hcZ : (c : G) ∈ Subgroup.center G := c.2
  have hc3 : (c : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
  have hc1 : (c : G) ≠ 1 := by
    intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    norm_num at hc
  obtain ⟨y₁, y₂, U, h₁, h₂, h₁3, h₂3, hy, hy₁1, hy₂₁, hU2, hU1, hUy₁, hUy₂, hUα⟩ := hw
  exact false_of_local_witness hG (c := (c : G))
    (fun y _ => (Subgroup.mem_center_iff.mp hcZ y).symm) ha
    ((Subgroup.mem_center_iff.mp hcZ a).symm) hc3 hc1 ha3 hout hZ
    ((mem_barCentralizer_zpowers_iff ha y₁).mpr h₁) ((mem_barCentralizer_zpowers_iff ha y₂).mpr h₂)
    h₁3 h₂3 hy hy₁1 hy₂₁ hU2 hU1 hUy₁ hUy₂ hUα

theorem false_of_hasLocalWitness_inducedAutHom (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (hw : ∀ ha : a ∈ Subgroup.normalizer (L : Set G),
      HasLocalWitness (inducedAutHom L e ⟨a, ha⟩)) : False := by
  obtain ⟨ha, hout'⟩ := id hout
  have hw' := hw ha
  rw [inducedAutHom_apply, hasLocalWitness_congr_iff] at hw'
  exact false_of_hasLocalWitness hG h3 ha ha3 hout' hZ hw'

end Exclusion

end CFSG.RankThree.PartTwo.Sec4
