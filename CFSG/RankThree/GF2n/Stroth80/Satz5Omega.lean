module

public import CFSG.RankThree.GF2n.Stroth80.Satz5Core
public import CFSG.RankThree.GF2n.Stroth80.QuadWitt
public import CFSG.ClassicalGroups.Orthogonal.Perfect

public section

namespace CFSG.RankThree.GF2n.Stroth80.Satz5

open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim79 CFSG.ClassicalGroups.Orthogonal
open TauCeti.QuadraticMap
open scoped commutatorElement

variable {G : Type} [Group G] {P Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

@[expose] noncomputable def omegaOf (M₀ : Tim79.QuadModel P Z K γ) :
    Subgroup (M₀.E ≃ₗ[K] M₀.E) :=
  ⁅orthogonalGroup M₀.toQuadraticForm, orthogonalGroup M₀.toQuadraticForm⁆

section Torus

variable {M₀ : Tim79.QuadModel P Z K γ} {v w : M₀.E}

@[expose] noncomputable def torusLin (M₀ : Tim79.QuadModel P Z K γ) (v w : M₀.E) (α β : K) :
    M₀.E →ₗ[K] M₀.E :=
  LinearMap.id + α • (M₀.B.flip w).smulRight v + β • (M₀.B.flip v).smulRight w

theorem torusLin_apply (α β : K) (x : M₀.E) :
    torusLin M₀ v w α β x = x + (α * M₀.B x w) • v + (β * M₀.B x v) • w := by
  simp [torusLin, smul_smul]

structure IsHypPair (M₀ : Tim79.QuadModel P Z K γ) (v w : M₀.E) : Prop where
  qv : M₀.Qf v = 0
  qw : M₀.Qf w = 0
  bvw : M₀.B v w = 1
  bwv : M₀.B w v = 1

theorem torusLin_Bw (hP : IsHypPair M₀ v w) (α β : K) (x : M₀.E) :
    M₀.B (torusLin M₀ v w α β x) w = (1 + α) * M₀.B x w := by
  simp only [torusLin_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hP.bvw, M₀.alt]
  ring

theorem torusLin_Bv (hP : IsHypPair M₀ v w) (α β : K) (x : M₀.E) :
    M₀.B (torusLin M₀ v w α β x) v = (1 + β) * M₀.B x v := by
  simp only [torusLin_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hP.bwv, M₀.alt]
  ring

theorem torusLin_comp (hP : IsHypPair M₀ v w) {α β α' β' : K} (hα : α + α' * (1 + α) = 0)
    (hβ : β + β' * (1 + β) = 0) (x : M₀.E) :
    torusLin M₀ v w α' β' (torusLin M₀ v w α β x) = x := by
  rw [torusLin_apply α' β' (torusLin M₀ v w α β x), torusLin_Bw hP, torusLin_Bv hP,
    torusLin_apply]
  calc x + (α * M₀.B x w) • v + (β * M₀.B x v) • w + (α' * ((1 + α) * M₀.B x w)) • v +
        (β' * ((1 + β) * M₀.B x v)) • w
      = x + ((α * M₀.B x w + α' * ((1 + α) * M₀.B x w)) • v) +
        ((β * M₀.B x v + β' * ((1 + β) * M₀.B x v)) • w) := by module
    _ = x := by
      rw [show α * M₀.B x w + α' * ((1 + α) * M₀.B x w) = 0 by
          linear_combination (M₀.B x w) * hα,
        show β * M₀.B x v + β' * ((1 + β) * M₀.B x v) = 0 by
          linear_combination (M₀.B x v) * hβ]
      simp

theorem torusLin_qf (hP : IsHypPair M₀ v w) {α β : K} (h : α * β + α + β = 0) (x : M₀.E) :
    M₀.Qf (torusLin M₀ v w α β x) = M₀.Qf x := by
  rw [torusLin_apply, add_assoc, M₀.Qf_add, M₀.Qf_add, M₀.Qf_smul, M₀.Qf_smul, hP.qv, hP.qw]
  simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, hP.bvw]
  linear_combination (M₀.B x w * M₀.B x v) * h

theorem exists_torus (hP : IsHypPair M₀ v w) {ν : K} (hν : ν ≠ 0) :
    ∃ τ : M₀.E ≃ₗ[K] M₀.E, τ ∈ orthogonalGroup M₀.toQuadraticForm ∧
      ∀ x, τ x = torusLin M₀ v w (ν - 1) (ν⁻¹ - 1) x := by
  refine ⟨LinearEquiv.ofLinearMap (torusLin M₀ v w (ν - 1) (ν⁻¹ - 1))
    (torusLin M₀ v w (ν⁻¹ - 1) (ν - 1))
    (LinearMap.ext fun x => torusLin_comp hP (by field_simp; ring) (by field_simp; ring) x)
    (LinearMap.ext fun x => torusLin_comp hP (by field_simp; ring) (by field_simp; ring) x),
    ?_, fun x => rfl⟩
  refine mem_orthogonalGroup_iff.mpr fun x => ?_
  exact torusLin_qf hP (by field_simp; ring) x

end Torus

section Eichler

variable {M₀ : Tim79.QuadModel P Z K γ} {X : Subgroup G} {v₁ v₂ w₁ w₂ : M₀.E}

theorem polar_eq (e f : M₀.E) : QuadraticMap.polar M₀.toQuadraticForm e f = M₀.B e f :=
  Tim79.QuadModel.polar_toQuadraticForm M₀ e f

theorem eichler_smul_mem_omega {τ : M₀.E ≃ₗ[K] M₀.E}
    (hτ : τ ∈ orthogonalGroup M₀.toQuadraticForm) {u₀ x : M₀.E} (hu₀ : M₀.Qf u₀ = 0)
    (hτu₀ : τ u₀ = u₀) {c₀ : K} (hc₀ : c₀ ≠ 1) (hx : τ x = c₀ • x) (hperp : M₀.B u₀ x = 0)
    (l : K) : eichler M₀.toQuadraticForm u₀ (l • x) ∈ omegaOf M₀ := by
  have hc : c₀ - 1 ≠ 0 := sub_ne_zero.mpr hc₀
  have hpol : QuadraticMap.polar M₀.toQuadraticForm u₀ ((l / (c₀ - 1)) • x) = 0 := by
    rw [polar_smul_right_eq, polar_eq, hperp, mul_zero]
  have h1 := commutatorElement_eichler hτ hτu₀ hpol
  have h2 : τ ((l / (c₀ - 1)) • x) - (l / (c₀ - 1)) • x = l • x := by
    rw [map_smul, hx, smul_smul, ← sub_smul]
    congr 1
    field_simp
  rw [h2] at h1
  rw [← h1]
  exact Subgroup.commutator_mem_commutator hτ (eichler_mem_orthogonalGroup _ _ _)

theorem Setting.rootA_eq_eichler (S : Setting M₀ X v₁ v₂ w₁ w₂) (hqv₂ : M₀.Qf v₂ = 0)
    (hqw₁ : M₀.Qf w₁ = 0) (l : K) (e : M₀.E) :
    rootA M₀ v₂ w₁ l e = eichler M₀.toQuadraticForm v₂ (l • w₁) e := by
  have hw : QuadraticMap.polar M₀.toQuadraticForm v₂ (l • w₁) = 0 := by
    rw [polar_eq, map_smul, smul_eq_mul, S.b21, mul_zero]
  rw [eichler_apply hqv₂ hw e]
  simp only [polar_eq, Tim79.QuadModel.toQuadraticForm_apply, M₀.Qf_smul, hqw₁, mul_zero,
    zero_mul, add_zero, map_smul, smul_eq_mul, rootA, sub_eq_add_neg, smul_smul]
  have h := S.add_self ((l * M₀.B e w₁) • v₂)
  rw [neg_eq_of_add_eq_zero_left h]
  module

theorem Setting.rootB_eq_eichler (S : Setting M₀ X v₁ v₂ w₁ w₂) (hqv₂ : M₀.Qf v₂ = 0)
    (hqv₁ : M₀.Qf v₁ = 0) (m : K) (e : M₀.E) :
    rootB M₀ v₁ v₂ m e = eichler M₀.toQuadraticForm v₂ (m • v₁) e := by
  have hw : QuadraticMap.polar M₀.toQuadraticForm v₂ (m • v₁) = 0 := by
    rw [polar_eq, map_smul, smul_eq_mul, S.bv2v1, mul_zero]
  rw [eichler_apply hqv₂ hw e]
  simp only [polar_eq, Tim79.QuadModel.toQuadraticForm_apply, M₀.Qf_smul, hqv₁, mul_zero,
    zero_mul, add_zero, map_smul, smul_eq_mul, rootB, sub_eq_add_neg, smul_smul]
  have h := S.add_self ((m * M₀.B e v₁) • v₂)
  rw [neg_eq_of_add_eq_zero_left h]
  module

end Eichler

section Omega

variable {M₀ : Tim79.QuadModel P Z K γ} {X : Subgroup G} {v₁ v₂ w₁ w₂ : M₀.E}

theorem Setting.false_of_omega (S : Setting M₀ X v₁ v₂ w₁ w₂) (hqv₁ : M₀.Qf v₁ = 0)
    (hqv₂ : M₀.Qf v₂ = 0) (hqw₁ : M₀.Qf w₁ = 0) {ν : K} (hν0 : ν ≠ 0) (hν1 : ν ≠ 1)
    (hΩ : ∀ T ∈ omegaOf M₀, ∃ g ∈ X, Induces M₀ g T) : False := by
  have hP : IsHypPair M₀ v₁ w₁ := ⟨hqv₁, hqw₁, S.b11, S.bw1v1⟩
  obtain ⟨τ, hτO, hτ⟩ := exists_torus hP hν0
  have hτv₂ : τ v₂ = v₂ := by
    rw [hτ, torusLin_apply]
    simp [S.b21, S.bv2v1]
  have hτw₁ : τ w₁ = ν⁻¹ • w₁ := by
    rw [hτ, torusLin_apply]
    simp only [M₀.alt, S.bw1v1, mul_zero, zero_smul, add_zero, mul_one]
    rw [sub_smul, one_smul]
    abel
  have hτv₁ : τ v₁ = ν • v₁ := by
    rw [hτ, torusLin_apply]
    simp only [M₀.alt, S.b11, mul_zero, zero_smul, add_zero, mul_one]
    rw [sub_smul, one_smul]
    abel
  have hν1' : ν⁻¹ ≠ 1 := fun h => hν1 (by simpa using congrArg (·⁻¹) h)
  refine S.false_of_rootLifts hν0 hν1 (fun l _ => ?_) (fun m _ => ?_)
  · obtain ⟨a, ha, hind⟩ := hΩ _ (eichler_smul_mem_omega hτO hqv₂ hτv₂ hν1' hτw₁ S.b21 l)
    refine ⟨a, ha, fun x hx => ?_⟩
    rw [hind x hx, S.rootA_eq_eichler hqv₂ hqw₁]
  · obtain ⟨b, hb, hind⟩ := hΩ _ (eichler_smul_mem_omega hτO hqv₂ hτv₂ hν1 hτv₁ S.bv2v1 m)
    refine ⟨b, hb, fun x hx => ?_⟩
    rw [hind x hx, S.rootB_eq_eichler hqv₂ hqv₁]

end Omega

end CFSG.RankThree.GF2n.Stroth80.Satz5
