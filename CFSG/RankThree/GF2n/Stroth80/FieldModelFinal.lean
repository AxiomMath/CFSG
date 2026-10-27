module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelMain

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section Final

variable (H : Hyp79 M V Q)

include H

theorem gammaCompat_of_opposite {g₁ g₂ : G} (hg₁V : conjSubgroup g₁ V ≠ V)
    (hg₁Q : conjSubgroup g₁ V ≤ Q)
    (hg₂V : conjSubgroup g₂ V ≠ V) (hg₂Q : conjSubgroup g₂ V ≤ Q) {n : ℕ}
    (hVn : Nat.card V = 2 ^ n) (D₁ : MulData V (conjSubgroup g₁ V) Q (GaloisField 2 n))
    (D₂ : MulData V (conjSubgroup g₂ V) Q (GaloisField 2 n)) : GammaCompat V D₁.γ D₂.γ := by
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push Not at hcon
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := H.q4
    omega
  have hKcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  by_cases hn3 : 3 ≤ n
  · obtain ⟨n', hVn', D, τ, a, hτM, hτH, hτU, hτo, hao, hγ, hψ, -⟩ :=
      H.exists_mulData_torus hg₁V hg₁Q
    have hnn : n = n' := Nat.pow_right_injective (le_refl 2) (hVn.symm.trans hVn')
    subst hnn
    have hmem := opposite_mem_class_of_three_le H hg₁V hg₁Q hn3 D hτM hτH hτU hτo hao hγ hψ
      hg₂V hg₂Q
    obtain ⟨-, -, -, D', c, σ, hc, hcσ⟩ := hmem
    exact GammaCompat.trans (MulData.compat_same D₁ D : GammaCompat V D₁.γ D.γ)
      (GammaCompat.trans (⟨c, σ, hc, hcσ⟩ : GammaCompat V D.γ D'.γ)
        (MulData.compat_same D' D₂ : GammaCompat V D'.γ D₂.γ))
  · have hn : n = 2 := by omega
    subst hn
    have hK : Nat.card (GaloisField 2 2) = 4 := by rw [hKcard]; norm_num
    obtain ⟨σ', hσ'⟩ := semilinear_of_card_four hK (MulData.thetaHom D₁ D₂)
      (MulData.thetaHom_bijective D₁ D₂)
    have hθb := MulData.thetaHom_bijective D₁ D₂
    have hθ1 : (MulData.thetaHom D₁ D₂) 1 ≠ 0 := fun h0 =>
      one_ne_zero (hθb.1 (by rw [h0, map_zero]))
    refine ⟨_, σ', hθ1, fun v hv => ?_⟩
    rw [← MulData.thetaHom_γ D₁ D₂ hv]
    exact hσ' _

theorem gammaCompat_of_opposite' {U₁ U₂ : Subgroup G} (hU₁g : ∃ g : G, U₁ = conjSubgroup g V)
    (hU₁V : U₁ ≠ V) (hU₁Q : U₁ ≤ Q) (hU₂g : ∃ g : G, U₂ = conjSubgroup g V) (hU₂V : U₂ ≠ V)
    (hU₂Q : U₂ ≤ Q) {n : ℕ} (hVn : Nat.card V = 2 ^ n) (D₁ : MulData V U₁ Q (GaloisField 2 n))
    (D₂ : MulData V U₂ Q (GaloisField 2 n)) : GammaCompat V D₁.γ D₂.γ := by
  obtain ⟨g₁, rfl⟩ := hU₁g
  obtain ⟨g₂, rfl⟩ := hU₂g
  exact gammaCompat_of_opposite H hU₁V hU₁Q hU₂V hU₂Q hVn D₁ D₂

theorem mem_class_of_opposite {g₁ g₂ : G} (hg₁V : conjSubgroup g₁ V ≠ V)
    (hg₁Q : conjSubgroup g₁ V ≤ Q) (hg₂V : conjSubgroup g₂ V ≠ V)
    (hg₂Q : conjSubgroup g₂ V ≤ Q) {n : ℕ} (hVn : Nat.card V = 2 ^ n)
    (D₁ : MulData V (conjSubgroup g₁ V) Q (GaloisField 2 n)) :
    conjSubgroup g₂ V ∈ classOf V Q D₁.γ := by
  obtain ⟨n₂, hVn₂, ⟨D₂⟩⟩ := H.exists_mulData hg₂V hg₂Q
  have hnn : n = n₂ := Nat.pow_right_injective (le_refl 2) (hVn.symm.trans hVn₂)
  subst hnn
  obtain ⟨c, σ, hc, hcσ⟩ := gammaCompat_of_opposite H hg₁V hg₁Q hg₂V hg₂Q hVn D₁ D₂
  exact ⟨⟨g₂, rfl⟩, hg₂Q, hg₂V, D₂, c, σ, hc, hcσ⟩

theorem classGroup_eq_self {g₁ : G} (hg₁V : conjSubgroup g₁ V ≠ V)
    (hg₁Q : conjSubgroup g₁ V ≤ Q) {n : ℕ} (hVn : Nat.card V = 2 ^ n)
    (D₁ : MulData V (conjSubgroup g₁ V) Q (GaloisField 2 n)) : classGroup V Q D₁.γ = Q := by
  refine le_antisymm (classGroup_le H.V_le_Q) (H.gen.le.trans (iSup₂_le fun g hg => ?_))
  by_cases h1 : conjSubgroup g V = V
  · exact h1.le.trans V_le_classGroup
  · exact le_classGroup_of_mem (mem_class_of_opposite H hg₁V hg₁Q h1 hg hVn D₁)

theorem semilinear_of_mem_M {g₁ : G} (hg₁V : conjSubgroup g₁ V ≠ V)
    (hg₁Q : conjSubgroup g₁ V ≤ Q) {n : ℕ} (hVn : Nat.card V = 2 ^ n)
    (D₁ : MulData V (conjSubgroup g₁ V) Q (GaloisField 2 n)) {m : G} (hm : m ∈ M) :
    ∃ (c : GaloisField 2 n) (σ : GaloisField 2 n ≃+* GaloisField 2 n), c ≠ 0 ∧
      ∀ v ∈ V, D₁.γ (m * v * m⁻¹) = c * σ (D₁.γ v) := by
  have hh := H.toHyp218 hg₁V hg₁Q
  have hmV' : m ∈ Subgroup.normalizer (V : Set G) := hh.M_le_normalizer hm
  have hmQ' : m ∈ Subgroup.normalizer (Q : Set G) := hh.M_le_normalizer_Q hm
  have hmV : m⁻¹ ∈ Subgroup.normalizer (V : Set G) := inv_mem hmV'
  have hmQ : m⁻¹ ∈ Subgroup.normalizer (Q : Set G) := inv_mem hmQ'
  have hU₂g : ∃ g : G, conjSubgroup m⁻¹ (conjSubgroup g₁ V) = conjSubgroup g V :=
    ⟨m⁻¹ * g₁, by rw [conjSubgroup_mul]⟩
  have hU₂Q : conjSubgroup m⁻¹ (conjSubgroup g₁ V) ≤ Q := by
    intro x hx
    have h1 : m⁻¹⁻¹ * x * m⁻¹ ∈ conjSubgroup g₁ V := mem_conjSubgroup.mp hx
    have h2 : m⁻¹ * (m⁻¹⁻¹ * x * m⁻¹) * m ∈ Q :=
      (mem_iff_conj_inv_of_normalizer hmQ' _).mp (hg₁Q h1)
    rwa [show m⁻¹ * (m⁻¹⁻¹ * x * m⁻¹) * m = x by group] at h2
  have hU₂V : conjSubgroup m⁻¹ (conjSubgroup g₁ V) ≠ V := by
    intro h
    apply hg₁V
    have h1 : conjSubgroup m (conjSubgroup m⁻¹ (conjSubgroup g₁ V)) = conjSubgroup g₁ V := by
      rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    have h2 : conjSubgroup m V = V := conjSubgroup_eq_self_iff.mpr hmV'
    rw [← h1, h, h2]
  obtain ⟨c, σ, hc, hcσ⟩ := gammaCompat_of_opposite' H ⟨g₁, rfl⟩ hg₁V hg₁Q hU₂g hU₂V hU₂Q hVn D₁
    (D₁.conjData hmV hmQ)
  refine ⟨c, σ, hc, fun v hv => ?_⟩
  have := hcσ v hv
  rwa [MulData.conjData_γ, inv_inv] at this

end Final

end CFSG.RankThree.GF2n.Stroth80.FieldModel
