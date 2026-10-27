module

public import CFSG.RankThree.GF2n.Stroth80.Satz5Omega
public import CFSG.RankThree.GF2n.Stroth80.Satz5Hyperbolic
public import CFSG.RankThree.GF2n.Stroth80.Sec25c

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim79 CFSG.RankThree.GF2n.Stroth80.Satz5
open scoped commutatorElement

section Abstract

variable {G : Type} [Group G] {P Z X : Subgroup G} {K : Type} [Field K] {γ : G → K}

@[expose] def InducesOmega (M₀ : Tim79.QuadModel P Z K γ) (X : Subgroup G) : Prop :=
  ∀ T ∈ omegaOf M₀, ∃ g ∈ X, Induces M₀ g T

theorem beisiegel_satz5 [CharP K 2] (M₀ : Tim79.QuadModel P Z K γ) (R : Tim79.GammaReg P Z γ)
    (hK : 2 < Nat.card K)
    (hyp : ∃ S₁ S₂ : Submodule K M₀.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M₀.Qf x = 0) ∧
      ∀ x ∈ S₂, M₀.Qf x = 0)
    (hdim : 4 ≤ Module.finrank K M₀.E) (hnorm : ∀ g ∈ X, ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (hcent : ∀ g ∈ X, ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hfaith : ∀ g ∈ X, (∀ x ∈ P, M₀.π (g * x * g⁻¹) = M₀.π x) →
      ∃ p ∈ P, ∀ x ∈ P, g * x * g⁻¹ = p * x * p⁻¹)
    (hΩ : InducesOmega M₀ X) : False := by
  obtain ⟨S₁, S₂, hS, hS₁, hS₂⟩ := hyp
  obtain ⟨v₁, v₂, w₁, w₂, qv₁, qv₂, qw₁, -, b11, b22, b12, b21, vv, ww⟩ :=
    exists_hyperbolic_quadruple M₀ hS hS₁ hS₂ hdim
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨ν, hν0, hν1⟩ := Satz5.exists_ne_zero_one hK
  exact (Setting.mk R h2 b11 b22 b12 b21 vv ww hnorm hcent hfaith :
    Setting M₀ X v₁ v₂ w₁ w₂).false_of_omega qv₁ qv₂ qw₁ hν0 hν1 hΩ

end Abstract

section Stroth

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem StrothHyp.satz5_conditions (H : StrothHyp M Q Z) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hreg : Tim79.GammaReg Q Z γ) {X : Subgroup G}
    (hX : X ≤ H0 M Z) :
    (∀ g ∈ X, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) ∧ (∀ g ∈ X, ∀ z ∈ Z, g * z * g⁻¹ = z) ∧
      ∀ g ∈ X, (∀ x ∈ Q, M₀.π (g * x * g⁻¹) = M₀.π x) →
        ∃ p ∈ Q, ∀ x ∈ Q, g * x * g⁻¹ = p * x * p⁻¹ := by
  refine ⟨fun g hg x hx => ?_, fun g hg z hz => ?_, fun g hg hπ => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hX hg).1) x).mp hx
  · have h := Subgroup.mem_centralizer_iff.mp (hX hg).2 z hz
    rw [← h]
    group
  · refine ⟨g, ?_, fun x _ => rfl⟩
    refine H.centralizer_Qt g (hX hg).1 fun y hy => ?_
    have hgy : g * y * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hX hg).1) y).mp hy
    have h1 : y⁻¹ * (g * y * g⁻¹) ∈ Z :=
      (Tim79.QuadModel.pi_eq_iff M₀ hy hgy).mp (hπ y hy).symm
    obtain ⟨z, hz⟩ : ∃ z : G, z = y⁻¹ * (g * y * g⁻¹) := ⟨_, rfl⟩
    rw [← hz] at h1
    have h3 : ⁅g, y⁆ = y * z * y⁻¹ := by
      rw [hz]
      simp only [commutatorElement_def]
      group
    have h4 := central_of_reg M₀ hreg h1 hy
    rw [h3, show y * z * y⁻¹ = z * y * y⁻¹ by rw [h4], mul_inv_cancel_right]
    exact h1

theorem BeisiegelSatz5Stroth (H : StrothHyp M Q Z) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {w : ℕ} (hw : Width Q Z w)
    (hw2 : 2 ≤ w) {X : Subgroup G} (hX : X ≤ H0 M Z) (hΩ : InducesOmega M₀ X) : False := by
  have hcard : 2 < Nat.card K := by
    rw [h.card]
    have := H.q4
    omega
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hdim : Module.finrank K M₀.E = 2 * w := h.finrank_E hw (by omega)
  have h2 : (2 : K) = 0 := by
    obtain ⟨n, k, -, hcp⟩ := H.cp
    obtain ⟨z, hz, hγz⟩ := h.reg.surj 1
    have hz2 : z * z = 1 := by rw [← sq]; exact sq_eq_one_of_cp hcp z hz
    have := h.reg.add z hz z hz
    rw [hz2, h.reg.one, hγz] at this
    linear_combination -this
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨hnorm, hcent, hfaith⟩ := H.satz5_conditions (M₀ := M₀) h.reg hX
  exact beisiegel_satz5 M₀ h.reg hcard h.hyperbolic (by omega) hnorm hcent hfaith hΩ

end Stroth

end CFSG.RankThree.GF2n.Stroth80
