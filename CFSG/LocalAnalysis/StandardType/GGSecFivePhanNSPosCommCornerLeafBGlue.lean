module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBIdem
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBShear
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBTrans

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

private theorem ggNSPosPF3C_omega_cube_of_quadratic {K : Type} [CommRing K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
  have h' : ω ^ 3 - 1 = 0 := by
    rw [← h]
    ring
  exact sub_eq_zero.mp h'

private theorem ggNSPosPF3C_eq_one_of_mul_self_eq_one {K : Type} [Field K] [CharP K 2] {a : K}
    (h : a * a = 1) : a = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hzero : (a - 1) * (a - 1) = 0 := by
    have h1 : (a - 1) * (a - 1) = a * a + 1 := by
      have e : (a - 1) * (a - 1) = a * a - 2 * a + 1 := by ring
      rw [e, h2]
      ring
    rw [h1, h]
    rw [one_add_one_eq_two, h2]
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hzero)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

theorem ggNSPosPF3C_lift_mul_eq_smul (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin 6) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) :
    ∃ ζ : Kˣ, (g₁ : Matrix (Fin 6) (Fin 6) K) * (g₂ : Matrix (Fin 6) (Fin 6) K) =
      (ζ : K) • ((g₂ : Matrix (Fin 6) (Fin 6) K) * (g₁ : Matrix (Fin 6) (Fin 6) K)) := by
  obtain ⟨z, hz⟩ := ggNSPosPF_commutator_scalar h hb₁ hb₂ h₁ h₂
  have hz0 : z ≠ 0 := by
    intro hz_eq
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero (ggNSPosPF_commutator g₁ g₂)
    rw [hz, hz_eq, zero_smul] at hdet
    simpa using hdet
  refine ⟨Units.mk0 z hz0, ?_⟩
  have hcomm : ggNSPosPF_commutator g₁ g₂ * (g₂ * g₁) = g₁ * g₂ := by
    unfold ggNSPosPF_commutator
    group
  have hmat := congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) hcomm
  simp only [Units.val_mul] at hmat
  rw [hz, Matrix.smul_mul, Matrix.one_mul] at hmat
  simpa using hmat.symm

theorem ggNSPosPF3C_false_of_shearData (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {ω : K}
    {X Y c : GL (Fin 6) K}
    (hD : ggNSPosPF3C_ShearData (unitaryInvolution K 2 f) ω X Y c)
    (hX : ∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b X)
    (hY : ∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b Y)
    (hc : ∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b c)
    (hμ : ∀ s : Kˣ, s ^ 3 = 1 → ∀ u : Su K 2 f 6,
      (u : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) s → ψ u = 1) :
    False := by
  obtain ⟨g, hgSU, hgc, hsh, sY, hsY, hgY⟩ :=
    ggNSPosPF3C_exists_shear (n := 6) (σ := unitaryInvolution K 2 f) hD
  have hcSU : c ∈ SUid (unitaryInvolution K 2 f) 6 := ggNSPosPF3C_c_mem_SUid hD
  let gS : Su K 2 f 6 := ⟨g, hgSU⟩
  let cS : Su K 2 f 6 := ⟨c, hcSU⟩
  have hc3mat : (c : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 :=
    ggNSPosPF3C_pow_three hD.omega hD.c_quad
  have hc3 : cS ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val] using hc3mat
  have hgcS : gS * cS = cS * gS := by
    apply Subtype.ext
    exact hgc
  have hcomm : ∀ b ∈ Bs, ∀ ℓ : GL (Fin 6) K,
      GGInducesUnitary (p := 2) (f := f) ψ b ℓ →
      ℓ * (cS : GL (Fin 6) K) = (cS : GL (Fin 6) K) * ℓ ∧
        ∃ (s : Kˣ) (j : ℕ), s ^ 3 = 1 ∧
          (gS : GL (Fin 6) K) * ℓ * (gS : GL (Fin 6) K)⁻¹ * ℓ⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 6) s * (cS : GL (Fin 6) K) ^ j := by
    intro b hb ℓ hℓ
    obtain ⟨_, hbc, hcind⟩ := hc
    obtain ⟨ζc, hζc⟩ := ggNSPosPF3C_lift_mul_eq_smul h hb hbc hℓ hcind
    have hζc1 : ζc = 1 :=
      ggNSPosPF3C_scalar_eq_one_of_conj hD.omega hD.c_quad hD.c_nonscalar hζc
    have hℓc : ℓ * c = c * ℓ := by
      apply Units.ext
      rw [hζc1] at hζc
      simpa using hζc
    obtain ⟨_, hbX, hXind⟩ := hX
    obtain ⟨ζ, hζ⟩ := ggNSPosPF3C_lift_mul_eq_smul h hb hbX hℓ hXind
    have hζ3 : (ζ : K) ^ 3 = 1 := by
      have hdet := congrArg Matrix.det hζ
      simp only [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin] at hdet
      have hdℓ : (ℓ : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
        Matrix.GeneralLinearGroup.det_ne_zero ℓ
      have hdX : (X : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
        Matrix.GeneralLinearGroup.det_ne_zero X
      have hd : (ℓ : Matrix (Fin 6) (Fin 6) K).det *
          (X : Matrix (Fin 6) (Fin 6) K).det ≠ 0 := mul_ne_zero hdℓ hdX
      have h6 : (ζ : K) ^ 6 = 1 := by
        rw [mul_comm ((X : Matrix (Fin 6) (Fin 6) K).det)
          ((ℓ : Matrix (Fin 6) (Fin 6) K).det)] at hdet
        refine mul_right_cancel₀ hd (by rw [one_mul]; exact hdet.symm)
      have h3sq : (ζ : K) ^ 3 * (ζ : K) ^ 3 = 1 := by
        rw [← h6]
        ring
      exact ggNSPosPF3C_eq_one_of_mul_self_eq_one h3sq
    obtain ⟨j, _, hcommj⟩ := hsh ℓ ζ hℓc hζ hζ3
    refine ⟨hℓc, ζ ^ 2, j, ?_, ?_⟩
    · apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      have : ((ζ : K) ^ 2) ^ 3 = ((ζ : K) ^ 3) ^ 2 := by ring
      rw [this, hζ3, one_pow]
    · simpa using hcommj
  have hY' : ∃ b ∈ Bs, ∃ ℓ : GL (Fin 6) K,
      GGInducesUnitary (p := 2) (f := f) ψ b ℓ ∧
        ∃ (s : Kˣ) (j : ℕ), s ^ 3 = 1 ∧ ¬ 3 ∣ j ∧
          (gS : GL (Fin 6) K) * ℓ * (gS : GL (Fin 6) K)⁻¹ * ℓ⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 6) s * (cS : GL (Fin 6) K) ^ j := by
    obtain ⟨bY, hbY, hYind⟩ := hY
    refine ⟨bY, hbY, Y, hYind, sY, 1, ?_, by norm_num, ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, hsY]
      have hω3 : ω ^ 3 = 1 := ggNSPosPF3C_omega_cube_of_quadratic hD.omega
      have : ((ω : K) ^ 2) ^ 3 = ((ω : K) ^ 3) ^ 2 := by ring
      rw [this, hω3, one_pow]
    · simpa using hgY
  exact ggNSPosPF3C_transvection_contradiction h gS cS hμ hc3
    (fun a => hD.c_nonscalar a) hgcS hcomm hY'

end CFSG.StandardType

end
