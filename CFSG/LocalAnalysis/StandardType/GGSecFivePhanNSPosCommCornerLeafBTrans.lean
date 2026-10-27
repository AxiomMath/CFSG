module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBTransG

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

private theorem ggNSPosPF3C_cube_root_cases {z : K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hz0 : z ≠ 0) {s : Kˣ} (hs3 : s ^ 3 = 1) :
    s = 1 ∨ s = Units.mk0 z hz0 ∨ s = (Units.mk0 z hz0) ^ 2 := by
  have hquad : z ^ 2 + z + 1 = 0 := by
    have hprod : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      have h1 : (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
      rw [h1, hz3]; ring
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hz1
    · exact h
  have hsK : (s : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hs3, Units.val_one]
  have hfac : ((s : K) - 1) * ((s : K) - z) * ((s : K) - z ^ 2) = 0 := by
    have h1 : ((s : K) - 1) * ((s : K) - z) * ((s : K) - z ^ 2) =
        ((s : K) ^ 3 - 1) + (z ^ 2 + z + 1) * ((s : K) - (s : K) ^ 2) +
          (z ^ 3 - 1) * ((s : K) - 1) := by ring
    rw [h1, hquad, hz3, hsK]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · left
      exact Units.ext (by simpa using sub_eq_zero.mp h)
    · right; left
      exact Units.ext (by simpa using sub_eq_zero.mp h)
  · right; right
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    simpa using sub_eq_zero.mp h

private theorem ggNSPosPF3C_commutator_eq_pow {c g : Su K 2 f 6}
    (hμ : ∀ s : Kˣ, s ^ 3 = 1 → ∀ u : Su K 2 f 6,
      (u : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) s → ψ u = 1)
    {b : G} {ℓ : GL (Fin 6) K}
    (hℓ : GGInducesUnitary (p := 2) (f := f) ψ b ℓ)
    {s : Kˣ} {j : ℕ} (hs3 : s ^ 3 = 1)
    (hconj : (g : GL (Fin 6) K) * ℓ * (g : GL (Fin 6) K)⁻¹ * ℓ⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) s * (c : GL (Fin 6) K) ^ j) :
    ψ g * b * (ψ g)⁻¹ * b⁻¹ = (ψ c) ^ j := by
  obtain ⟨y₀, hy₀eq, hy₀ψ⟩ := hℓ.2 g⁻¹
  have hgy : ((g * y₀ : Su K 2 f 6) : GL (Fin 6) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) s * (c : GL (Fin 6) K) ^ j := by
    rw [Subgroup.coe_mul, hy₀eq, Subgroup.coe_inv, ← hconj]
    group
  have hu : (((g * y₀) * (c ^ j)⁻¹ : Su K 2 f 6) : GL (Fin 6) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) s := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hgy]
    group
  have hψu : ψ ((g * y₀) * (c ^ j)⁻¹) = 1 := hμ s hs3 _ hu
  have hy₀ψ' : ψ y₀ = b * (ψ g)⁻¹ * b⁻¹ := by
    rw [← hy₀ψ, map_inv]
  calc ψ g * b * (ψ g)⁻¹ * b⁻¹
      = ψ g * (b * (ψ g)⁻¹ * b⁻¹) := by group
    _ = ψ g * ψ y₀ := by rw [← hy₀ψ']
    _ = ψ (g * y₀) := (map_mul ψ g y₀).symm
    _ = ψ ((g * y₀) * (c ^ j)⁻¹ * c ^ j) := by
          rw [show (g * y₀) * (c ^ j)⁻¹ * c ^ j = g * y₀ by group]
    _ = ψ ((g * y₀) * (c ^ j)⁻¹) * ψ (c ^ j) := map_mul ψ _ _
    _ = 1 * (ψ c) ^ j := by rw [hψu, map_pow]
    _ = (ψ c) ^ j := one_mul _

theorem ggNSPosPF3C_psi_scalar_eq_one {z : K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hz0 : z ≠ 0)
    {x : Su K 2 f 6}
    (hx : (x : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 z hz0))
    (hxeq : ψ x = 1) :
    ∀ s : Kˣ, s ^ 3 = 1 → ∀ u : Su K 2 f 6,
      (u : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) s → ψ u = 1 := by
  intro s hs3 u hu
  rcases ggNSPosPF3C_cube_root_cases hz3 hz1 hz0 hs3 with hs | hs | hs
  · have hu1 : u = 1 := by
      apply Subtype.ext
      simpa [hu, hs]
    rw [hu1, map_one]
  · have hux : u = x := by
      apply Subtype.ext
      simpa [hu, hs, hx]
    rw [hux, hxeq]
  · have hu2 : u = x ^ 2 := by
      apply Subtype.ext
      rw [hu, hs, map_pow, Subgroup.coe_pow, hx]
    rw [hu2, map_pow, hxeq, one_pow]

theorem ggNSPosPF3C_transvection_contradiction (h : GGNSLocalHyp 3 B Bs K f 6 ψ)
    (g c : Su K 2 f 6)
    (hμ : ∀ s : Kˣ, s ^ 3 = 1 → ∀ u : Su K 2 f 6,
      (u : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) s → ψ u = 1)
    (hc3 : c ^ 3 = 1)
    (hcns : ∀ a : K, ((c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ≠ a • 1)
    (hgc : g * c = c * g)
    (hcomm : ∀ b ∈ Bs, ∀ ℓ : GL (Fin 6) K, GGInducesUnitary (p := 2) (f := f) ψ b ℓ →
      ℓ * (c : GL (Fin 6) K) = (c : GL (Fin 6) K) * ℓ ∧
        ∃ (s : Kˣ) (j : ℕ), s ^ 3 = 1 ∧
          (g : GL (Fin 6) K) * ℓ * (g : GL (Fin 6) K)⁻¹ * ℓ⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 6) s * (c : GL (Fin 6) K) ^ j)
    (hY : ∃ b ∈ Bs, ∃ ℓ : GL (Fin 6) K, GGInducesUnitary (p := 2) (f := f) ψ b ℓ ∧
      ∃ (s : Kˣ) (j : ℕ), s ^ 3 = 1 ∧ ¬ 3 ∣ j ∧
        (g : GL (Fin 6) K) * ℓ * (g : GL (Fin 6) K)⁻¹ * ℓ⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 6) s * (c : GL (Fin 6) K) ^ j) :
    False := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · exfalso
      have hdvd := h.dvd
      rw [hf0] at hdvd
      norm_num at hdvd
    · exact hfpos
  have hc₀3 : (ψ c) ^ 3 = 1 := by
    rw [← map_pow, hc3, map_one]
  have hc₀1 : ψ c ≠ 1 := by
    intro hψc
    have hc_ker : c ∈ ψ.ker := MonoidHom.mem_ker.mpr hψc
    have hc_center : c ∈ Subgroup.center (Su K 2 f 6) := h.ker hc_ker
    have hN : ∀ u : Su K 2 f 6,
        (c : GL (Fin 6) K) * (u : GL (Fin 6) K) =
          (u : GL (Fin 6) K) * (c : GL (Fin 6) K) := by
      intro u
      have hu : u * c = c * u := Subgroup.mem_center_iff.mp hc_center u
      have h1 : (c * u : Su K 2 f 6) = u * c := hu.symm
      simpa only [Subgroup.coe_mul] using
        congrArg (fun v : Su K 2 f 6 => (v : GL (Fin 6) K)) h1
    obtain ⟨a, ha⟩ := ggNSPosPF_exists_scalar_of_commute_SUid (K := K) (f := f) (n := 6)
      h.card hf (by norm_num) hN
    exact hcns (a : K) (by
      rw [ha, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal])
  have hc₀cent : ψ c ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨ℓ, hℓ⟩ := h.acts b hb
    obtain ⟨hℓc, -⟩ := hcomm b hb ℓ hℓ
    obtain ⟨y, hyeq, hyψ⟩ := hℓ.2 c
    have hconj : ℓ * (c : GL (Fin 6) K) * ℓ⁻¹ = (c : GL (Fin 6) K) := by
      rw [hℓc]; group
    have hy : y = c := Subtype.ext (by rw [hyeq, hconj])
    have hbψ : b * ψ c * b⁻¹ = ψ c := by rw [hyψ, hy]
    calc b * ψ c = b * ψ c * b⁻¹ * b := by group
      _ = ψ c * b := by rw [hbψ]
  have hc₀mem : ψ c ∈ Bs := h.bstar.2.2.2 (ψ c) hc₀cent hc₀3
  have hγc : ψ g * ψ c = ψ c * ψ g := by
    have h1 := congrArg ψ hgc
    rw [map_mul, map_mul] at h1
    exact h1
  have hγ : ∀ b ∈ Bs, ∃ j : ℕ, ψ g * b * (ψ g)⁻¹ * b⁻¹ = (ψ c) ^ j := by
    intro b hb
    obtain ⟨ℓ, hℓ⟩ := h.acts b hb
    obtain ⟨-, s, j, hs3, hconj⟩ := hcomm b hb ℓ hℓ
    exact ⟨j, ggNSPosPF3C_commutator_eq_pow hμ hℓ hs3 hconj⟩
  have hγ1 : ∃ b ∈ Bs, ψ g * b * (ψ g)⁻¹ * b⁻¹ ≠ 1 := by
    obtain ⟨b, hb, ℓ, hℓ, s, j, hs3, h3j, hconj⟩ := hY
    refine ⟨b, hb, ?_⟩
    have hceq := ggNSPosPF3C_commutator_eq_pow hμ hℓ hs3 hconj
    intro h1
    have hcj : (ψ c) ^ j = 1 := by rw [← hceq, h1]
    have hdvd : orderOf (ψ c) ∣ j := orderOf_dvd_iff_pow_eq_one.mpr hcj
    have hord : orderOf (ψ c) = 3 := orderOf_eq_prime (p := 3) hc₀3 hc₀1
    rw [hord] at hdvd
    exact h3j hdvd
  exact ggNSPosPF3C_false_of_shear h.noTr h.bstar.2.1 hc₀mem hc₀1 hc₀3 hγc hγ hγ1

end CFSG.StandardType

end
