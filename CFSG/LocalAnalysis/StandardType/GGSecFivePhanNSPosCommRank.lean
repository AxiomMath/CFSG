module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSCornerDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosLiftE
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLift
import CFSG.RankThree.PartOne.CTP.SeitzDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPF_scalar_eq_one_of_dvd (hC : GGSecFiveNSCornerInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) (hdvd : p ∣ n) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1) :
    z = 1 := by
  by_contra hz1
  have hn0 : 0 < n := by have := h.four_le; omega
  have hne : g₁ * g₂ ≠ g₂ * g₁ := by
    intro hcomm
    have hc1 : ggNSPosPF_commutator g₁ g₂ = 1 :=
      (ggNSPosPF_commutator_eq_one_iff g₁ g₂).mpr hcomm
    have hmat : (1 : Matrix (Fin n) (Fin n) K) = z • 1 := by
      have h := hz
      rw [hc1] at h
      simpa using h
    have h00 : (1 : Matrix (Fin n) (Fin n) K) ⟨0, hn0⟩ ⟨0, hn0⟩ =
        (z • 1 : Matrix (Fin n) (Fin n) K) ⟨0, hn0⟩ ⟨0, hn0⟩ :=
      congrArg (fun M => M ⟨0, hn0⟩ ⟨0, hn0⟩) hmat
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact hz1 h00.symm
  obtain ⟨E, hE, hE1, hE2, hmem, -⟩ := ggNSPosLE_exists_E h
  have hx : g₁ ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))) :=
    hmem b₁ hb₁ g₁ h₁
  have hy : g₂ ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))) :=
    hmem b₂ hb₂ g₂ h₂
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    have hd : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
      rw [h1]
      exact dvd_mul_right _ _
    exact dvd_trans h.dvd hd
  obtain ⟨X, hX, Y, hY, z₀, hXp, hz₀, hXY⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.exists_heisenberg_pair
      h.prime h.odd hpK hn0 hE hx hy hne
  obtain ⟨hnm, hEm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.card_le_of_heisenberg
      h.prime h.odd hpK hn0 hE hX hY hXp hz₀ hXY
  set m := Module.finrank K
    (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1)
  have hp3 : 3 ≤ p := by
    have h2 := h.prime.two_le
    have hne := h.odd
    omega
  have hm2 : 2 ≤ m := by
    have hle := (Nat.pow_le_pow_iff_right h.prime.one_lt).mp (hE2.trans hEm)
    omega
  have hn3 : n - 3 ≤ m + 1 :=
    (Nat.pow_le_pow_iff_right h.prime.one_lt).mp (hE1.trans hEm)
  have h3m : 3 * m ≤ n := by
    rw [hnm]
    exact Nat.mul_le_mul_right m hp3
  have hm_eq : m = 2 := by omega
  have hn_eq : n = 6 := by
    have h1 : 6 ≤ n := by
      have h := h3m
      rw [hm_eq] at h
      omega
    have h2 : n ≤ 6 := by
      have h := hn3
      rw [hm_eq] at h
      omega
    omega
  have hp_eq : p = 3 := by
    have h : p * m = 6 := by rw [← hnm, hn_eq]
    rw [hm_eq] at h
    omega
  subst p
  subst n
  exact hne (hC G 3 B Bs K f ψ h rfl b₁ hb₁ b₂ hb₂ g₁ g₂ h₁ h₂)

theorem ggNSPosPF_scalar_eq_one (hC : GGSecFiveNSCornerInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1) :
    z = 1 := by
  by_cases hdvd : p ∣ n
  · exact ggNSPosPF_scalar_eq_one_of_dvd hC h hb₁ hb₂ h₁ h₂ hdvd hz
  · have hp : z ^ p = 1 := ggNSPosPF_commutator_pow_prime_aux h hb₁ hb₂ h₁ h₂ hz
    have hn : z ^ n = 1 := ggNSPosPF_commutator_pow_n_aux h hb₁ hb₂ h₁ h₂ hz
    have hn0 : n ≠ 0 := by have := h.four_le; omega
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, zero_pow hn0] at hn
      exact zero_ne_one hn
    let u : Kˣ := Units.mk0 z hz0
    have hup : u ^ p = 1 := by ext; simpa [u] using hp
    have hun : u ^ n = 1 := by ext; simpa [u] using hn
    have h1 : orderOf u ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hup
    have h2 : orderOf u ∣ n := orderOf_dvd_iff_pow_eq_one.mpr hun
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd h.prime).mpr hdvd
    have h3 : orderOf u = 1 := by
      apply Nat.dvd_one.mp
      have := Nat.dvd_gcd h1 h2
      rwa [hcop.gcd_eq_one] at this
    have hu1 : u = 1 := orderOf_eq_one_iff.mp h3
    have hzu : (u : K) = 1 := by rw [hu1]; rfl
    simpa [u] using hzu

theorem ggNSPosPF_commutator_eq_one (hC : GGSecFiveNSCornerInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) :
    ggNSPosPF_commutator g₁ g₂ = 1 := by
  obtain ⟨z, hz⟩ := ggNSPosPF_commutator_scalar h hb₁ hb₂ h₁ h₂
  have hz1 : z = 1 := ggNSPosPF_scalar_eq_one hC h hb₁ hb₂ h₁ h₂ hz
  refine Units.ext ?_
  rw [hz, hz1, one_smul]
  rfl

end CFSG.StandardType

end
