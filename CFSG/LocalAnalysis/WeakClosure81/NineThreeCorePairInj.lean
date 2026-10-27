module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairA
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_pair_phi_inj (hc : Nine3Choice V T A K S X p g x) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} {σ : Equiv.Perm (Fin (n + 1))} {bb : Fin (n + 1) → G}
    (he : Nine3PairEnum V K S A g n B σ bb) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) (hUS : ¬ U ≤ S) {i : G} (hi : i ∈ U) (hi1 : i ≠ 1)
    {k : Fin (n + 1)} (hk : k ≠ 0) : ⁅i, bb k⁆ ≠ 1 := by
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  obtain ⟨c, hcfib⟩ := nine3_exists_fib hc hρ hU
  have hc0 : c ≠ 0 := by
    intro h0
    exact hUS ((nine3_fib_zero_iff hc hρ hU).mp (h0 ▸ hcfib))
  have hBkΩ : B k ∈ omegaIn V K (nineE V K) :=
    ⟨(he.Ω k hk).1, (he.Ω k hk).2.trans hc.core.S_le_K⟩
  have hBkfib : Nine3Fib K p ρ (B k) 0 :=
    (nine3_fib_zero_iff hc hρ hBkΩ).mpr (he.Ω k hk).2
  obtain ⟨hbBk, hbR⟩ := he.bb_mem k hk
  intro hcomm
  exact nine3_comm_ne_one hc hρ hU hBkΩ hcfib hBkfib hc0 hi hi1 hbBk hbR
    (commutatorElement_eq_one_iff_mul_comm.mp hcomm)

theorem nine3_pair_psi_inj (hc : Nine3Choice V T A K S X p g x) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} {σ : Equiv.Perm (Fin (n + 1))} {bb : Fin (n + 1) → G}
    (he : Nine3PairEnum V K S A g n B σ bb) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) (hUS : ¬ U ≤ S) {j : G}
    (hj : j ∈ conjSubgroup U g) (hj1 : j ≠ 1) {l : Fin (n + 1)} (hl : l ≠ 1) :
    ⁅g⁻¹ * bb (σ.symm l) * g, j⁆ ≠ 1 := by
  have hk : σ.symm l ≠ 0 := by
    intro h0
    apply hl
    calc l = σ (σ.symm l) := (σ.apply_symm_apply l).symm
      _ = σ 0 := by rw [h0]
      _ = 1 := he.σ0
  let w' : G := g * j * g⁻¹
  have hw'U : w' ∈ U := by
    simpa only [w'] using mem_conjSubgroup_iff.mp hj
  have hjw : j = g⁻¹ * w' * g := by
    simp only [w']
    group
  have hw'1 : w' ≠ 1 := by
    intro h
    apply hj1
    have h1 : g⁻¹ * w' * g = 1 := by
      rw [h]
      group
    rwa [← hjw] at h1
  intro hcomm
  have hconj : g⁻¹ * ⁅bb (σ.symm l), w'⁆ * g = ⁅g⁻¹ * bb (σ.symm l) * g, j⁆ := by
    have h := conjugate_commutatorElement (g₁ := bb (σ.symm l)) (g₂ := w') (g₃ := g⁻¹)
    simp only [inv_inv] at h
    rw [← hjw] at h
    exact h
  have hone : g⁻¹ * ⁅bb (σ.symm l), w'⁆ * g = 1 := by
    rw [hconj]
    exact hcomm
  have hcomm_bb : ⁅bb (σ.symm l), w'⁆ = 1 := by
    have h2 : ⁅bb (σ.symm l), w'⁆ =
        g * (g⁻¹ * ⁅bb (σ.symm l), w'⁆ * g) * g⁻¹ := by group
    rw [h2, hone]
    group
  have hw'bb : ⁅w', bb (σ.symm l)⁆ = 1 := by
    rw [← commutatorElement_inv, hcomm_bb, inv_one]
  exact (nine3_pair_phi_inj hc he hU hUS hw'U hw'1 hk) hw'bb

end CFSG.LocalAnalysis.WeakClosure81
