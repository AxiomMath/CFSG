module

public import CFSG.Milestones.ASVolI.F4L3Aut

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

theorem burnsideF429a_key_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hk hcomm
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, -⟩ := burnsideF447_setup hf hyp.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hNp := burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ := by
    have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf hyp.toHypF_4_4g
    rw [burnsideF4d_pCoreOf_inf_eq (M₁ ⊓ M₂) hle]
    exact hNp.2
  have C : burnsideF447_Ctx f Φ ρ Gp := ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩
  have hrN : r ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) := by
    rw [← hNp.1]
    exact hr
  obtain ⟨u, hu, b, hb, rfl⟩ := burnsideF447_frattini C.hq hΦ hrN
  obtain ⟨δ, t₁, t₂, σ, hρb⟩ := burnsideF447_diag C.hq hΦ hΦρ hE hb.1 hb.2
  have hfix : ∀ a : Fˣ, Units.map σ.toMonoidHom a = a := by
    intro a
    have hdT : proj 3 F (dMat a a⁻¹) ∈ torus3 F := dP_mem_torus3 _ _
    have hdN := map_mem_normalizer_map Φ (torus3_le_normalizer hdT)
    have hΦd : Φ (proj 3 F (dMat a a⁻¹)) ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      refine ⟨?_, ?_⟩
      · rw [← hrange]
        exact ⟨_, rfl⟩
      · rw [hNp.1]
        exact hdN
    have h1 := hcomm _ hΦd
    rw [hS] at h1
    have h2 : b * Φ (proj 3 F (dMat a a⁻¹)) * b⁻¹ * (Φ (proj 3 F (dMat a a⁻¹)))⁻¹ ∈
        (projUnitriangular 3 F).map Φ := by
      have e : b * Φ (proj 3 F (dMat a a⁻¹)) * b⁻¹ * (Φ (proj 3 F (dMat a a⁻¹)))⁻¹ =
          u⁻¹ * (u * b * Φ (proj 3 F (dMat a a⁻¹)) * (u * b)⁻¹ *
            (Φ (proj 3 F (dMat a a⁻¹)))⁻¹) *
          (Φ (proj 3 F (dMat a a⁻¹)) * u * (Φ (proj 3 F (dMat a a⁻¹)))⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) h1)
        ((Subgroup.mem_normalizer_iff.mp hdN u).mp hu)
    have hact : ρ b (proj 3 F (dMat a a⁻¹)) =
        proj 3 F (dMat (Units.map σ.toMonoidHom a) (Units.map σ.toMonoidHom a⁻¹)) := by
      rw [hρb, MulAut.mul_apply, MulAut.mul_apply, burnsideF447_fieldAut_dMat,
        MulAut.conj_apply, burnsideF447_torus_conj_fix (dP_mem_torus3 _ _) (dP_mem_torus3 _ _),
        conjAut_nuDiag_dMat]
    have h3 : ρ b (proj 3 F (dMat a a⁻¹)) * (proj 3 F (dMat a a⁻¹))⁻¹ ∈
        projUnitriangular 3 F := by
      refine (Subgroup.mem_map_iff_mem hΦ).mp ?_
      rw [map_mul, map_inv, hΦρ]
      exact h2
    have h4 : ρ b (proj 3 F (dMat a a⁻¹)) * (proj 3 F (dMat a a⁻¹))⁻¹ ∈ torus3 F := by
      rw [hact]
      exact Subgroup.mul_mem _ (dP_mem_torus3 _ _) (Subgroup.inv_mem _ hdT)
    have h5 := burnsideF447_two_odd (isSylowTwoOf_U (F := F)).2.1 (torus3_odd (F := F)) h3 h4
    have h6 : ρ b (proj 3 F (dMat a a⁻¹)) = proj 3 F (dMat a a⁻¹) := mul_inv_eq_one.mp h5
    rw [hact] at h6
    have h7 : Units.map σ.toMonoidHom a⁻¹ = (Units.map σ.toMonoidHom a)⁻¹ := map_inv _ _
    rw [h7] at h6
    exact burnsideF447_dMat_inj h6
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    show σ x = x
    by_cases hx : x = 0
    · rw [hx, map_zero]
    · have h1 : ((Units.map σ.toMonoidHom (Units.mk0 x hx) : Fˣ) : F) = x := by
        rw [hfix]
        rfl
      simpa using h1
  have hconjL : ∀ p : projectiveSL 3 F, MulAut.conj p ∈ linearAutGroup 3 F := by
    intro p
    obtain ⟨g, rfl⟩ := proj_surjective 3 F p
    rw [← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _
  have hlin : ρ (u * b) ∈ linearAutGroup 3 F := by
    obtain ⟨p, -, rfl⟩ := hu
    rw [map_mul, burnsideF447_rho_Phi hΦ hΦρ, hρb, hσ, map_one, mul_one]
    exact Subgroup.mul_mem _ (hconjL p)
      (Subgroup.mul_mem _ (conjAut_mem_linearAutGroup _) (hconjL _))
  have hinn : ρ (u * b) ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    refine CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (fun h => ?_) _
      hlin k ?_
    · have := h.trans (Nat.gcd_dvd_left 3 _)
      omega
    · rw [← map_pow, hk, map_one]
      exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := hinn
  have hrg : u * b = Φ g := hρ (by rw [burnsideF447_rho_Phi hΦ hΦρ, hg])
  rw [hrg, ← hrange]
  exact ⟨g, rfl⟩

end CFSG.ASVolI
