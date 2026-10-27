module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrRes
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormModelA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem ggQ2g_E7_two_ne : ((2 : ℤ) : ZMod 3) ≠ 0 := by decide

private theorem ggQ2g_E7_two_ne' : (2 : ZMod 3) ≠ 0 := by decide

private theorem ggQ2g_E7_scalar (s : ZMod 3) (h : s ≠ 0) : s = 1 ∨ s = 2 := by
  revert s
  decide

theorem ggQ2_gammaNbrGraphE7_false (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hK1 : GGQTwoK1 p B Bs x D J) (M : GGQTwoModel p Bs x y D L J K) (e : Fin 7 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E 7 i j) (he0 : M.b = e 0)
    (hea : M.a = e 1)
    (hV : Submodule.span (ZMod p)
      (insert M.yV (Set.range fun i : {k // k ≠ M.b} => M.coroot i)) = ⊤)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφy : ggLin (p := p) M.model φ M.yV ∈ Submodule.span (ZMod p) {M.yV})
    (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod p) (c : ZMod p)
    (w : M.V ≃ₗ[ZMod p] M.V) (hSc : M.toLin.ScaledAut M.b π μ)
    (hw : w ∈ M.toLin.parab {k | k ≠ M.b})
    (hT : ∀ i : {k // k ≠ M.b},
      ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    (hπa : π ⟨M.a, M.a_ne_b⟩ ≠ ⟨M.a, M.a_ne_b⟩) : False := by
  subst hp
  classical
  obtain ⟨σ, hσ, hσc⟩ := ggQ2g_E7_sigma M.cartan e M.b he0 hecart
  obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport M.toLin M.b σ hσc hSc
  have hπσ : ∀ i, π (σ i) = σ (π' i) := fun i => hπσ₀ i
  have hμσ : ∀ i, μ (σ i) = μ' i := fun i => hμσ₀ i
  obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD 6 (by norm_num) π' μ' hμ'0 hrel
  have hM : M.cartan = (CartanMatrix.E 7).submatrix e.symm e.symm := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [← hecart (e.symm i) (e.symm j)]
    simp
  have hdet : ((M.toLin.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
    show ((M.cartan.det : ℤ) : ZMod 3) ≠ 0
    rw [hM, Matrix.det_submatrix_equiv_self, CartanMatrix.E₇_det]
    exact ggQ2g_E7_two_ne
  have hbas : M.toLin.Basis := ggQ2g_basis M.toLin M.b M.yV hdet hV
  have hnot := ggQ2g_y_not_mem M.toLin M.b M.yV hbas hV
  have hy0 : M.yV ≠ 0 := fun h => hnot (by rw [h]; exact Submodule.zero_mem _)
  have hfix := (ggQ2_fixed_lin M).2
  have hnorm : ∀ g ∈ M.linGroup, g M.yV ∈ Submodule.span (ZMod 3) {M.yV} →
      ∃ (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod 3) (c : ZMod 3),
        ∃ w ∈ M.toLin.parab {k | k ≠ M.b}, ∀ i : {k // k ≠ M.b},
          g (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
    intro g hg hgy
    rw [GGQTwoModel.linGroup, Subgroup.mem_map] at hg
    obtain ⟨φ', hφ', rfl⟩ := hg
    have hleaf : ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0 := by
      rw [he0]
      exact ggQ2_uniqueNbr_of_equiv M.cartan (CartanMatrix.E 7) e hecart 0
        ⟨2, by decide, fun j hj =>
          (by decide : ∀ j : Fin 7, j ≠ 0 ∧ CartanMatrix.E 7 0 j ≠ 0 → j = 2) j hj⟩
    obtain ⟨π, μ, c, -, -, -, w, hw, h⟩ := ggQ2_tbwNorm_at_b hLB hP h5 hS rfl hnb hK1 M hleaf
      (hbas.1.comp _ Subtype.val_injective) M.yV hfix hnot hφ' hgy
    exact ⟨π, μ, c, w, hw, h⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : M.V ≃ₗ[ZMod 3] M.V, Φ = ggLin (p := 3) M.model φ := ⟨_, rfl⟩
  have hΦA : Φ ∈ M.linGroup := by
    rw [hΦ, GGQTwoModel.linGroup]
    exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  rw [← hΦ] at hT hφy
  have hww : w ∈ M.toLin.weyl := Subgroup.closure_mono (Set.image_mono (Set.subset_univ _)) hw
  have hwA : w ∈ M.linGroup := ggQ2_weyl_le_lin M hww
  have hΨA : w⁻¹ * Φ ∈ M.linGroup := M.linGroup.mul_mem (M.linGroup.inv_mem hwA) hΦA
  have hinv : ∀ v, w⁻¹ (w v) = v := fun v => w.symm_apply_apply v
  obtain ⟨t, htΦ⟩ := Submodule.mem_span_singleton.mp hφy
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hy0
    apply Φ.injective
    rw [← htΦ, zero_smul, map_zero]
  have hwy : w⁻¹ M.yV = M.yV :=
    (hfix M.yV).mpr (Submodule.mem_span_singleton_self _) w⁻¹ (Subgroup.inv_mem _ hw)
  have hΨy : (w⁻¹ * Φ) M.yV = t • M.yV := by
    show w⁻¹ (Φ M.yV) = _
    rw [← htΦ, map_smul, hwy]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hT (σ 0)
    rw [zero_smul] at h1
    have h2 : M.coroot (σ 0 : M.ι) = 0 := Φ.injective (h1.trans (map_zero Φ).symm)
    have h3 := M.toLin.root_coroot_self (σ 0 : M.ι)
    have h5 : M.toLin.root (σ 0 : M.ι) (M.toLin.coroot (σ 0 : M.ι)) =
        M.toLin.root (σ 0 : M.ι) 0 := congrArg (M.toLin.root (σ 0 : M.ι)) h2
    exact ggQ2g_E7_two_ne' (h3.symm.trans (h5.trans (LinearMap.map_zero _)))
  have hs0 : c * μ' ⟨0, by norm_num⟩ ≠ 0 := mul_ne_zero hc0 (hμ'0 _)
  have hs : c * μ' ⟨0, by norm_num⟩ = 1 ∨ c * μ' ⟨0, by norm_num⟩ = 2 :=
    ggQ2g_E7_scalar _ hs0
  have ht : t = 1 ∨ t = 2 := ggQ2g_E7_scalar t ht0
  have ha4 : (⟨M.a, M.a_ne_b⟩ : {k // k ≠ M.b}) = σ 4 :=
    Subtype.ext (by
      show M.a = (σ 4 : M.ι)
      rw [hσ 4, hea]
      rfl)
  have hπ'ne : π' ≠ 1 := fun h1 => hπa (by rw [ha4, hπσ, h1, Equiv.Perm.one_apply])
  have hπ' : π' = Equiv.swap (⟨6 - 2, by omega⟩ : Fin 6) ⟨6 - 1, by omega⟩ :=
    hπc.resolve_left hπ'ne
  have hπτ : ∀ i : Fin 6,
      (![6, 5, 4, 3, 1, 2] : Fin 6 → Fin 7)
        (Equiv.swap (⟨6 - 2, by omega⟩ : Fin 6) ⟨6 - 1, by omega⟩ i) =
      ggg7_tau ((![6, 5, 4, 3, 1, 2] : Fin 6 → Fin 7) i) := by
    decide
  have hΨσ : ∀ i : Fin 6, (w⁻¹ * Φ) (M.coroot (σ i : M.ι)) =
      (c * μ' ⟨0, by norm_num⟩) • M.coroot (σ (π' i) : M.ι) := by
    intro i
    have h1 := hT (σ i)
    rw [hπσ i, hμσ i, hμc i] at h1
    show w⁻¹ (Φ (M.coroot (σ i : M.ι))) = _
    rw [h1, map_smul, map_smul, hinv, smul_smul]
  have hτs : ∀ t : Fin 7, t ≠ 0 → ∃ j : Fin 6, (![6, 5, 4, 3, 1, 2] : Fin 6 → Fin 7) j = t := by
    decide
  refine ggQ2g_E7_false M.toLin e hecart hbas M.linGroup (ggQ2_weyl_le_lin M) M.yV M.b he0 hV hfix
    hnorm (w⁻¹ * Φ) hΨA _ t hs ht hΨy ?_
  intro j hj
  obtain ⟨i, hi⟩ := hτs j hj
  have hσi : (σ i : M.ι) = e j := by rw [hσ i, hi]
  have hσπ : (σ (π' i) : M.ι) = e (ggg7_tau j) := by
    rw [hσ, hπ', hπτ i, hi]
  show (w⁻¹ * Φ) (M.coroot (e j)) = (c * μ' ⟨0, by norm_num⟩) • M.coroot (e (ggg7_tau j))
  rw [← hσi, hΨσ i, hσπ]

