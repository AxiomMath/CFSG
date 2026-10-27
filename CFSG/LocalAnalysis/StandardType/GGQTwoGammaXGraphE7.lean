module

public import CFSG.LinearAlgebra.F3ConnectedPairingScalar
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXRes
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormModelA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2GammaXGraphE7Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ∀ M : GGQTwoModel p Bs x y D L J K, ∀ e : Fin 7 ≃ M.ι,
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.E 7 i j) → M.a = e 0 →
      Submodule.span (ZMod p) (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV} →
      ∀ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p)
        (w : M.V ≃ₗ[ZMod p] M.V),
        M.toLin.ScaledAut M.a π μ → w ∈ M.toLin.parab {k | k ≠ M.a} →
        (∀ i : {k // k ≠ M.a},
          ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i))) →
        π ⟨M.b, M.a_ne_b.symm⟩ ≠ ⟨M.b, M.a_ne_b.symm⟩ →
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs

theorem ggQ2_gammaXGraphE7_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaXGraphE7Input := by
  have htwo_ne : ((2 : ℤ) : ZMod 3) ≠ 0 := by decide
  have hneg : (-1 : ZMod 3) = 2 := by decide
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ y K hnb M e hecart he0 hV φ hφ hφxV π μ c w
    hSc hw hT hπb
  subst hp
  classical
  exfalso
  obtain ⟨σ, hσ, hσc⟩ := ggQ2g_E7_sigma M.cartan e M.a he0 hecart
  obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport M.toLin M.a σ hσc hSc
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
    exact htwo_ne
  have hbas : M.toLin.Basis := ggQ2g_basis M.toLin M.a M.xV hdet hV
  have hnot := ggQ2g_y_not_mem M.toLin M.a M.xV hbas hV
  have hx0 : M.xV ≠ 0 := fun h => hnot (by rw [h]; exact Submodule.zero_mem _)
  have hfix := (ggQ2_fixed_lin M).1
  have hnorm : ∀ g ∈ M.linGroup, g M.xV ∈ Submodule.span (ZMod 3) {M.xV} →
      ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod 3) (c : ZMod 3),
        ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
          g (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
    intro g hg hgx
    rw [GGQTwoModel.linGroup, Subgroup.mem_map] at hg
    obtain ⟨φ', hφ', rfl⟩ := hg
    obtain ⟨π, μ, c, -, -, -, w, hw, h⟩ := ggQ2_tbwNorm_at_a hLB hP h5 hS rfl M
      (hbas.1.comp _ Subtype.val_injective) M.xV hfix hnot hφ' hgx
    exact ⟨π, μ, c, w, hw, h⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : M.V ≃ₗ[ZMod 3] M.V, Φ = ggLin (p := 3) M.model φ := ⟨_, rfl⟩
  have hΦA : Φ ∈ M.linGroup := by
    rw [hΦ, GGQTwoModel.linGroup]
    exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  rw [← hΦ] at hT hφxV
  have hww : w ∈ M.toLin.weyl := Subgroup.closure_mono (Set.image_mono (Set.subset_univ _)) hw
  have hwA : w ∈ M.linGroup := ggQ2_weyl_le_lin M hww
  have hΨA : w⁻¹ * Φ ∈ M.linGroup := M.linGroup.mul_mem (M.linGroup.inv_mem hwA) hΦA
  have hinv : ∀ v, w⁻¹ (w v) = v := fun v => w.symm_apply_apply v
  obtain ⟨t, htΦ⟩ := Submodule.mem_span_singleton.mp hφxV
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hx0
    apply Φ.injective
    rw [← htΦ, zero_smul, map_zero]
  have hwy : w⁻¹ M.xV = M.xV :=
    (hfix M.xV).mpr (Submodule.mem_span_singleton_self _) w⁻¹ (Subgroup.inv_mem _ hw)
  have hΨx : (w⁻¹ * Φ) M.xV = t • M.xV := by
    show w⁻¹ (Φ M.xV) = _
    rw [← htΦ, map_smul, hwy]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hT (σ 0)
    rw [zero_smul] at h1
    have h2 : M.coroot (σ 0 : M.ι) = 0 := Φ.injective (h1.trans (map_zero Φ).symm)
    have h3 := M.toLin.root_coroot_self (σ 0 : M.ι)
    have h5 : M.toLin.root (σ 0 : M.ι) (M.toLin.coroot (σ 0 : M.ι)) =
        M.toLin.root (σ 0 : M.ι) 0 := congrArg (M.toLin.root (σ 0 : M.ι)) h2
    exact QTwoLin.two_ne_zero_of_charP_three (h3.symm.trans (h5.trans (LinearMap.map_zero _)))
  have hscalar : ∀ s : ZMod 3, s ≠ 0 → s = 1 ∨ s = 2 := by
    intro s hs
    rcases CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one s hs with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact hneg)
  have hs0 : c * μ' ⟨0, by norm_num⟩ ≠ 0 := mul_ne_zero hc0 (hμ'0 _)
  have hs : c * μ' ⟨0, by norm_num⟩ = 1 ∨ c * μ' ⟨0, by norm_num⟩ = 2 := hscalar _ hs0
  have ht : t = 1 ∨ t = 2 := hscalar t ht0
  obtain ⟨i, hi⟩ := σ.surjective ⟨M.b, M.a_ne_b.symm⟩
  have hπ'ne : π' ≠ 1 := by
    intro h1
    exact hπb (by rw [← hi, hπσ i, h1, Equiv.Perm.one_apply])
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
  refine ggQ2g_E7_false M.toLin e hecart hbas M.linGroup (ggQ2_weyl_le_lin M) M.xV M.a he0 hV
    hfix hnorm (w⁻¹ * Φ) hΨA _ t hs ht hΨx ?_
  intro j hj
  obtain ⟨i, hi⟩ := hτs j hj
  have hσi : (σ i : M.ι) = e j := by rw [hσ i, hi]
  have hσπ : (σ (π' i) : M.ι) = e (ggg7_tau j) := by
    rw [hσ, hπ', hπτ i, hi]
  show (w⁻¹ * Φ) (M.coroot (e j)) = (c * μ' ⟨0, by norm_num⟩) • M.coroot (e (ggg7_tau j))
  rw [← hσi, hΨσ i, hσπ]

end CFSG.StandardType

end
