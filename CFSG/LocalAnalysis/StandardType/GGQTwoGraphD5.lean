module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphD5Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormModelA
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem ggQ2g_D5_two_ne : ((4 : ℤ) : ZMod 3) ≠ 0 := by decide

private theorem ggQ2g_D5_two_ne' : (2 : ZMod 3) ≠ 0 := by decide

private theorem ggQ2g_D5_scalar (s : ZMod 3) (h : s ≠ 0) : s = 1 ∨ s = 2 := by
  revert s
  decide

private theorem ggQ2g_D5_shift (i j : Fin 4) :
    CartanMatrix.D 5 i.succ j.succ = CartanMatrix.D 4 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggQ2g_D5_swap (i j : Fin 5) :
    CartanMatrix.D 5 (Equiv.swap (3 : Fin 5) 4 i) (Equiv.swap (3 : Fin 5) 4 j) =
      CartanMatrix.D 5 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggQ2g_D5_perm : ∀ q : Equiv.Perm (Fin 4), q 1 = 1 → q 0 ≠ 0 → q 2 ≠ 2 →
    (∀ i, q i = (![2, 1, 0, 3] : Fin 4 → Fin 4) i) ∨
      (∀ i, q i = (![2, 1, 3, 0] : Fin 4 → Fin 4) i) ∨
        (∀ i, q i = (![3, 1, 0, 2] : Fin 4 → Fin 4) i) := by
  decide

private theorem ggQ2g_D5_core (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G}
    {K : Subgroup G} (M : GGQTwoModel 3 Bs x y D L J K)
    (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.b = e 0)
    (hea : M.a = e 3)
    (hV : Submodule.span (ZMod 3)
      (insert M.yV (Set.range fun i : {k // k ≠ M.b} => M.coroot i)) = ⊤)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφy : ggLin (p := 3) M.model φ M.yV ∈ Submodule.span (ZMod 3) {M.yV})
    (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod 3) (c : ZMod 3)
    (w : M.V ≃ₗ[ZMod 3] M.V) (hSc : M.toLin.ScaledAut M.b π μ)
    (hw : w ∈ M.toLin.parab {k | k ≠ M.b})
    (hT : ∀ i : {k // k ≠ M.b},
      ggLin (p := 3) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    (hπa : π ⟨M.a, M.a_ne_b⟩ ≠ ⟨M.a, M.a_ne_b⟩)
    (hπ1 : ∀ i : {k // k ≠ M.b}, (i : M.ι) = e 1 → ((π i : {k // k ≠ M.b}) : M.ι) ≠ e 1) :
    False := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 4 ≃ {i // i ≠ M.b}, ∀ j, (σ j : M.ι) = e j.succ := by
    refine ⟨Equiv.ofBijective
      (fun j => ⟨e j.succ, fun h => Fin.succ_ne_zero j (e.injective (h.trans he0))⟩) ⟨?_, ?_⟩,
      fun j => rfl⟩
    · intro a b hab
      exact Fin.succ_injective _ (e.injective (Subtype.ext_iff.mp hab))
    · rintro ⟨i, hi⟩
      obtain ⟨t, rfl⟩ := e.surjective i
      have ht : t ≠ 0 := fun h => hi (by rw [he0, h])
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr ht
      exact ⟨j, rfl⟩
  have hσc : ∀ i j, M.cartan (σ i : M.ι) (σ j : M.ι) = CartanMatrix.D 4 i j := by
    intro i j
    rw [hσ i, hσ j, hecart]
    exact ggQ2g_D5_shift i j
  obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport M.toLin M.b σ hσc hSc
  have hπσ : ∀ i, π (σ i) = σ (π' i) := fun i => hπσ₀ i
  have hμσ : ∀ i, μ (σ i) = μ' i := fun i => hμσ₀ i
  obtain ⟨hμc, hπ1'⟩ := ggQ2g_scaledD4 π' μ' hμ'0 hrel
  have hπ'2 : π' 2 ≠ 2 := by
    intro h2
    apply hπa
    have hja : (⟨M.a, M.a_ne_b⟩ : {k // k ≠ M.b}) = σ 2 :=
      Subtype.ext (by rw [hσ 2]; exact hea)
    rw [hja, hπσ, h2]
  have hπ'0 : π' 0 ≠ 0 := by
    intro h0
    apply hπ1 (σ 0) (by rw [hσ 0]; rfl)
    rw [hπσ, h0, hσ 0]
    rfl
  have hM : M.cartan = (CartanMatrix.D 5).submatrix e.symm e.symm := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [← hecart (e.symm i) (e.symm j)]
    simp
  have hdet : ((M.toLin.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
    show ((M.cartan.det : ℤ) : ZMod 3) ≠ 0
    rw [hM, Matrix.det_submatrix_equiv_self, CartanMatrix.D_det (by norm_num)]
    exact ggQ2g_D5_two_ne
  have hbas : M.toLin.Basis := ggQ2g_basis M.toLin M.b M.yV hdet hV
  have hnot := ggQ2g_y_not_mem M.toLin M.b M.yV hbas hV
  have hy0 : M.yV ≠ 0 := fun h => hnot (by rw [h]; exact Submodule.zero_mem _)
  have hfixy := (ggQ2_fixed_lin M).2
  have hfixx := (ggQ2_fixed_lin M).1
  have hnorm : ∀ u : M.V,
      (∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u}) →
      u ∉ Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) →
      ∀ g ∈ M.linGroup, g u ∈ Submodule.span (ZMod 3) {u} →
        ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod 3) (c : ZMod 3),
          ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
            g (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
    intro u hfix hnotu g hg hgu
    rw [GGQTwoModel.linGroup, Subgroup.mem_map] at hg
    obtain ⟨φ', hφ', rfl⟩ := hg
    obtain ⟨π, μ, c, -, -, -, w, hw, h⟩ := ggQ2_tbwNorm_at_a hLB hP h5 hS rfl M
      (hbas.1.comp _ Subtype.val_injective) u hfix hnotu hφ' hgu
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
    (hfixy M.yV).mpr (Submodule.mem_span_singleton_self _) w⁻¹ (Subgroup.inv_mem _ hw)
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
    exact ggQ2g_D5_two_ne' (h3.symm.trans (h5.trans (LinearMap.map_zero _)))
  have hs0 : c * μ' 0 ≠ 0 := mul_ne_zero hc0 (hμ'0 _)
  have hs : c * μ' 0 = 1 ∨ c * μ' 0 = 2 := ggQ2g_D5_scalar _ hs0
  have ht : t = 1 ∨ t = 2 := ggQ2g_D5_scalar t ht0
  have hΨσ : ∀ i : Fin 4, (w⁻¹ * Φ) (M.coroot (σ i : M.ι)) =
      (c * μ' 0) • M.coroot (σ (π' i) : M.ι) := by
    intro i
    have h1 := hT (σ i)
    rw [hπσ i, hμσ i, hμc i] at h1
    show w⁻¹ (Φ (M.coroot (σ i : M.ι))) = _
    rw [h1, map_smul, map_smul, hinv, smul_smul]
  have hΨc_of : ∀ g : Fin 5 → Fin 5, (∀ i : Fin 4, g i.succ = (π' i).succ) →
      ∀ j : Fin 5, j ≠ 0 → (w⁻¹ * Φ) (M.coroot (e j)) = (c * μ' 0) • M.coroot (e (g j)) := by
    intro g hg j hj
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hj
    have h1 := hΨσ i
    rw [hσ i, hσ (π' i)] at h1
    rw [hg i]
    exact h1
  have main : ∀ g gi : Fin 5 → Fin 5, ggg5_pair g gi →
      (∀ j : Fin 5, j ≠ 0 →
        (w⁻¹ * Φ) (M.coroot (e j)) = (c * μ' 0) • M.coroot (e (g j))) → False := by
    intro g gi hg hΨc
    exact ggQ2g_D5_false M.toLin e hecart hbas M.linGroup (ggQ2_weyl_le_lin M) M.yV M.xV M.b M.a
      he0 hea hV hfixy hfixx hnorm (w⁻¹ * Φ) hΨA (c * μ' 0) t hs ht g gi hg hΨy hΨc
  rcases ggQ2g_D5_perm π' hπ1' hπ'0 hπ'2 with hq | hq | hq
  · exact main ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (Or.inl ⟨rfl, rfl⟩)
      (hΨc_of _ fun i => by rw [hq i]; revert i; decide)
  · exact main ![0, 3, 2, 4, 1] ![0, 4, 2, 1, 3] (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (hΨc_of _ fun i => by rw [hq i]; revert i; decide)
  · exact main ![0, 4, 2, 1, 3] ![0, 3, 2, 4, 1] (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (hΨc_of _ fun i => by rw [hq i]; revert i; decide)

theorem ggQ2_gammaNbrGraphD5_false (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) [Fact p.Prime] {y : G} {K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.b = e 0)
    (hea : M.a = e 3 ∨ M.a = e 4)
    (hV : Submodule.span (ZMod p)
      (insert M.yV (Set.range fun i : {k // k ≠ M.b} => M.coroot i)) = ⊤)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφy : ggLin (p := p) M.model φ M.yV ∈ Submodule.span (ZMod p) {M.yV})
    (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod p) (c : ZMod p)
    (w : M.V ≃ₗ[ZMod p] M.V) (hSc : M.toLin.ScaledAut M.b π μ)
    (hw : w ∈ M.toLin.parab {k | k ≠ M.b})
    (hT : ∀ i : {k // k ≠ M.b},
      ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    (hπa : π ⟨M.a, M.a_ne_b⟩ ≠ ⟨M.a, M.a_ne_b⟩)
    (hπ1 : ∀ i : {k // k ≠ M.b}, (i : M.ι) = e 1 → ((π i : {k // k ≠ M.b}) : M.ι) ≠ e 1) :
    False := by
  subst hp
  rcases hea with hea | hea
  · exact ggQ2g_D5_core hLB hP h5 hS M e hecart he0 hea hV hφ hφy π μ c w hSc hw hT hπa hπ1
  ·
    refine ggQ2g_D5_core hLB hP h5 hS M ((Equiv.swap (3 : Fin 5) 4).trans e) (fun i j => ?_) ?_
      ?_ hV hφ hφy π μ c w hSc hw hT hπa ?_
    · rw [Equiv.trans_apply, Equiv.trans_apply, hecart]
      exact ggQ2g_D5_swap i j
    · show M.b = e (Equiv.swap (3 : Fin 5) 4 0)
      rw [he0, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    · rw [hea, Equiv.trans_apply, Equiv.swap_apply_left]
    · intro i hi
      rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at hi ⊢
      exact hπ1 i hi

end CFSG.StandardType

end
