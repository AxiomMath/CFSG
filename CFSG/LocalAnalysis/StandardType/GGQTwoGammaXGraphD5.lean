module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphD5Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXRes
import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7Lin
import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormModelA
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2GammaXGraphD5Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ∀ M : GGQTwoModel p Bs x y D L J K, ∀ e : Fin 5 ≃ M.ι,
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) → M.a = e 0 →
      Submodule.span (ZMod p) (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV} →
      ∀ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p)
        (w : M.V ≃ₗ[ZMod p] M.V),
        M.toLin.ScaledAut M.a π μ → w ∈ M.toLin.parab {k | k ≠ M.a} →
        (∀ i : {k // k ≠ M.a},
          ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i))) →
        π ⟨M.b, M.a_ne_b.symm⟩ ≠ ⟨M.b, M.a_ne_b.symm⟩ →
        (∀ i : {k // k ≠ M.a}, (i : M.ι) = e 1 → ((π i : {k // k ≠ M.a}) : M.ι) ≠ e 1) →
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs

private theorem ggQ2gx_D5_transport {G : Type} [Group G]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel 3 Bs x y D L J K)
    (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod 3)
    (hSc : M.toLin.ScaledAut M.a π μ) :
    ∃ (σ : Fin 4 ≃ {i // i ≠ M.a}) (π' : Equiv.Perm (Fin 4)) (μ' : Fin 4 → ZMod 3),
      (∀ j, (σ j : M.ι) = e j.succ) ∧ (∀ i, π (σ i) = σ (π' i)) ∧ (∀ i, μ (σ i) = μ' i) ∧
        (∀ i, μ' i ≠ 0) ∧ (∀ i, μ' i = μ' 0) ∧ π' 1 = 1 := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 4 ≃ {i // i ≠ M.a}, ∀ j, (σ j : M.ι) = e j.succ := by
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
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨π', μ', hμ'0, hrel, hπσ, hμσ⟩ := ggQ2g_transport M.toLin M.a σ hσc hSc
  obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD4 π' μ' hμ'0 hrel
  exact ⟨σ, π', μ', hσ, hπσ, hμσ, hμ'0, hμc, hπc⟩

private theorem ggQ2gx_D5_twist {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel 3 Bs x y D L J K)
    (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j)
    (hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV})
    {π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}} {μ : {k // k ≠ M.a} → ZMod 3} {c : ZMod 3}
    {w : M.V ≃ₗ[ZMod 3] M.V}
    (hw : w ∈ M.toLin.parab {k | k ≠ M.a})
    (hT : ∀ i : {k // k ≠ M.a},
      ggLin (p := 3) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    {σ : Fin 4 ≃ {i // i ≠ M.a}} (hσ : ∀ j, (σ j : M.ι) = e j.succ)
    {π' : Equiv.Perm (Fin 4)} {μ' : Fin 4 → ZMod 3}
    (hπσ : ∀ i, π (σ i) = σ (π' i)) (hμσ : ∀ i, μ (σ i) = μ' i) (hμ'0 : ∀ i, μ' i ≠ 0)
    (hμc : ∀ i, μ' i = μ' 0) (hπc : π' 1 = 1) (hπ'0 : π' 0 ≠ 0) (hπ'2 : π' 2 ≠ 2) :
    M.toLin.Basis ∧ ∃ Ψ ∈ M.linGroup, ∃ s t : ZMod 3, (s = 1 ∨ s = 2) ∧ (t = 1 ∨ t = 2) ∧
      ∃ g gi : Fin 5 → Fin 5, ggg5_pair g gi ∧ Ψ M.xV = t • M.xV ∧
        ∀ j : Fin 5, j ≠ 0 → Ψ (M.coroot (e j)) = s • M.coroot (e (g j)) := by
  classical
  have hM : M.cartan = (CartanMatrix.D 5).submatrix e.symm e.symm := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [← hecart (e.symm i) (e.symm j)]
    simp
  have hdet : ((M.toLin.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
    show ((M.cartan.det : ℤ) : ZMod 3) ≠ 0
    rw [hM, Matrix.det_submatrix_equiv_self]
    decide +kernel
  have hbas : M.toLin.Basis := ggQ2g_basis M.toLin M.a M.xV hdet hV
  have hnot := ggQ2g_y_not_mem M.toLin M.a M.xV hbas hV
  have hx0 : M.xV ≠ 0 := fun h => hnot (by rw [h]; exact Submodule.zero_mem _)
  have hfixa := (ggQ2_fixed_lin M).1
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : M.V ≃ₗ[ZMod 3] M.V, Φ = ggLin (p := 3) M.model φ := ⟨_, rfl⟩
  have hΦA : Φ ∈ M.linGroup := by
    rw [hΦ, GGQTwoModel.linGroup]
    exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  rw [← hΦ] at hT hφx
  have hww : w ∈ M.toLin.weyl := Subgroup.closure_mono (Set.image_mono (Set.subset_univ _)) hw
  have hwA : w ∈ M.linGroup := ggQ2_weyl_le_lin M hww
  have hΨA : w⁻¹ * Φ ∈ M.linGroup := M.linGroup.mul_mem (M.linGroup.inv_mem hwA) hΦA
  have hinv : ∀ v, w⁻¹ (w v) = v := fun v => w.symm_apply_apply v
  obtain ⟨t, htΦ⟩ := Submodule.mem_span_singleton.mp hφx
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hx0
    apply Φ.injective
    rw [← htΦ, zero_smul, map_zero]
  have hwx : w⁻¹ M.xV = M.xV :=
    (hfixa M.xV).mpr (Submodule.mem_span_singleton_self _) w⁻¹ (Subgroup.inv_mem _ hw)
  have hΨx : (w⁻¹ * Φ) M.xV = t • M.xV := by
    show w⁻¹ (Φ M.xV) = _
    rw [← htΦ, map_smul, hwx]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hT (σ 0)
    rw [zero_smul] at h1
    have h2 : M.coroot (σ 0 : M.ι) = 0 := Φ.injective (h1.trans (map_zero Φ).symm)
    have h3 := M.toLin.root_coroot_self (σ 0 : M.ι)
    have h5 : M.toLin.root (σ 0 : M.ι) (M.toLin.coroot (σ 0 : M.ι)) =
        M.toLin.root (σ 0 : M.ι) 0 := congrArg (M.toLin.root (σ 0 : M.ι)) h2
    exact (by decide : (2 : ZMod 3) ≠ 0) (h3.symm.trans (h5.trans (LinearMap.map_zero _)))
  have hscalar : ∀ s : ZMod 3, s ≠ 0 → s = 1 ∨ s = 2 := by decide
  have hs0 : c * μ' 0 ≠ 0 := mul_ne_zero hc0 (hμ'0 0)
  have hs : c * μ' 0 = 1 ∨ c * μ' 0 = 2 := hscalar _ hs0
  have ht : t = 1 ∨ t = 2 := hscalar t ht0
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
  have hperm : ∀ q : Equiv.Perm (Fin 4), q 1 = 1 → q 0 ≠ 0 → q 2 ≠ 2 →
      (∀ i, q i = (![2, 1, 0, 3] : Fin 4 → Fin 4) i) ∨
        (∀ i, q i = (![2, 1, 3, 0] : Fin 4 → Fin 4) i) ∨
          (∀ i, q i = (![3, 1, 0, 2] : Fin 4 → Fin 4) i) := by
    decide
  refine ⟨hbas, w⁻¹ * Φ, hΨA, c * μ' 0, t, hs, ht, ?_⟩
  rcases hperm π' hπc hπ'0 hπ'2 with hq | hq | hq
  · exact ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], Or.inl ⟨rfl, rfl⟩, hΨx,
      hΨc_of _ fun i => by rw [hq i]; revert i; decide⟩
  · exact ⟨![0, 3, 2, 4, 1], ![0, 4, 2, 1, 3], Or.inr (Or.inl ⟨rfl, rfl⟩), hΨx,
      hΨc_of _ fun i => by rw [hq i]; revert i; decide⟩
  · exact ⟨![0, 4, 2, 1, 3], ![0, 3, 2, 4, 1], Or.inr (Or.inr ⟨rfl, rfl⟩), hΨx,
      hΨc_of _ fun i => by rw [hq i]; revert i; decide⟩

private theorem ggQ2gx_D5_cell (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) (hK1 : GGQTwoK1 3 B Bs x D J)
    (M : GGQTwoModel 3 Bs x y D L J K)
    (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hb : M.b = e 3 ∨ M.b = e 1)
    (hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV})
    {π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}} {μ : {k // k ≠ M.a} → ZMod 3} {c : ZMod 3}
    {w : M.V ≃ₗ[ZMod 3] M.V}
    (hw : w ∈ M.toLin.parab {k | k ≠ M.a})
    (hT : ∀ i : {k // k ≠ M.a},
      ggLin (p := 3) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    {σ : Fin 4 ≃ {i // i ≠ M.a}} (hσ : ∀ j, (σ j : M.ι) = e j.succ)
    {π' : Equiv.Perm (Fin 4)} {μ' : Fin 4 → ZMod 3}
    (hπσ : ∀ i, π (σ i) = σ (π' i)) (hμσ : ∀ i, μ (σ i) = μ' i) (hμ'0 : ∀ i, μ' i ≠ 0)
    (hμc : ∀ i, μ' i = μ' 0) (hπc : π' 1 = 1) (hπ'0 : π' 0 ≠ 0) (hπ'2 : π' 2 ≠ 2) :
    False := by
  obtain ⟨hbas, Ψ, hΨ, s, t, hs, ht, g, gi, hg, hΨx, hΨc⟩ :=
    ggQ2gx_D5_twist M e hecart hV hφ hφx hw hT hσ hπσ hμσ hμ'0 hμc hπc hπ'0 hπ'2
  rcases hb with hb | hb
  ·
    have hleaf : ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0 := by
      rw [hb]
      exact ggQ2_uniqueNbr_of_equiv M.cartan (CartanMatrix.D 5) e hecart 3
        ⟨2, by decide, fun j hj =>
          (by decide : ∀ j : Fin 5, j ≠ 3 ∧ CartanMatrix.D 5 3 j ≠ 0 → j = 2) j hj⟩
    have hnorm : ∀ u : M.V,
        (∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.b}, g v = v) ↔
          v ∈ Submodule.span (ZMod 3) {u}) →
        u ∉ Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ M.b} => M.coroot i) →
        ∀ g ∈ M.linGroup, g u ∈ Submodule.span (ZMod 3) {u} →
          ∃ (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod 3) (c : ZMod 3),
            ∃ w ∈ M.toLin.parab {k | k ≠ M.b}, ∀ i : {k // k ≠ M.b},
              g (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
      intro u hfix hnotu g hg hgu
      rw [GGQTwoModel.linGroup, Subgroup.mem_map] at hg
      obtain ⟨φ', hφ', rfl⟩ := hg
      obtain ⟨π, μ, c, -, -, -, w, hw, h⟩ := ggQ2_tbwNorm_at_b hLB hP h5 hS rfl hnb hK1 M hleaf
        (hbas.1.comp _ Subtype.val_injective) u hfix hnotu hφ' hgu
      exact ⟨π, μ, c, w, hw, h⟩
    exact ggQ2g_D5_false M.toLin e hecart hbas M.linGroup (ggQ2_weyl_le_lin M) M.xV M.yV
      M.a M.b he0 hb hV (ggQ2_fixed_lin M).1 (ggQ2_fixed_lin M).2 hnorm Ψ hΨ s t hs ht g gi hg
      hΨx hΨc
  ·
    exact ggQ2gx_D5_one_false M.toLin e hecart hbas M.linGroup (ggQ2_weyl_le_lin M) M.xV M.yV
      M.a M.b he0 hb hV (ggQ2_fixed_lin M).1 (ggQ2_fixed_lin M).2
      (fun g hg hgy => ggQ2_linNbrLineStab_normalizes hLB hP h5 hS hnb hK1 M hg hgy)
      Ψ hΨ s t hs ht g gi hg hΨx hΨc

theorem ggQ2_gammaXGraphD5_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaXGraphD5Input := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ y K hnb M e hecart he0 hV φ hφ hφx π μ c w
    hSc hw hT hπb hπ1
  subst hp
  classical
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  exfalso
  obtain ⟨j, hj, hj0⟩ : ∃ j : Fin 5, M.b = e j ∧ j ≠ 0 := by
    obtain ⟨j, hj⟩ := e.surjective M.b
    exact ⟨j, hj.symm, fun h => M.a_ne_b (by rw [he0, ← h]; exact hj)⟩
  obtain ⟨σ, π', μ', hσ, hπσ, hμσ, hμ'0, hμc, hπc⟩ :=
    ggQ2gx_D5_transport M e hecart he0 π μ hSc
  have hσ0 : (σ 0 : M.ι) = e 1 := hσ 0
  have hσ1 : (σ 1 : M.ι) = e 2 := hσ 1
  have hσ2 : (σ 2 : M.ι) = e 3 := hσ 2
  have hσ3 : (σ 3 : M.ι) = e 4 := hσ 3
  have hπ'0 : π' 0 ≠ 0 := by
    intro h0
    exact hπ1 (σ 0) hσ0 (by rw [hπσ 0, h0]; exact hσ0)
  set e' : Fin 5 ≃ M.ι := (Equiv.swap (3 : Fin 5) 4).trans e with he'
  have hecart' : ∀ i j, M.cartan (e' i) (e' j) = CartanMatrix.D 5 i j := by
    intro i j
    rw [he', Equiv.trans_apply, Equiv.trans_apply, hecart]
    fin_cases i <;> fin_cases j <;> decide
  have he0' : M.a = e' 0 := by
    rw [he', he0, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have he1' : e' 1 = e 1 := by
    rw [he', Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have he3' : e' 3 = e 4 := by
    rw [he', Equiv.trans_apply, Equiv.swap_apply_left]
  have he4' : e' 4 = e 3 := by
    rw [he', Equiv.trans_apply, Equiv.swap_apply_right]
  obtain ⟨σ', π'', μ'', hσ', hπ''σ', hμ''σ', hμ''0, hμ''c, hπ''c⟩ :=
    ggQ2gx_D5_transport M e' hecart' he0' π μ hSc
  have hπ''0 : π'' 0 ≠ 0 := by
    intro h0
    refine hπ1 (σ' 0) ((hσ' 0).trans he1') ?_
    rw [hπ''σ' 0, h0]
    exact (hσ' 0).trans he1'
  fin_cases j
  · exact hj0 rfl
  ·
    by_cases h2 : π' 2 = 2
    ·
      have hπ'3 : π' 3 ≠ 3 :=
        (by decide : ∀ q : Equiv.Perm (Fin 4), q 1 = 1 → q 0 ≠ 0 → q 2 = 2 → q 3 ≠ 3)
          π' hπc hπ'0 h2
      have hfix4 : π (σ 3) ≠ σ 3 := by
        intro h
        exact hπ'3 (σ.injective (by rw [← hπσ 3]; exact h))
      have hπ''2 : π'' 2 ≠ 2 := by
        intro h2'
        have h1 : π (σ' 2) = σ' 2 := by rw [hπ''σ' 2, h2']
        have hσ'2σ3 : σ' 2 = σ 3 := Subtype.ext ((hσ' 2).trans (he3'.trans hσ3.symm))
        rw [hσ'2σ3] at h1
        exact hfix4 h1
      have hb' : M.b = e' 1 := hj.trans he1'.symm
      exact ggQ2gx_D5_cell hLB hP h5 hS hnb hK1 M e' hecart' he0' (Or.inr hb') hV hφ hφx hw hT hσ'
        hπ''σ' hμ''σ' hμ''0 hμ''c hπ''c hπ''0 hπ''2
    · exact ggQ2gx_D5_cell hLB hP h5 hS hnb hK1 M e hecart he0 (Or.inr hj) hV hφ hφx hw hT hσ hπσ
        hμσ hμ'0 hμc hπc hπ'0 h2
  ·
    have hnode : (⟨M.b, M.a_ne_b.symm⟩ : {k // k ≠ M.a}) = σ 1 := by
      apply Subtype.ext
      show M.b = (σ 1 : M.ι)
      rw [hj]
      exact hσ1.symm
    exact hπb (by rw [hnode, hπσ 1, hπc])
  ·
    have hπ'2 : π' 2 ≠ 2 := by
      intro h2
      have hnode : (⟨M.b, M.a_ne_b.symm⟩ : {k // k ≠ M.a}) = σ 2 := by
        apply Subtype.ext
        show M.b = (σ 2 : M.ι)
        rw [hj]
        exact hσ2.symm
      exact hπb (by rw [hnode, hπσ 2, h2])
    exact ggQ2gx_D5_cell hLB hP h5 hS hnb hK1 M e hecart he0 (Or.inl hj) hV hφ hφx hw hT hσ hπσ
      hμσ hμ'0 hμc hπc hπ'0 hπ'2
  ·
    have hπ''2 : π'' 2 ≠ 2 := by
      intro h2
      have hnode : (⟨M.b, M.a_ne_b.symm⟩ : {k // k ≠ M.a}) = σ' 2 :=
        Subtype.ext (hj.trans (he3'.symm.trans (hσ' 2).symm))
      exact hπb (by rw [hnode, hπ''σ' 2, h2])
    have hb' : M.b = e' 3 := hj.trans he3'.symm
    exact ggQ2gx_D5_cell hLB hP h5 hS hnb hK1 M e' hecart' he0' (Or.inl hb') hV hφ hφx hw hT hσ'
      hπ''σ' hμ''σ' hμ''0 hμ''c hπ''c hπ''0 hπ''2

end CFSG.StandardType

end
