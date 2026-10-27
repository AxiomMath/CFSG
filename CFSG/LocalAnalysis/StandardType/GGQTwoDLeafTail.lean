module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphSwap
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphClassify
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphCommon
public import CFSG.LocalAnalysis.StandardType.GGQTwoScalarStable

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma lr7tl_neg_one : (-1 : ZMod 3) = 2 := by decide

private lemma lr7tl_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

private lemma lr7tl_scalar (D : GGQ2Lin 3) (xV : D.V)
    (hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0)
    (hV : Submodule.span (ZMod 3)
      (insert xV (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) = ⊤)
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} (hπ1 : ∀ i, π i = i)
    {T : D.V →ₗ[ZMod 3] D.V} {c : ZMod 3} {w : D.V ≃ₗ[ZMod 3] D.V}
    (hw : w ∈ D.parab {k | k ≠ D.a})
    (hT : ∀ i : {k // k ≠ D.a}, T (D.coroot i) = c • w (D.coroot (π i)))
    (hTx : T xV ∈ Submodule.span (ZMod 3) {xV}) :
    ∃ w' ∈ D.parab {k | k ≠ D.a}, ∀ z : D.V, ∀ v ∈ Submodule.span (ZMod 3) {xV, z},
      w' (T v) ∈ Submodule.span (ZMod 3) {xV, z} := by
  have hS : D.ScalarModW D.a π (fun _ => 1) := by
    refine ⟨1, Or.inl rfl, 1, (D.parab {k | k ≠ D.a}).one_mem, fun i => ?_⟩
    simp [hπ1 i]
  obtain ⟨w', hw', ε, hε⟩ :=
    ggQ2_scalarStable D xV hxα hV hS hw (T := T) (fun i => by simpa using hT i) hTx
  refine ⟨w', hw', fun z v hv => ?_⟩
  obtain ⟨s, hs⟩ := hε v
  rw [hs]
  have hx : xV ∈ Submodule.span (ZMod 3) ({xV, z} : Set D.V) := Submodule.subset_span (by simp)
  exact Submodule.add_mem _ (Submodule.smul_mem _ ε hv) (Submodule.smul_mem _ s hx)

theorem ggQ2_dLeaf_stablePlane (D : GGQ2Lin 3) (hbas : D.Basis) {k : ℕ} (hk : 3 ≤ k)
    (f : Fin (2 * k) ≃ {i // i ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) (xV : D.V) (hx0 : xV ≠ 0)
    (hfix : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {xV})
    (hV : Submodule.span (ZMod 3)
      (insert xV (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) = ⊤)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hWA : D.weyl ≤ A)
    (hnorm : ∀ g ∈ A, g xV ∈ Submodule.span (ZMod 3) {xV} →
      ∃ (π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}) (c : ZMod 3), c ≠ 0 ∧
        (∀ i j : {k // k ≠ D.a}, D.cartan (π i) (π j) = D.cartan i j) ∧
        ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : {k // k ≠ D.a},
          g (D.coroot i) = c • w (D.coroot (π i)))
    {T : D.V ≃ₗ[ZMod 3] D.V} (hT : T ∈ A) (hTx : T xV ∈ Submodule.span (ZMod 3) {xV}) :
    (∃ w' ∈ D.parab {k | k ≠ D.a}, ∀ z : D.V, ∀ v ∈ Submodule.span (ZMod 3) {xV, z},
        w' (T v) ∈ Submodule.span (ZMod 3) {xV, z}) ∨
    (∃ w' ∈ D.weyl, ∀ z : D.V, ∀ v ∈ Submodule.span (ZMod 3) {xV, z},
        w' (T v) ∈ Submodule.span (ZMod 3) {xV, z}) := by
  classical
  have hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0 :=
    ggQ2g_alpha_fixed rfl D D.a xV hfix
  obtain ⟨π, c, hc0, hπ, w, hw, hTw⟩ := hnorm T hT hTx
  have hScaled : D.ScaledAut D.a π (fun _ => 1) :=
    ⟨fun _ => lr7tl_one_ne_zero, fun i j => by simp [hπ i j]⟩
  let Tl : D.V →ₗ[ZMod 3] D.V := T.toLinearMap
  have hTwl : ∀ i : {k // k ≠ D.a}, Tl (D.coroot i) = c • w (D.coroot (π i)) :=
    fun i => by simpa [Tl] using hTw i
  have hTxl : Tl xV ∈ Submodule.span (ZMod 3) {xV} := by simpa [Tl] using hTx
  have hscalarFinish (hπ1 : ∀ i : {k // k ≠ D.a}, π i = i) :
      ∃ w' ∈ D.parab {k | k ≠ D.a}, ∀ z : D.V, ∀ v ∈ Submodule.span (ZMod 3) {xV, z},
        w' (T v) ∈ Submodule.span (ZMod 3) {xV, z} :=
    lr7tl_scalar D xV hxα hV hπ1 hw hTwl hTxl
  obtain ⟨c₀, hc₀a, hc₀l⟩ := ggQ2g_second_leaf D (by omega : 2 ≤ k) f hf
  rcases ggQ2g_classify D D.a c₀ hc₀a hc₀l (by omega : 2 ≤ k) f hf with
    ⟨e, hecart, hcox, he0, -⟩ | ⟨rfl, e, hecart, he0, -⟩
  ·
    let e' : Fin (2 * k + 1) ≃ D.ι := e
    have hecart' : ∀ i j : Fin (2 * k + 1),
        D.cartan (e' i) (e' j) = CartanMatrix.D (2 * k + 1) i j := hecart
    have hcox' : D.coxeter = (ggCoxeterMatrixD (2 * k + 1)).reindex e' := hcox
    have he0' : D.a = e' ⟨0, by omega⟩ := he0
    let σf : Fin (2 * k) → {i : D.ι // i ≠ D.a} := fun i =>
      ⟨e' i.succ, by
        rw [he0']
        intro h
        exact Fin.succ_ne_zero i (e'.injective h)⟩
    have hσf_bij : Function.Bijective σf := by
      constructor
      · intro a b hab
        have h1 : e' a.succ = e' b.succ := congrArg Subtype.val hab
        exact Fin.succ_injective (2 * k) (e'.injective h1)
      · rintro ⟨i, hi⟩
        obtain ⟨t, rfl⟩ := e'.surjective i
        have ht : t ≠ 0 := by
          intro h
          exact hi (by rw [h]; exact he0'.symm)
        obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero ht
        have hσfj : (σf j : D.ι) = e' j.succ := rfl
        exact ⟨j, Subtype.ext (by rw [hσfj, hj])⟩
    let σ : Fin (2 * k) ≃ {i : D.ι // i ≠ D.a} := Equiv.ofBijective σf hσf_bij
    have hσ : ∀ i j, D.cartan (σ i) (σ j) = CartanMatrix.D (2 * k) i j := by
      intro i j
      have h1 := hecart' i.succ j.succ
      change D.cartan (e' i.succ) (e' j.succ) = CartanMatrix.D (2 * k) i j
      rw [h1, ggQ2xa_D_succ_succ (by omega : 2 ≤ k) i j]
    obtain ⟨π', μ', hμ'0, hrel, hπσ, hμσ⟩ := ggQ2g_transport D D.a σ hσ hScaled
    obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD (2 * k) (by omega : 6 ≤ 2 * k) π' μ' hμ'0 hrel
    rcases hπc with hπ'1 | hπ'swap
    · exact Or.inl (hscalarFinish (fun i => by
        have h := hπσ (σ.symm i)
        rw [hπ'1] at h
        simpa using h))
    · right
      have hπσv : ∀ i, ((π (σ i) : {k // k ≠ D.a}) : D.ι) =
          ((σ (π' i) : {k // k ≠ D.a}) : D.ι) := fun i => congrArg Subtype.val (hπσ i)
      have hT' : ∀ i : D.ι, i ≠ D.a →
          Tl (D.coroot i) = c • (1 : ZMod 3) • w (D.coroot (Equiv.swap
            (e' ⟨2 * k + 1 - 2, by omega⟩) (e' ⟨2 * k + 1 - 1, by omega⟩) i)) := by
        intro i hi
        let j : Fin (2 * k) := σ.symm ⟨i, hi⟩
        have hj : (σ j : D.ι) = i := congrArg Subtype.val (σ.apply_symm_apply ⟨i, hi⟩)
        have h1 := hTwl (σ j)
        rw [hj] at h1
        simp only [hπσv j, hπ'swap] at h1
        have hσj : (σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
            ⟨2 * k - 1, by omega⟩ j) : D.ι) =
            Equiv.swap (e' ⟨2 * k + 1 - 2, by omega⟩)
              (e' ⟨2 * k + 1 - 1, by omega⟩) i := by
          have hsa : (⟨2 * k + 1 - 2, by omega⟩ : Fin (2 * k + 1)) =
              (⟨2 * k - 2, by omega⟩ : Fin (2 * k)).succ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega
          have hsb : (⟨2 * k + 1 - 1, by omega⟩ : Fin (2 * k + 1)) =
              (⟨2 * k - 1, by omega⟩ : Fin (2 * k)).succ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega
          rw [hsa, hsb]
          have hσa : (σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
              ⟨2 * k - 1, by omega⟩ j) : D.ι) =
              e' ((Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
                ⟨2 * k - 1, by omega⟩ j).succ) := rfl
          rw [hσa]
          rw [← Function.Injective.swap_apply (Fin.succ_injective (2 * k))
            (⟨2 * k - 2, by omega⟩) (⟨2 * k - 1, by omega⟩) j]
          rw [← show e' j.succ = i from hj]
          exact (Function.Injective.swap_apply e'.injective
            (⟨2 * k - 2, by omega⟩ : Fin (2 * k)).succ
            (⟨2 * k - 1, by omega⟩ : Fin (2 * k)).succ j.succ).symm
        rw [hσj] at h1
        simpa using h1
      obtain ⟨w', hw'weyl, hstab⟩ :=
        ggQ2g_swap_stable (p := 3) (by decide) D hbas (m := 2 * k + 1) (by omega)
          e' hcox' he0' xV hfix hV hw hT' hTxl
      exact ⟨w', hw'weyl, hstab⟩
  ·
    let e' : Fin 7 ≃ D.ι := e
    have hecart' : ∀ i j, D.cartan (e' i) (e' j) = CartanMatrix.E 7 i j := hecart
    have he0' : D.a = e' 0 := he0
    obtain ⟨σ, hσ, hσc⟩ := ggQ2g_E7_sigma D.cartan e' D.a he0' hecart'
    obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport D D.a σ hσc hScaled
    obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD 6 (by norm_num) π' μ' hμ'0 hrel
    rcases hπc with hπ'1 | hπ'swap
    · exact Or.inl (hscalarFinish (fun i => by
        have h := hπσ₀ (σ.symm i)
        rw [hπ'1] at h
        simpa using h))
    · exfalso
      have hπ' : π' = Equiv.swap (⟨6 - 2, by omega⟩ : Fin 6) ⟨6 - 1, by omega⟩ := hπ'swap
      have hparab_le_weyl : D.parab {k | k ≠ D.a} ≤ D.weyl :=
        Subgroup.closure_mono (Set.image_mono (Set.subset_univ _))
      have hwA : w ∈ A := hWA (hparab_le_weyl hw)
      have hΨA : w⁻¹ * T ∈ A := A.mul_mem (A.inv_mem hwA) hT
      have hnorm' : ∀ g ∈ A, g xV ∈ Submodule.span (ZMod 3) {xV} →
          ∃ (π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}) (μ : {k // k ≠ D.a} → ZMod 3)
            (c : ZMod 3), ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : {k // k ≠ D.a},
              g (D.coroot i) = c • μ i • w (D.coroot (π i)) := by
        intro g hg hgx
        obtain ⟨π, c, hc0, hπ, w, hw, hTw⟩ := hnorm g hg hgx
        exact ⟨π, fun _ => 1, c, w, hw, fun i => by simpa using hTw i⟩
      have hwfix : w⁻¹ xV = xV :=
        (hfix xV).mpr (Submodule.mem_span_singleton_self xV) w⁻¹ (Subgroup.inv_mem _ hw)
      obtain ⟨t, ht_eq⟩ := Submodule.mem_span_singleton.mp hTx
      have ht0 : t ≠ 0 := by
        rintro rfl
        apply hx0
        apply T.injective
        rw [← ht_eq, zero_smul, map_zero]
      have ht : t = 1 ∨ t = 2 := by
        rcases CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one t ht0 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact lr7tl_neg_one)
      have hs : c = 1 ∨ c = 2 := by
        rcases CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one c hc0 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact lr7tl_neg_one)
      have hΨy : (w⁻¹ * T) xV = t • xV := by
        show w⁻¹ (T xV) = t • xV
        rw [← ht_eq, map_smul, hwfix]
      have hinv : ∀ v, w⁻¹ (w v) = v := fun v => w.symm_apply_apply v
      have hΨσ : ∀ i : Fin 6, (w⁻¹ * T) (D.coroot (σ i : D.ι)) =
          c • D.coroot (σ (π' i) : D.ι) := by
        intro i
        have h1 := hTwl (σ i)
        rw [hπσ₀ i] at h1
        show w⁻¹ (Tl (D.coroot (σ i : D.ι))) = _
        rw [h1, map_smul, hinv]
      refine ggQ2g_E7_false D e' hecart' hbas A hWA xV D.a he0' hV hfix hnorm'
        (w⁻¹ * T) hΨA c t hs ht hΨy ?_
      intro j hj
      obtain ⟨i, hi⟩ := ggQ2xa_tau_surj j hj
      have hσi : (σ i : D.ι) = e' j := by rw [hσ i, hi]
      have hσπ : (σ (π' i) : D.ι) = e' (ggg7_tau j) := by
        rw [hσ, hπ', ggQ2xa_tau_swap i, hi]
      show (w⁻¹ * T) (D.coroot (e' j)) = c • D.coroot (e' (ggg7_tau j))
      rw [← hσi, hΨσ i, hσπ]

end CFSG.StandardType

end
