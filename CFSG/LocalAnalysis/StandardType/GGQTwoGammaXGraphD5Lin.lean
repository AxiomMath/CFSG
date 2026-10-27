module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphD5Fin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphD5Lin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2gx_D5_parab_pred (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (κ : D.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ j v, κ (D.simpleRefl (e j) v) = ggg5_S j (κ v)) (a : Fin 5)
    (P : (Fin 5 → ZMod 3) → Prop) (hP : ∀ v, P v → ∀ j : Fin 5, j ≠ a → P (ggg5_S j v))
    (w : D.V ≃ₗ[ZMod 3] D.V) (hw : w ∈ D.parab {k | k ≠ e a}) (v : D.V) (hv : P (κ v)) :
    P (κ (w v)) := by
  have key : ∀ w ∈ D.parab {k | k ≠ e a},
      (∀ v, P (κ v) → P (κ (w v))) ∧ (∀ v, P (κ v) → P (κ (w⁻¹ v))) := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ =>
      (∀ v, P (κ v) → P (κ (w v))) ∧ (∀ v, P (κ v) → P (κ (w⁻¹ v)))) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      have hj : j ≠ a := fun h => hi (by rw [h])
      have hs : ∀ v, P (κ v) → P (κ (D.simpleRefl (e j) v)) := by
        intro v hv
        rw [hκs]
        exact hP _ hv j hj
      refine ⟨hs, ?_⟩
      have hinv : (D.simpleRefl (e j))⁻¹ = D.simpleRefl (e j) :=
        Module.reflection_inv _
      rw [hinv]
      exact hs
    · exact ⟨fun v hv => hv, fun v hv => hv⟩
    · rintro g₁ g₂ - - ⟨h1a, h1b⟩ ⟨h2a, h2b⟩
      refine ⟨fun v hv => h1a (g₂ v) (h2a v hv), fun v hv => ?_⟩
      rw [mul_inv_rev]
      exact h2b (g₁⁻¹ v) (h1b v hv)
    · rintro g - ⟨h1a, h1b⟩
      exact ⟨h1b, by simpa using h1a⟩
  exact (key w hw).1 v hv

theorem ggQ2gx_D5_one_false (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (hcart : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.D 5 i j) (hbas : D.Basis)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hA : D.weyl ≤ A) (y x : D.V) (b₀ a₀ : D.ι)
    (hb₀ : b₀ = e 0) (ha₀ : a₀ = e 1)
    (hV : Submodule.span (ZMod 3) (insert y (Set.range fun i : {k // k ≠ b₀} => D.coroot i)) = ⊤)
    (hfixy : ∀ v, (∀ g ∈ D.parab {k | k ≠ b₀}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {y})
    (hfixx : ∀ v, (∀ g ∈ D.parab {k | k ≠ a₀}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hnorm : ∀ g ∈ A, g x ∈ Submodule.span (ZMod 3) {x} →
      g ∈ Subgroup.normalizer (D.parab {k | k ≠ a₀} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (Ψ : D.V ≃ₗ[ZMod 3] D.V) (hΨ : Ψ ∈ A) (s t : ZMod 3) (hs : s = 1 ∨ s = 2)
    (ht : t = 1 ∨ t = 2) (g gi : Fin 5 → Fin 5) (hg : ggg5_pair g gi) (hΨy : Ψ y = t • y)
    (hΨc : ∀ j : Fin 5, j ≠ 0 → Ψ (D.coroot (e j)) = s • D.coroot (e (g j))) : False := by
  classical
  subst hb₀ ha₀
  obtain ⟨κ, hκ1, -, hκs⟩ := ggQ2g_D5_coord D e hcart hbas
  obtain ⟨r₀, -, hκy⟩ :=
    ggQ2g_D5_line D e κ hκs 0 ggg5_y ggg5_y_ne ggg5_y_fixed y hfixy
  obtain ⟨r', -, hκx⟩ :=
    ggQ2g_D5_line D e κ hκs 1 ggg5x_x ggg5x_x_ne ggg5x_x_fixed x hfixx
  have hκΨ : ∀ v, κ (Ψ v) = ggg5_T g s t (κ v) := by
    have hlin : κ.toLinearMap ∘ₗ Ψ.toLinearMap = ggg5_Tl g s t ∘ₗ κ.toLinearMap := by
      refine LinearMap.ext_on hV ?_
      intro v hv
      rcases hv with hv | ⟨i, hi⟩
      · rw [hv]
        show κ (Ψ y) = ggg5_Tl g s t (κ y)
        rw [hΨy, map_smul, hκy, map_smul, ggg5_Tl_apply, ggg5_T_y g gi hg s t hs ht]
        exact smul_comm _ _ _
      · obtain ⟨j, hj⟩ := e.surjective i.1
        have hj0 : j ≠ 0 := fun h => i.2 (by rw [← hj, h])
        rw [← hi]
        show κ (Ψ (D.coroot i.1)) = ggg5_Tl g s t (κ (D.coroot i.1))
        rw [← hj, hΨc j hj0, map_smul]
        simp only [hκ1, ggg5_Tl_apply, ggg5_T_single, ggg5_img_ne g s t j hj0]
    intro v
    simpa [ggg5_Tl_apply] using LinearMap.congr_fun hlin v
  have hκΨi : ∀ v, κ (Ψ⁻¹ v) = ggg5_T gi s t (κ v) := by
    intro v
    have h1 := hκΨ (Ψ⁻¹ v)
    have h2 : Ψ (Ψ⁻¹ v) = v := Ψ.apply_symm_apply v
    rw [h2] at h1
    rw [h1, ggg5_T_inv g gi hg s t hs ht]
  obtain ⟨l, hl, hNx0, hN0, hN1, hN234⟩ := ggg5x_cert g gi hg s t hs ht
  have hex : ∃ N : D.V ≃ₗ[ZMod 3] D.V, N ∈ A ∧
      ∀ v, κ (N v) = ggg5_N g gi l s t (κ v) := by
    let r : Fin 5 → D.V ≃ₗ[ZMod 3] D.V := fun k => D.simpleRefl (e k)
    have hr : ∀ k v, κ (r k v) = ggg5_S k (κ v) := fun k v => hκs k v
    have hrA : ∀ k, r k ∈ A := fun k =>
      hA (Subgroup.subset_closure ⟨e k, Set.mem_univ _, rfl⟩)
    have hPA : Ψ * r 0 * Ψ⁻¹ ∈ A := A.mul_mem (A.mul_mem hΨ (hrA 0)) (A.inv_mem hΨ)
    rcases hl with rfl | rfl | rfl
    · refine ⟨Ψ * r 0 * Ψ⁻¹, hPA, fun v => ?_⟩
      simp only [LinearEquiv.mul_apply, hκΨ, hr, hκΨi]
      rfl
    · refine ⟨r 1 * r 2 * r 3 * (Ψ * r 0 * Ψ⁻¹) * r 3 * r 2 * r 1, ?_,
        fun v => ?_⟩
      · exact A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem
          (A.mul_mem (hrA 1) (hrA 2)) (hrA 3)) hPA) (hrA 3)) (hrA 2)) (hrA 1)
      · simp only [LinearEquiv.mul_apply, hκΨ, hr, hκΨi]
        rfl
    · refine ⟨r 1 * r 2 * r 4 * (Ψ * r 0 * Ψ⁻¹) * r 4 * r 2 * r 1, ?_,
        fun v => ?_⟩
      · exact A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem
          (A.mul_mem (hrA 1) (hrA 2)) (hrA 4)) hPA) (hrA 4)) (hrA 2)) (hrA 1)
      · simp only [LinearEquiv.mul_apply, hκΨ, hr, hκΨi]
        rfl
  obtain ⟨N, hNA, hκN⟩ := hex
  obtain ⟨u₀, hκu₀⟩ : ∃ u₀ : D.V, κ u₀ = ggg5x_x :=
    ⟨κ.symm _, κ.apply_symm_apply _⟩
  have hxu₀ : x = r' • u₀ := κ.injective (by rw [map_smul, hκu₀, hκx])
  have hNu₀ : N u₀ = u₀ ∨ N u₀ = -u₀ := by
    rcases hNx0 with h | h
    · left; apply κ.injective; rw [hκN, hκu₀, h]
    · right; apply κ.injective; rw [hκN, hκu₀, h, map_neg, hκu₀]; rfl
  have hNx : N x ∈ Submodule.span (ZMod 3) {x} := by
    have hNx' : N x = x ∨ N x = -x := by
      rw [hxu₀, map_smul]
      rcases hNu₀ with h | h
      · left; rw [h]
      · right; rw [h, smul_neg]
    rcases hNx' with h | h
    · rw [h]; exact Submodule.mem_span_singleton_self x
    · rw [h]; exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self x)
  have hR : N * D.simpleRefl (e 0) * N⁻¹ ∈ D.parab {k | k ≠ e 1} := by
    have hr0 : D.simpleRefl (e 0) ∈ D.parab {k | k ≠ e 1} :=
      Subgroup.subset_closure ⟨e 0, fun h => absurd (e.injective h) (by decide), rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hnorm N hNA hNx) _).mp hr0
  let f : D.V →ₗ[ZMod 3] ZMod 3 := (D.root (e 0)).comp (N.symm : D.V →ₗ[ZMod 3] D.V)
  have hκR : ∀ z, κ ((N * D.simpleRefl (e 0) * N⁻¹) z) =
      κ z - f z • ggg5_N g gi l s t (Pi.single 0 1) := by
    intro z
    have h1 : (N * D.simpleRefl (e 0) * N⁻¹) z = z - f z • N (D.coroot (e 0)) := by
      show N (D.simpleRefl (e 0) (N.symm z)) = _
      rw [GGQ2Lin.simpleRefl, Module.reflection_apply, map_sub, map_smul,
        LinearEquiv.apply_symm_apply]
      rfl
    rw [h1, map_sub, map_smul, hκN, hκ1]
    rfl
  have hf0 : f (D.coroot (e 0)) = 0 := by
    have h := ggQ2gx_D5_parab_pred D e κ hκs 1
      (fun w => w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 ∧ w 4 = 0)
      (fun w hw j hj => ggg5x_S_factorA1 w hw j hj) _ hR (D.coroot (e 0))
      (by rw [hκ1]; decide)
    simp only [hκR, hκ1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    obtain ⟨-, h2, h3, h4⟩ := h
    have key : ∀ i : Fin 5, i ≠ 0 → (Pi.single 0 1 : Fin 5 → ZMod 3) i -
        f (D.coroot (e 0)) * ggg5_N g gi l s t (Pi.single 0 1) i = 0 →
        f (D.coroot (e 0)) = 0 ∨ ggg5_N g gi l s t (Pi.single 0 1) i = 0 := by
      intro i hi h
      rw [Pi.single_eq_of_ne hi, zero_sub] at h
      exact mul_eq_zero.mp (neg_eq_zero.mp h)
    rcases hN234 with hv | hv | hv
    · exact (key 2 (by decide) h2).resolve_right hv
    · exact (key 3 (by decide) h3).resolve_right hv
    · exact (key 4 (by decide) h4).resolve_right hv
  have hfk : ∀ k : Fin 5, k ≠ 0 → k ≠ 1 → f (D.coroot (e k)) = 0 := by
    intro k hk0 hk1
    have h := ggQ2gx_D5_parab_pred D e κ hκs 1 (fun w => w 0 = 0 ∧ w 1 = 0)
      (fun w hw j hj => ggg5x_S_factorA3 w hw j hj) _ hR (D.coroot (e k))
      (by rw [hκ1]; exact ⟨Pi.single_eq_of_ne (Ne.symm hk0) _, Pi.single_eq_of_ne (Ne.symm hk1) _⟩)
    have h0 := h.1
    simp only [hκR, hκ1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h0
    rw [Pi.single_eq_of_ne (Ne.symm hk0), zero_sub] at h0
    exact (mul_eq_zero.mp (neg_eq_zero.mp h0)).resolve_right hN0
  have hsum : N (D.coroot (e 0)) =
      ∑ j : Fin 5, ggg5_N g gi l s t (Pi.single 0 1) j • D.coroot (e j) := by
    apply κ.injective
    rw [hκN, hκ1, map_sum]
    simp only [map_smul, hκ1]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hfN : f (N (D.coroot (e 0))) = 2 := by
    show D.root (e 0) (N.symm (N (D.coroot (e 0)))) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact D.root_coroot_self (e 0)
  have h2 : (2 : ZMod 3) = 0 := by
    rw [← hfN, hsum, map_sum]
    simp only [map_smul, smul_eq_mul, Fin.sum_univ_five]
    rw [hf0, hN1, hfk 2 (by decide) (by decide), hfk 3 (by decide) (by decide),
      hfk 4 (by decide) (by decide)]
    simp
  exact absurd h2 (by decide)

end CFSG.StandardType

end
