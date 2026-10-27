module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7Fin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2g_E7_coord (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hcart : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 7 i j) (hbas : D.Basis) :
    ∃ κ : D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3),
      (∀ i, κ (D.coroot (e i)) = Pi.single i 1) ∧
      (∀ j v, D.root (e j) v = ∑ k, ggg7_C j k * κ v k) ∧
      (∀ j v, κ (D.simpleRefl (e j) v) = ggg7_S j (κ v)) := by
  classical
  have hLI : LinearIndependent (ZMod 3) (fun i : Fin 7 => D.coroot (e i)) :=
    hbas.1.comp e e.injective
  have hcard : Fintype.card (Fin 7) = Module.finrank (ZMod 3) D.V := by
    rw [Fintype.card_fin]
    have := hbas.2
    rw [Fintype.card_congr e.symm, Fintype.card_fin] at this
    exact this
  haveI : Module.Finite (ZMod 3) D.V := by
    refine Module.finite_of_finrank_pos ?_
    rw [← hcard]; norm_num
  have hspan : Submodule.span (ZMod 3) (Set.range fun i : Fin 7 => D.coroot (e i)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' hcard
  let B : Module.Basis (Fin 7) (ZMod 3) D.V := Module.Basis.mk hLI hspan.ge
  have hB : ∀ i, B i = D.coroot (e i) := fun i => by simp [B]
  have hκ1 : ∀ i, B.equivFun (D.coroot (e i)) = Pi.single i 1 := fun i => by
    rw [← hB i]
    simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_pi_single i 1
  have hκ2 : ∀ j v, D.root (e j) v = ∑ k, ggg7_C j k * B.equivFun v k := fun j v => by
    conv_lhs => rw [← B.sum_equivFun v]
    simp only [map_sum, map_smul, smul_eq_mul, hB, D.pairing]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcart, ggg7_C_eq, mul_comm]
  refine ⟨B.equivFun, hκ1, hκ2, fun j v => ?_⟩
  have h1 : D.simpleRefl (e j) v = v - D.root (e j) v • D.coroot (e j) :=
    Module.reflection_apply (h := D.root_coroot_self (e j)) v
  rw [h1, map_sub, map_smul, hκ1 j, hκ2 j v]
  rfl

theorem ggQ2g_E7_parab_phi (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (κ : D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (hκs : ∀ j v, κ (D.simpleRefl (e j) v) = ggg7_S j (κ v))
    (w : D.V ≃ₗ[ZMod 3] D.V) (hw : w ∈ D.parab {k | k ≠ e 0}) (v : D.V)
    (hv : κ v ∈ ggg7_phi) : κ (w v) ∈ ggg7_phi := by
  have key : ∀ w ∈ D.parab {k | k ≠ e 0},
      (∀ v, κ v ∈ ggg7_phi → κ (w v) ∈ ggg7_phi) ∧
        (∀ v, κ v ∈ ggg7_phi → κ (w⁻¹ v) ∈ ggg7_phi) := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ =>
      (∀ v, κ v ∈ ggg7_phi → κ (w v) ∈ ggg7_phi) ∧
        (∀ v, κ v ∈ ggg7_phi → κ (w⁻¹ v) ∈ ggg7_phi)) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      have hj : j ≠ 0 := fun h => hi (by rw [h])
      have hs : ∀ v, κ v ∈ ggg7_phi → κ (D.simpleRefl (e j) v) ∈ ggg7_phi := by
        intro v hv
        rw [hκs]
        exact ggg7_phi_closed _ hv j hj
      refine ⟨hs, ?_⟩
      have : (D.simpleRefl (e j))⁻¹ = D.simpleRefl (e j) := Module.reflection_inv _
      rw [this]
      exact hs
    · exact ⟨fun v hv => hv, fun v hv => hv⟩
    · rintro a b - - ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨fun v hv => ha1 (b v) (hb1 v hv), fun v hv => ?_⟩
      rw [mul_inv_rev]
      exact hb2 (a⁻¹ v) (ha2 v hv)
    · rintro a - ⟨ha1, ha2⟩
      exact ⟨ha2, by simpa using ha1⟩
  exact (key w hw).1 v hv

private noncomputable def ggQ2g_wordElt (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι) (l : List (Fin 7)) :
    D.V ≃ₗ[ZMod 3] D.V :=
  l.foldl (fun g j => D.simpleRefl (e j) * g) 1

private theorem ggQ2g_wordElt_coord (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (κ : D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (hκs : ∀ j v, κ (D.simpleRefl (e j) v) = ggg7_S j (κ v)) (l : List (Fin 7)) (v : D.V) :
    κ (ggQ2g_wordElt D e l v) = ggg7_word l (κ v) := by
  suffices h : ∀ (l : List (Fin 7)) (g : D.V ≃ₗ[ZMod 3] D.V) (v : D.V),
      κ ((l.foldl (fun g j => D.simpleRefl (e j) * g) g) v) =
        ggg7_word l (κ (g v)) by
    simpa [ggQ2g_wordElt] using h l 1 v
  intro l
  induction l with
  | nil => intro g v; rfl
  | cons j l ih =>
      intro g v
      rw [List.foldl_cons, ih]
      simp only [ggg7_word, List.foldl_cons]
      rw [LinearEquiv.mul_apply, hκs]

private theorem ggQ2g_wordElt_mem (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (l : List (Fin 7)) :
    ggQ2g_wordElt D e l ∈ A := by
  suffices h : ∀ (l : List (Fin 7)) (g : D.V ≃ₗ[ZMod 3] D.V), g ∈ A →
      l.foldl (fun g j => D.simpleRefl (e j) * g) g ∈ A by
    exact h l 1 (one_mem A)
  intro l
  induction l with
  | nil => intro g hg; exact hg
  | cons j l ih =>
      intro g hg
      rw [List.foldl_cons]
      refine ih _ (mul_mem ?_ hg)
      exact hW (Subgroup.subset_closure ⟨e j, Set.mem_univ _, rfl⟩)

theorem ggQ2g_y_not_mem {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e₀ : D.ι) (y : D.V)
    (hbas : D.Basis)
    (hV : Submodule.span (ZMod p) (insert y (Set.range fun i : {k // k ≠ e₀} => D.coroot i)) = ⊤) :
    y ∉ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ e₀} => D.coroot i) := by
  classical
  intro hy
  have hspan : Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ e₀} => D.coroot i) = ⊤ := by
    rw [← hV, Submodule.span_insert_eq_span hy]
  have h1 : Module.finrank (ZMod p) D.V ≤ Fintype.card {k // k ≠ e₀} :=
    finrank_le_of_span_eq_top (R := ZMod p) (v := fun i : {k // k ≠ e₀} => D.coroot i) hspan
  have hcard : Fintype.card {k // k ≠ e₀} + 1 = Fintype.card D.ι := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card D.ι := Fintype.card_pos_iff.mpr ⟨e₀⟩
    omega
  have h2 := hbas.2
  omega

theorem ggQ2g_E7_sigma {ι : Type} (C : Matrix ι ι ℤ) (e : Fin 7 ≃ ι) (e₀ : ι) (he0 : e₀ = e 0)
    (hcart : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) :
    ∃ σ : Fin 6 ≃ {i // i ≠ e₀}, (∀ j, (σ j : ι) = e (![6, 5, 4, 3, 1, 2] j)) ∧
      ∀ i j, C (σ i : ι) (σ j : ι) = CartanMatrix.D 6 i j := by
  subst he0
  let τ : Fin 6 → Fin 7 := ![6, 5, 4, 3, 1, 2]
  have hτ0 : ∀ j, τ j ≠ 0 := by decide
  have hτi : ∀ a b, τ a = τ b → a = b := by decide
  have hτs : ∀ t : Fin 7, t ≠ 0 → ∃ j, τ j = t := by decide
  have hτc : ∀ i j : Fin 6, CartanMatrix.E 7 (τ i) (τ j) = CartanMatrix.D 6 i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [τ, CartanMatrix.E, CartanMatrix.D]
  let σ : Fin 6 ≃ {i // i ≠ e 0} := Equiv.ofBijective
    (fun j => ⟨e (τ j), fun h => hτ0 j (e.injective h)⟩)
    ⟨fun a b hab => hτi a b (e.injective (Subtype.ext_iff.mp hab)), by
      rintro ⟨i, hi⟩
      obtain ⟨t, rfl⟩ := e.surjective i
      have ht : t ≠ 0 := fun h => hi (by rw [h])
      obtain ⟨j, hj⟩ := hτs t ht
      exact ⟨j, Subtype.ext (by simp [hj])⟩⟩
  refine ⟨σ, fun j => rfl, fun i j => ?_⟩
  show C (e (τ i)) (e (τ j)) = _
  rw [hcart]
  exact hτc i j

theorem ggQ2g_E7_false (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hcart : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 7 i j) (hbas : D.Basis)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hA : D.weyl ≤ A) (y : D.V) (e₀ : D.ι) (he0 : e₀ = e 0)
    (hV : Submodule.span (ZMod 3) (insert y (Set.range fun i : {k // k ≠ e₀} => D.coroot i)) = ⊤)
    (hfix : ∀ v, (∀ g ∈ D.parab {k | k ≠ e₀}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {y})
    (hnorm : ∀ g ∈ A, g y ∈ Submodule.span (ZMod 3) {y} →
      ∃ (π : {k // k ≠ e₀} ≃ {k // k ≠ e₀}) (μ : {k // k ≠ e₀} → ZMod 3) (c : ZMod 3),
        ∃ w ∈ D.parab {k | k ≠ e₀}, ∀ i : {k // k ≠ e₀},
          g (D.coroot i) = c • μ i • w (D.coroot (π i)))
    (Ψ : D.V ≃ₗ[ZMod 3] D.V) (hΨ : Ψ ∈ A) (s t : ZMod 3) (hs : s = 1 ∨ s = 2)
    (ht : t = 1 ∨ t = 2) (hΨy : Ψ y = t • y)
    (hΨc : ∀ j : Fin 7, j ≠ 0 → Ψ (D.coroot (e j)) = s • D.coroot (e (ggg7_tau j))) : False := by
  classical
  subst he0
  obtain ⟨κ, hκ1, hκ2, hκs⟩ := ggQ2g_E7_coord D e hcart hbas
  have hy0 : y ≠ 0 := fun h =>
    ggQ2g_y_not_mem D (e 0) y hbas hV (by rw [h]; exact Submodule.zero_mem _)
  obtain ⟨r, hr, hκyr⟩ : ∃ r : ZMod 3, (r = 1 ∨ r = 2) ∧ κ y = r • ggg7_y := by
    have hal := ggQ2g_alpha_fixed rfl D (e 0) y hfix
    have hrows : ∀ j : Fin 7, j ≠ 0 → ∑ k, ggg7_C j k * κ y k = 0 := by
      intro j hj
      rw [← hκ2 j y]
      exact hal ⟨e j, fun h => hj (e.injective h)⟩
    have hk0 : κ y ≠ 0 := fun h => hy0 (κ.injective (by rw [h, map_zero]))
    rcases ggg7_y_unique (κ y) hrows with h | h | h
    · exact absurd h hk0
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨2, Or.inr rfl, h⟩
  have hκΨ : ∀ v, κ (Ψ v) = ggg7_T s t (κ v) := by
    have hlin : κ.toLinearMap ∘ₗ Ψ.toLinearMap = ggg7_Tl s t ∘ₗ κ.toLinearMap := by
      refine LinearMap.ext_on hV ?_
      intro v hv
      rcases hv with hv | ⟨i, hi⟩
      · rw [hv]
        show κ (Ψ y) = ggg7_Tl s t (κ y)
        rw [hΨy, map_smul, hκyr, map_smul, ggg7_Tl_apply, ggg7_T_y s t hs ht]
        exact smul_comm _ _ _
      · obtain ⟨j, hj⟩ := e.surjective i.1
        have hj0 : j ≠ 0 := fun h => i.2 (by rw [← hj, h])
        rw [← hi]
        show κ (Ψ (D.coroot i.1)) = ggg7_Tl s t (κ (D.coroot i.1))
        rw [← hj, hΨc j hj0, map_smul]
        simp only [hκ1, ggg7_Tl_apply, ggg7_T_single, ggg7_img_ne s t j hj0]
    intro v
    simpa [ggg7_Tl_apply] using LinearMap.congr_fun hlin v
  have hκΨi : ∀ v, κ (Ψ⁻¹ v) = ggg7_T s t (κ v) := by
    intro v
    have h1 := hκΨ (Ψ⁻¹ v)
    have h2 : Ψ (Ψ⁻¹ v) = v := Ψ.apply_symm_apply v
    rw [h2] at h1
    rw [h1, ggg7_T_involutive s t hs ht]
  obtain ⟨l, i0, hi0, hNy0, hNi⟩ := ggg7_cert s t hs ht
  let N : D.V ≃ₗ[ZMod 3] D.V :=
    ggQ2g_wordElt D e l * (Ψ * D.simpleRefl (e 0) * Ψ⁻¹) * ggQ2g_wordElt D e l.reverse
  have hNA : N ∈ A := by
    have hS0 : D.simpleRefl (e 0) ∈ A := hA (Subgroup.subset_closure ⟨e 0, Set.mem_univ _, rfl⟩)
    exact A.mul_mem (A.mul_mem (ggQ2g_wordElt_mem D e A hA l)
      (A.mul_mem (A.mul_mem hΨ hS0) (A.inv_mem hΨ))) (ggQ2g_wordElt_mem D e A hA l.reverse)
  have hκN : ∀ v, κ (N v) = ggg7_N l s t (κ v) := by
    intro v
    simp only [N, LinearEquiv.mul_apply]
    rw [ggQ2g_wordElt_coord D e κ hκs, hκΨ, hκs, hκΨi, ggQ2g_wordElt_coord D e κ hκs]
    rfl
  have hNy : N y = y := by
    apply κ.injective
    rw [hκN, hκyr]
    exact hNy0 r
  obtain ⟨π, μ, c, w, hw, hN⟩ :=
    hnorm N hNA (by rw [hNy]; exact Submodule.mem_span_singleton_self y)
  have hi0' : e i0 ≠ e 0 := fun h => hi0 (e.injective h)
  have hlhs : κ (N (D.coroot (e i0))) = ggg7_N l s t (Pi.single i0 1) := by rw [hκN, hκ1]
  have hmem : ∀ i : {k // k ≠ e 0}, κ (w (D.coroot i.1)) ∈ ggg7_phi := by
    intro i
    obtain ⟨j, hj⟩ := e.surjective i.1
    have hj0 : j ≠ 0 := fun h => i.2 (by rw [← hj, h])
    refine ggQ2g_E7_parab_phi D e κ hκs w hw _ ?_
    rw [← hj, hκ1]
    exact ggg7_phi_simple j hj0
  have hfinal : ggg7_N l s t (Pi.single i0 1) =
      (c * μ ⟨e i0, hi0'⟩) • κ (w (D.coroot (π ⟨e i0, hi0'⟩).1)) := by
    rw [← hlhs, hN ⟨e i0, hi0'⟩, map_smul, map_smul, smul_smul]
  have hv := hmem (π ⟨e i0, hi0'⟩)
  generalize c * μ ⟨e i0, hi0'⟩ = a at hfinal
  generalize κ (w (D.coroot (π ⟨e i0, hi0'⟩).1)) = u at hfinal hv
  rcases (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) a with rfl | rfl | rfl
  · rw [zero_smul] at hfinal
    have h0 : N (D.coroot (e i0)) = 0 := by
      apply κ.injective
      rw [hlhs, hfinal, map_zero]
    have h1 : D.coroot (e i0) = 0 := by
      apply N.injective
      rw [h0, map_zero]
    have h2 := congrArg κ h1
    rw [hκ1, map_zero] at h2
    have h3 := congrFun h2 i0
    simp at h3
  · rw [one_smul] at hfinal
    exact hNi (by rw [hfinal]; exact hv)
  · have h2 : (2 : ZMod 3) • u = -u := by
      ext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      generalize u i = z
      revert z
      decide
    rw [h2] at hfinal
    exact hNi (by rw [hfinal]; exact ggg7_phi_neg u hv)

end CFSG.StandardType

end
