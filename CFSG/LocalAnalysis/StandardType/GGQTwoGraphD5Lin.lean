module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphD5Fin
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2g_D5_coord (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (hcart : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.D 5 i j) (hbas : D.Basis) :
    ∃ κ : D.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3),
      (∀ i, κ (D.coroot (e i)) = Pi.single i 1) ∧
      (∀ j v, D.root (e j) v = ∑ k, ggg5_C j k * κ v k) ∧
      (∀ j v, κ (D.simpleRefl (e j) v) = ggg5_S j (κ v)) := by
  classical
  have hLI : LinearIndependent (ZMod 3) (fun i : Fin 5 => D.coroot (e i)) :=
    hbas.1.comp e e.injective
  have hcard : Fintype.card (Fin 5) = Module.finrank (ZMod 3) D.V := by
    rw [Fintype.card_fin]
    have := hbas.2
    rw [Fintype.card_congr e.symm, Fintype.card_fin] at this
    exact this
  have : Module.Finite (ZMod 3) D.V := by
    refine Module.finite_of_finrank_pos ?_
    rw [← hcard]; norm_num
  have hspan : Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => D.coroot (e i)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' hcard
  let B : Module.Basis (Fin 5) (ZMod 3) D.V := Module.Basis.mk hLI hspan.ge
  have hB : ∀ i, B i = D.coroot (e i) := fun i => by simp [B]
  have hκ1 : ∀ i, B.equivFun (D.coroot (e i)) = Pi.single i 1 := fun i => by
    rw [← hB i]
    simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_pi_single i 1
  have hκ2 : ∀ j v, D.root (e j) v = ∑ k, ggg5_C j k * B.equivFun v k := fun j v => by
    conv_lhs => rw [← B.sum_equivFun v]
    simp only [map_sum, map_smul, smul_eq_mul, hB, D.pairing]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcart, ggg5_C_eq, mul_comm]
  refine ⟨B.equivFun, hκ1, hκ2, fun j v => ?_⟩
  have h1 : D.simpleRefl (e j) v = v - D.root (e j) v • D.coroot (e j) :=
    Module.reflection_apply (h := D.root_coroot_self (e j)) v
  rw [h1, map_sub, map_smul, hκ1 j, hκ2 j v]
  rfl

theorem ggQ2g_D5_line (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (κ : D.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ j v, κ (D.simpleRefl (e j) v) = ggg5_S j (κ v))
    (a : Fin 5) (v₀ : Fin 5 → ZMod 3) (hv₀ : v₀ ≠ 0)
    (hfix₀ : ∀ j : Fin 5, j ≠ a → ggg5_S j v₀ = v₀) (u : D.V)
    (hfix : ∀ v, (∀ g ∈ D.parab {k | k ≠ e a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {u}) :
    ∃ r : ZMod 3, (r = 1 ∨ r = 2) ∧ κ u = r • v₀ := by
  have hle : D.parab {k | k ≠ e a} ≤
      MulAction.stabilizer (D.V ≃ₗ[ZMod 3] D.V) (κ.symm v₀) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    have hj : j ≠ a := fun h => hi (by rw [h])
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    apply κ.injective
    show κ (D.simpleRefl (e j) (κ.symm v₀)) = κ (κ.symm v₀)
    rw [hκs, κ.apply_symm_apply, hfix₀ j hj]
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.mp ((hfix (κ.symm v₀)).mp fun g hg => hle hg)
  have hr'0 : r' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hr'
    exact hv₀ (by simpa using congrArg κ hr'.symm)
  have hsq : r' * r' = 1 := (by decide : ∀ r : ZMod 3, r ≠ 0 → r * r = 1) r' hr'0
  refine ⟨r', (by decide : ∀ r : ZMod 3, r ≠ 0 → r = 1 ∨ r = 2) r' hr'0, ?_⟩
  have h1 : u = r' • κ.symm v₀ := by
    rw [← hr', smul_smul, hsq, one_smul]
  rw [h1, map_smul, κ.apply_symm_apply]

theorem ggQ2g_D5_parab_phi (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (κ : D.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ j v, κ (D.simpleRefl (e j) v) = ggg5_S j (κ v))
    (w : D.V ≃ₗ[ZMod 3] D.V) (hw : w ∈ D.parab {k | k ≠ e 3}) (v : D.V)
    (hv : κ v ∈ ggg5_phi) : κ (w v) ∈ ggg5_phi := by
  have key : ∀ w ∈ D.parab {k | k ≠ e 3},
      (∀ v, κ v ∈ ggg5_phi → κ (w v) ∈ ggg5_phi) ∧
        (∀ v, κ v ∈ ggg5_phi → κ (w⁻¹ v) ∈ ggg5_phi) := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ =>
      (∀ v, κ v ∈ ggg5_phi → κ (w v) ∈ ggg5_phi) ∧
        (∀ v, κ v ∈ ggg5_phi → κ (w⁻¹ v) ∈ ggg5_phi)) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      have hj : j ≠ 3 := fun h => hi (by rw [h])
      have hs : ∀ v, κ v ∈ ggg5_phi → κ (D.simpleRefl (e j) v) ∈ ggg5_phi := by
        intro v hv
        rw [hκs]
        exact ggg5_phi_closed _ hv j hj
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

private noncomputable def ggQ2g_wordElt5 (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι) (l : List (Fin 5)) :
    D.V ≃ₗ[ZMod 3] D.V :=
  l.foldl (fun g j => D.simpleRefl (e j) * g) 1

private theorem ggQ2g_wordElt5_coord (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (κ : D.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ j v, κ (D.simpleRefl (e j) v) = ggg5_S j (κ v)) (l : List (Fin 5)) (v : D.V) :
    κ (ggQ2g_wordElt5 D e l v) = ggg5_word l (κ v) := by
  suffices h : ∀ (l : List (Fin 5)) (g : D.V ≃ₗ[ZMod 3] D.V) (v : D.V),
      κ ((l.foldl (fun g j => D.simpleRefl (e j) * g) g) v) =
        ggg5_word l (κ (g v)) by
    simpa [ggQ2g_wordElt5] using h l 1 v
  intro l
  induction l with
  | nil => intro g v; rfl
  | cons j l ih =>
      intro g v
      rw [List.foldl_cons, ih]
      simp only [ggg5_word, List.foldl_cons]
      rw [LinearEquiv.mul_apply, hκs]

private theorem ggQ2g_wordElt5_mem (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (l : List (Fin 5)) :
    ggQ2g_wordElt5 D e l ∈ A := by
  suffices h : ∀ (l : List (Fin 5)) (g : D.V ≃ₗ[ZMod 3] D.V), g ∈ A →
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

theorem ggQ2g_D5_false (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (hcart : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.D 5 i j) (hbas : D.Basis)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hA : D.weyl ≤ A) (y x : D.V) (b₀ a₀ : D.ι)
    (hb₀ : b₀ = e 0) (ha₀ : a₀ = e 3)
    (hV : Submodule.span (ZMod 3) (insert y (Set.range fun i : {k // k ≠ b₀} => D.coroot i)) = ⊤)
    (hfixy : ∀ v, (∀ g ∈ D.parab {k | k ≠ b₀}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {y})
    (hfixx : ∀ v, (∀ g ∈ D.parab {k | k ≠ a₀}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hnorm : ∀ u : D.V,
      (∀ v, (∀ g ∈ D.parab {k | k ≠ a₀}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u}) →
      u ∉ Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ a₀} => D.coroot i) →
      ∀ g ∈ A, g u ∈ Submodule.span (ZMod 3) {u} →
        ∃ (π : {k // k ≠ a₀} ≃ {k // k ≠ a₀}) (μ : {k // k ≠ a₀} → ZMod 3) (c : ZMod 3),
          ∃ w ∈ D.parab {k | k ≠ a₀}, ∀ i : {k // k ≠ a₀},
            g (D.coroot i) = c • μ i • w (D.coroot (π i)))
    (Ψ : D.V ≃ₗ[ZMod 3] D.V) (hΨ : Ψ ∈ A) (s t : ZMod 3) (hs : s = 1 ∨ s = 2)
    (ht : t = 1 ∨ t = 2) (g gi : Fin 5 → Fin 5) (hg : ggg5_pair g gi) (hΨy : Ψ y = t • y)
    (hΨc : ∀ j : Fin 5, j ≠ 0 → Ψ (D.coroot (e j)) = s • D.coroot (e (g j))) : False := by
  classical
  subst hb₀ ha₀
  obtain ⟨κ, hκ1, -, hκs⟩ := ggQ2g_D5_coord D e hcart hbas
  obtain ⟨r, -, hκy⟩ := ggQ2g_D5_line D e κ hκs 0 ggg5_y ggg5_y_ne ggg5_y_fixed y hfixy
  obtain ⟨r', hr', hκx⟩ := ggQ2g_D5_line D e κ hκs 3 ggg5_x ggg5_x_ne ggg5_x_fixed x hfixx
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
  obtain ⟨l, i0, hi0, hNx0, hNi⟩ := ggg5_cert g gi hg s t hs ht
  let N : D.V ≃ₗ[ZMod 3] D.V :=
    ggQ2g_wordElt5 D e l * (Ψ * D.simpleRefl (e 0) * Ψ⁻¹) * ggQ2g_wordElt5 D e l.reverse
  have hNA : N ∈ A := by
    have hS0 : D.simpleRefl (e 0) ∈ A := hA (Subgroup.subset_closure ⟨e 0, Set.mem_univ _, rfl⟩)
    exact A.mul_mem (A.mul_mem (ggQ2g_wordElt5_mem D e A hA l)
      (A.mul_mem (A.mul_mem hΨ hS0) (A.inv_mem hΨ))) (ggQ2g_wordElt5_mem D e A hA l.reverse)
  have hκN : ∀ v, κ (N v) = ggg5_N g gi l s t (κ v) := by
    intro v
    simp only [N, LinearEquiv.mul_apply]
    rw [ggQ2g_wordElt5_coord D e κ hκs, hκΨ, hκs, hκΨi, ggQ2g_wordElt5_coord D e κ hκs]
    rfl
  obtain ⟨u₀, hκu₀⟩ : ∃ u₀ : D.V, κ u₀ = ggg5_x := ⟨κ.symm _, κ.apply_symm_apply _⟩
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
  have hnotx : x ∉ Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ e 3} => D.coroot i) := by
    intro hx
    have hle : Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ e 3} => D.coroot i) ≤
        LinearMap.ker ((LinearMap.proj (3 : Fin 5) : (Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3) ∘ₗ
          κ.toLinearMap) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i.1
      have hj3 : j ≠ 3 := fun h => i.2 (by rw [← hj, h])
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.proj_apply]
      rw [← hj, hκ1, Pi.single_eq_of_ne (Ne.symm hj3)]
    have h3 := hle hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.proj_apply] at h3
    rw [hκx, Pi.smul_apply, ggg5_x_three, smul_eq_mul, mul_one] at h3
    rcases hr' with rfl | rfl <;> exact absurd h3 (by decide)
  obtain ⟨π, μ, c, w, hw, hN⟩ := hnorm x hfixx hnotx N hNA hNx
  have hi0' : e i0 ≠ e 3 := fun h => hi0 (e.injective h)
  have hlhs : κ (N (D.coroot (e i0))) = ggg5_N g gi l s t (Pi.single i0 1) := by
    rw [hκN, hκ1]
  have hmem : ∀ i : {k // k ≠ e 3}, κ (w (D.coroot i.1)) ∈ ggg5_phi := by
    intro i
    obtain ⟨j, hj⟩ := e.surjective i.1
    have hj3 : j ≠ 3 := fun h => i.2 (by rw [← hj, h])
    refine ggQ2g_D5_parab_phi D e κ hκs w hw _ ?_
    rw [← hj, hκ1]
    exact ggg5_phi_simple j hj3
  have hfinal : ggg5_N g gi l s t (Pi.single i0 1) =
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
    exact hNi (by rw [hfinal]; exact ggg5_phi_neg u hv)

end CFSG.StandardType

end
