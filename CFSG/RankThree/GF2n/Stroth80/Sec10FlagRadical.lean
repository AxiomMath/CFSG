module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveIsometry

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private lemma bilin_apply_eq_quad_sub {B : LinearMap.BilinForm K E} {Qf : E → K}
    (hQf : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (e f : E) :
    B e f = Qf (e + f) - Qf e - Qf f := by
  rw [hQf]
  ring

private lemma quad_isometry {Γ : Type*} [Group Γ] {B : LinearMap.BilinForm K E} {Qf : E → K}
    (hQf : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (ρ : Γ →* (E ≃ₗ[K] E))
    (hρQ : ∀ γ e, Qf (ρ γ e) = Qf e) : ∀ (γ : Γ) x y, B (ρ γ x) (ρ γ y) = B x y := by
  intro γ x y
  rw [bilin_apply_eq_quad_sub hQf, bilin_apply_eq_quad_sub hQf,
    ← map_add, hρQ, hρQ, hρQ]

private lemma opm_mem_orthogonal_of_mem_orthogonal {Γ : Type*} [Group Γ]
    {B : LinearMap.BilinForm K E} {Qf : E → K} (hndB : B.Nondegenerate) (hrefl : B.IsRefl)
    (hQf : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) {Vb Ub : Submodule K E}
    (ρ : Γ →* (E ≃ₗ[K] E)) (hρQ : ∀ γ e, Qf (ρ γ e) = Qf e)
    (hρV : ∀ γ, ∀ v ∈ Vb, ρ γ v = v)
    (hρU : ∀ γ, ∀ e ∈ B.orthogonal Ub, ρ γ e - e ∈ Vb) :
    ∀ γ, ∀ e ∈ B.orthogonal Vb, opm (ρ γ) e ∈ Ub := by
  have hiso : ∀ (γ : Γ) x y, B (ρ γ x) (ρ γ y) = B x y := quad_isometry hQf ρ hρQ
  have hρW : ∀ γ, ∀ e ∈ B.orthogonal Vb, ρ γ e ∈ B.orthogonal Vb := by
    intro γ e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at he ⊢
    intro v hv
    have h1 : B (ρ γ v) (ρ γ e) = B v e := hiso γ v e
    rw [hρV γ v hv] at h1
    rw [h1]
    exact he v hv
  intro γ e he
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hndB hrefl Ub]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
  have hxV : opm (ρ γ) x ∈ Vb := by
    rw [opm_apply]
    exact hρU γ x hx
  have hge : ρ γ e ∈ B.orthogonal Vb := hρW γ e he
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hge
  have h1 : B (opm (ρ γ) x) (ρ γ e) = 0 := hge _ hxV
  have h2 : B (ρ γ x) (ρ γ e) = B x e := hiso γ x e
  have h4 : opm (ρ γ) e = ρ γ e - e := opm_apply _ _
  rw [h4]
  simp only [map_sub, LinearMap.sub_apply]
  rw [← h2]
  have hsub : B x (ρ γ e) - B (ρ γ x) (ρ γ e) = B (x - ρ γ x) (ρ γ e) := by
    rw [map_sub, LinearMap.sub_apply]
  rw [hsub]
  have hx' : x - ρ γ x = -opm (ρ γ) x := by
    rw [opm_apply]
    abel
  rw [hx', map_neg, LinearMap.neg_apply, h1, neg_zero]

private lemma opm_self_apply_eq_zero {Γ : Type*} [Group Γ] {B : LinearMap.BilinForm K E}
    {Qf : E → K} (hQf : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) {Vb Ub : Submodule K E}
    (hU : ∀ u ∈ Ub, Qf u = 0) (ρ : Γ →* (E ≃ₗ[K] E)) (hρQ : ∀ γ e, Qf (ρ γ e) = Qf e)
    (hΔ : ∀ γ, ∀ e ∈ B.orthogonal Vb, opm (ρ γ) e ∈ Ub) :
    ∀ γ, ∀ w ∈ B.orthogonal Vb, B (opm (ρ γ) w) w = 0 := by
  intro γ w hw
  have hΔw : opm (ρ γ) w ∈ Ub := hΔ γ w hw
  have h := hQf (opm (ρ γ) w) w
  rw [show opm (ρ γ) w + w = ρ γ w by rw [opm_apply]; abel, hU _ hΔw, hρQ γ w] at h
  rw [zero_add] at h
  have h' : Qf w + 0 = Qf w + B (opm (ρ γ) w) w := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h').symm

private lemma opm_antisymm {Γ : Type*} [Group Γ] {B : LinearMap.BilinForm K E}
    {Vb : Submodule K E} (ρ : Γ →* (E ≃ₗ[K] E))
    (halt : ∀ γ, ∀ w ∈ B.orthogonal Vb, B (opm (ρ γ) w) w = 0)
    (e1 e2 : B.orthogonal Vb) (γ : Γ) :
    B (opm (ρ γ) (e2 : E)) (e1 : E) = -B (opm (ρ γ) (e1 : E)) (e2 : E) := by
  have hsum : B (opm (ρ γ) ((e1 : E) + e2)) ((e1 : E) + e2) = 0 :=
    halt γ _ ((B.orthogonal Vb).add_mem e1.2 e2.2)
  have h11 : B (opm (ρ γ) (e1 : E)) (e1 : E) = 0 := halt γ e1 e1.2
  have h22 : B (opm (ρ γ) (e2 : E)) (e2 : E) = 0 := halt γ e2 e2.2
  simp only [map_add, LinearMap.add_apply] at hsum
  rw [h11, h22, zero_add, add_zero] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

private lemma basis_coord_expansion {W : Submodule K E} {C : Submodule K W}
    (bC : Module.Basis (Fin 2) K C) {e1 e2 : W} (he1 : e1 = bC 0) (he2 : e2 = bC 1)
    (v : C) : (v : W) = bC.equivFun v 0 • e1 + bC.equivFun v 1 • e2 := by
  calc (v : W) = ((∑ i : Fin 2, bC.equivFun v i • bC i : C) : W) := by
        rw [bC.sum_equivFun v]
    _ = ((bC.equivFun v 0 • bC 0 + bC.equivFun v 1 • bC 1 : C) : W) := by
        rw [Fin.sum_univ_two]
    _ = bC.equivFun v 0 • e1 + bC.equivFun v 1 • e2 := by
        rw [he1, he2]
        simp

private lemma exists_flag_decomposition {B : LinearMap.BilinForm K E} (hndB : B.Nondegenerate)
    {Vb Ub : Submodule K E} (hVU : Vb ≤ Ub)
    (hdim : Module.finrank K Ub = Module.finrank K Vb + 2) :
    ∃ e1 e2 : B.orthogonal Vb, ∀ w : B.orthogonal Vb,
      ∃ u : B.orthogonal Vb, (u : E) ∈ B.orthogonal Ub ∧ ∃ a b : K,
        (w : E) = (u : E) + a • (e1 : E) + b • (e2 : E) := by
  classical
  set W : Submodule K E := B.orthogonal Vb with hW
  have hW0W : B.orthogonal Ub ≤ W := B.orthogonal_le hVU
  have hdimW : Module.finrank K W = Module.finrank K (B.orthogonal Ub) + 2 := by
    rw [hW, LinearMap.BilinForm.finrank_orthogonal hndB,
      LinearMap.BilinForm.finrank_orthogonal hndB]
    have h1 : Module.finrank K Vb ≤ Module.finrank K E := Submodule.finrank_le Vb
    have h2 : Module.finrank K Ub ≤ Module.finrank K E := Submodule.finrank_le Ub
    omega
  let W0' : Submodule K W := (B.orthogonal Ub).submoduleOf W
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W0'
  have hCfin : Module.finrank K C = 2 := by
    have h1 : Module.finrank K W0' + Module.finrank K C = Module.finrank K W :=
      Submodule.finrank_add_eq_of_isCompl hC
    have h2 : Module.finrank K W0' = Module.finrank K (B.orthogonal Ub) :=
      (Submodule.submoduleOfEquivOfLe hW0W).finrank_eq
    omega
  let bC : Module.Basis (Fin 2) K C := Module.finBasisOfFinrankEq K C hCfin
  let e1 : W := bC 0
  let e2 : W := bC 1
  have he1 : e1 = bC 0 := rfl
  have he2 : e2 = bC 1 := rfl
  have hce : ∀ v : C, (v : W) = bC.equivFun v 0 • e1 + bC.equivFun v 1 • e2 :=
    fun v => basis_coord_expansion bC he1 he2 v
  have hdecomp : ∀ w : W, ∃ u : W, (u : E) ∈ B.orthogonal Ub ∧ ∃ a b : K,
      (w : E) = (u : E) + a • (e1 : E) + b • (e2 : E) := by
    intro w
    obtain ⟨u, v, huv, -⟩ := Submodule.existsUnique_add_of_isCompl hC w
    have huvE : (w : E) = ((u : W) : E) + ((v : C) : E) := by
      rw [← huv]
      simp
    refine ⟨(u : W), ?_, bC.equivFun v 0, bC.equivFun v 1, ?_⟩
    · exact u.2
    calc (w : E) = ((u : W) : E) + ((v : C) : E) := huvE
      _ = ((u : W) : E) + (bC.equivFun v 0 • (e1 : E) +
            bC.equivFun v 1 • (e2 : E)) := by
            rw [show ((v : C) : E) = ((v : W) : E) from rfl, hce]
            simp
      _ = ((u : W) : E) + bC.equivFun v 0 • (e1 : E) +
            bC.equivFun v 1 • (e2 : E) := by abel
  refine ⟨e1, e2, ?_⟩
  exact hdecomp

private lemma opm_mul_apply_eq_add {Vb W : Submodule K E} {x y : E ≃ₗ[K] E}
    (hx : ∀ v ∈ Vb, x v = v) (hy : ∀ w ∈ W, y w - w ∈ Vb) (w : E) (hw : w ∈ W) :
    (x * y) w - w = (x w - w) + (y w - w) := by
  have hyw : y w - w ∈ Vb := hy w hw
  rw [LinearEquiv.mul_apply]
  have hxy : x (y w) - w = x (y w - w) + (x w - w) := by
    rw [map_sub]
    abel
  rw [hxy, hx (y w - w) hyw, add_comm]

private lemma opm_inv_apply_eq_neg {Vb W : Submodule K E} {x : E ≃ₗ[K] E}
    (hx : ∀ v ∈ Vb, x v = v) (hxW : ∀ w ∈ W, x w - w ∈ Vb) (w : E) (hw : w ∈ W) :
    x⁻¹ w - w = -(x w - w) := by
  have h : x w - w ∈ Vb := hxW w hw
  apply x.injective
  have h1 : x (x⁻¹ w) = w := LinearEquiv.apply_symm_apply x w
  rw [map_sub, h1, map_neg, hx _ h, neg_sub]

private lemma isometry_inv {B : LinearMap.BilinForm K E} {x : E ≃ₗ[K] E}
    (hx : ∀ e f, B (x e) (x f) = B e f) : ∀ e f, B (x⁻¹ e) (x⁻¹ f) = B e f := by
  intro e f
  have h := hx (x⁻¹ e) (x⁻¹ f)
  have h1 : x (x⁻¹ e) = e := LinearEquiv.apply_symm_apply x e
  have h2 : x (x⁻¹ f) = f := LinearEquiv.apply_symm_apply x f
  rw [h1, h2] at h
  exact h.symm

private lemma fixes_inv {Vb : Submodule K E} {x : E ≃ₗ[K] E} (hx : ∀ v ∈ Vb, x v = v) :
    ∀ v ∈ Vb, x⁻¹ v = v := by
  intro v hv
  apply x.injective
  have h1 : x (x⁻¹ v) = v := LinearEquiv.apply_symm_apply x v
  rw [h1, hx v hv]

private lemma fixes_mul {Vb : Submodule K E} {x y : E ≃ₗ[K] E}
    (hx : ∀ v ∈ Vb, x v = v) (hy : ∀ v ∈ Vb, y v = v) : ∀ v ∈ Vb, (x * y) v = v := by
  intro v hv
  rw [LinearEquiv.mul_apply, hy v hv, hx v hv]

private lemma isometry_mul {B : LinearMap.BilinForm K E} {x y : E ≃ₗ[K] E}
    (hx : ∀ e f, B (x e) (x f) = B e f) (hy : ∀ e f, B (y e) (y f) = B e f) :
    ∀ e f, B ((x * y) e) ((x * y) f) = B e f := by
  intro e f
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]

private lemma exists_flag_coefficient_hom {Γ : Type*} [Group Γ] {B : LinearMap.BilinForm K E}
    {Vb Ub : Submodule K E} (hUorth : Ub ≤ B.orthogonal Ub) (ρ : Γ →* (E ≃ₗ[K] E))
    (hρU : ∀ γ, ∀ e ∈ B.orthogonal Ub, ρ γ e - e ∈ Vb)
    (hΔW : ∀ γ, ∀ e ∈ B.orthogonal Vb, opm (ρ γ) e ∈ Ub)
    (e1 e2 : B.orthogonal Vb) :
    ∃ c : Γ →* Multiplicative K,
      ∀ γ, c γ = 1 → B (opm (ρ γ) (e1 : E)) (e2 : E) = 0 := by
  let c : Γ →* Multiplicative K := {
    toFun := fun γ => Multiplicative.ofAdd (B (opm (ρ γ) (e1 : E)) (e2 : E))
    map_one' := by
      show Multiplicative.ofAdd (B (opm (ρ 1) (e1 : E)) (e2 : E)) = 1
      rw [ofAdd_eq_one, map_one]
      simp [opm]
    map_mul' := by
      intro γ δ
      show Multiplicative.ofAdd (B (opm (ρ (γ * δ)) (e1 : E)) (e2 : E)) =
        Multiplicative.ofAdd (B (opm (ρ γ) (e1 : E)) (e2 : E)) *
        Multiplicative.ofAdd (B (opm (ρ δ) (e1 : E)) (e2 : E))
      rw [← ofAdd_add]
      congr 1
      have hop : opm (ρ (γ * δ)) (e1 : E) =
          opm (ρ γ) (opm (ρ δ) (e1 : E)) + opm (ρ δ) (e1 : E) +
            opm (ρ γ) (e1 : E) := by
        simp only [opm_apply, map_mul, LinearEquiv.mul_apply, map_sub]
        abel
      have hfirst : B (opm (ρ γ) (opm (ρ δ) (e1 : E))) (e2 : E) = 0 := by
        have hmem : opm (ρ δ) (e1 : E) ∈ B.orthogonal Ub := hUorth (hΔW δ (e1 : E) e1.2)
        have hV : opm (ρ γ) (opm (ρ δ) (e1 : E)) ∈ Vb := by
          rw [opm_apply]
          exact hρU γ _ hmem
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp e2.2) _ hV
      rw [hop]
      simp only [map_add, LinearMap.add_apply, hfirst, zero_add]
      rw [add_comm] }
  refine ⟨c, ?_⟩
  intro γ hc
  exact ofAdd_eq_one.mp hc

private lemma opm_mem_of_coefficient_eq_zero {Γ : Type*} [Group Γ]
    {B : LinearMap.BilinForm K E} (hsymm : B.IsSymm) (hndB : B.Nondegenerate)
    (hrefl : B.IsRefl) {Vb Ub : Submodule K E} (ρ : Γ →* (E ≃ₗ[K] E))
    (hρU : ∀ γ, ∀ e ∈ B.orthogonal Ub, ρ γ e - e ∈ Vb)
    (hΔW : ∀ γ, ∀ e ∈ B.orthogonal Vb, opm (ρ γ) e ∈ Ub)
    (halt : ∀ γ, ∀ w ∈ B.orthogonal Vb, B (opm (ρ γ) w) w = 0)
    {e1 e2 : B.orthogonal Vb}
    (hdecomp : ∀ w : B.orthogonal Vb, ∃ u : B.orthogonal Vb,
      (u : E) ∈ B.orthogonal Ub ∧ ∃ a b : K,
        (w : E) = (u : E) + a • (e1 : E) + b • (e2 : E))
    (hanti : ∀ γ, B (opm (ρ γ) (e2 : E)) (e1 : E) = -B (opm (ρ γ) (e1 : E)) (e2 : E))
    (γ : Γ) (hc0 : B (opm (ρ γ) (e1 : E)) (e2 : E) = 0) :
    ∀ w ∈ B.orthogonal Vb, opm (ρ γ) w ∈ Vb := by
  intro w hw
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hndB hrefl Vb]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro f hf
  rw [hsymm.eq f (opm (ρ γ) w)]
  obtain ⟨u, hu, a, b, hwu⟩ := hdecomp ⟨w, hw⟩
  obtain ⟨u', hu', a', b', hfu⟩ := hdecomp ⟨f, hf⟩
  have hwu' : w = (u : E) + a • (e1 : E) + b • (e2 : E) := hwu
  have hfu' : f = (u' : E) + a' • (e1 : E) + b' • (e2 : E) := hfu
  have hDw : opm (ρ γ) w = opm (ρ γ) (u : E) + a • opm (ρ γ) (e1 : E) +
      b • opm (ρ γ) (e2 : E) := by
    rw [hwu']
    simp only [map_add, map_smul, add_assoc]
  have hΔuV : opm (ρ γ) (u : E) ∈ Vb := by
    rw [opm_apply]
    exact hρU γ _ hu
  have hΔ1U : opm (ρ γ) (e1 : E) ∈ Ub := hΔW γ (e1 : E) e1.2
  have hΔ2U : opm (ρ γ) (e2 : E) ∈ Ub := hΔW γ (e2 : E) e2.2
  have huu : B (opm (ρ γ) (u : E)) (u' : E) = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp u'.2) _ hΔuV
  have hu1 : B (opm (ρ γ) (u : E)) (e1 : E) = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp e1.2) _ hΔuV
  have hu2 : B (opm (ρ γ) (u : E)) (e2 : E) = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp e2.2) _ hΔuV
  have h1u : B (opm (ρ γ) (e1 : E)) (u' : E) = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hu') _ hΔ1U
  have h2u : B (opm (ρ γ) (e2 : E)) (u' : E) = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hu') _ hΔ2U
  have h11 : B (opm (ρ γ) (e1 : E)) (e1 : E) = 0 := halt γ e1 e1.2
  have h22 : B (opm (ρ γ) (e2 : E)) (e2 : E) = 0 := halt γ e2 e2.2
  have h21 : B (opm (ρ γ) (e2 : E)) (e1 : E) = 0 := by
    rw [hanti γ, hc0, neg_zero]
  rw [hDw, hfu']
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    huu, hu1, hu2, h1u, h2u, h11, h22, h21, hc0, smul_zero, add_zero, zero_add, mul_zero]

private lemma isSymm_of_quad {B : LinearMap.BilinForm K E} {Qf : E → K}
    (hQf : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) : B.IsSymm := by
  refine ⟨fun e f => ?_⟩
  rw [bilin_apply_eq_quad_sub hQf e f, bilin_apply_eq_quad_sub hQf f e, add_comm f e]
  ring

theorem exists_hom_sub_mem_of_flag {K E Γ : Type} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Group Γ] (B : LinearMap.BilinForm K E) (Qf : E → K)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQf : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) {Vb Ub : Submodule K E} (hVU : Vb ≤ Ub)
    (hU : ∀ u ∈ Ub, Qf u = 0) (hdim : Module.finrank K Ub = Module.finrank K Vb + 2)
    (ρ : Γ →* (E ≃ₗ[K] E)) (hρQ : ∀ γ e, Qf (ρ γ e) = Qf e)
    (hρV : ∀ γ, ∀ v ∈ Vb, ρ γ v = v)
    (hρU : ∀ γ, ∀ e ∈ B.orthogonal Ub, ρ γ e - e ∈ Vb) :
    ∃ c : Γ →* Multiplicative K, ∀ γ, c γ = 1 → ∀ w ∈ B.orthogonal Vb, ρ γ w - w ∈ Vb := by
  have hsymm : B.IsSymm := isSymm_of_quad hQf
  have hrefl : B.IsRefl := hsymm.isRefl
  have hndB : B.Nondegenerate := hrefl.nondegenerate_iff_separatingLeft.mpr hnd
  have hUorth : Ub ≤ B.orthogonal Ub := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u' hu'
    have h := hQf u u'
    rw [hU u hu, hU u' hu', hU (u + u') (Ub.add_mem hu hu')] at h
    rw [← hsymm.eq u u']
    simpa using h.symm
  obtain ⟨e1, e2, hdecomp⟩ := exists_flag_decomposition (B := B) hndB hVU hdim
  have hΔW : ∀ γ, ∀ e ∈ B.orthogonal Vb, opm (ρ γ) e ∈ Ub :=
    opm_mem_orthogonal_of_mem_orthogonal hndB hrefl hQf ρ hρQ hρV hρU
  have halt : ∀ γ, ∀ w ∈ B.orthogonal Vb, B (opm (ρ γ) w) w = 0 :=
    opm_self_apply_eq_zero hQf hU ρ hρQ hΔW
  have hanti : ∀ γ, B (opm (ρ γ) (e2 : E)) (e1 : E) = -B (opm (ρ γ) (e1 : E)) (e2 : E) :=
    opm_antisymm ρ halt e1 e2
  obtain ⟨c, hc⟩ := exists_flag_coefficient_hom hUorth ρ hρU hΔW e1 e2
  refine ⟨c, ?_⟩
  intro γ hcγ w hw
  have hc0 : B (opm (ρ γ) (e1 : E)) (e2 : E) = 0 := hc γ hcγ
  have h := opm_mem_of_coefficient_eq_zero hsymm hndB hrefl ρ hρU hΔW halt hdecomp hanti γ hc0
  exact h w hw

theorem commutator_apply_sub_mem_of_radical {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (halt : ∀ e, B e e = 0) {Vb : Submodule K E}
    {g h : E ≃ₗ[K] E} (hgB : ∀ e f, B (g e) (g f) = B e f)
    (hhB : ∀ e f, B (h e) (h f) = B e f) (hgV : ∀ v ∈ Vb, g v = v) (hhV : ∀ v ∈ Vb, h v = v)
    (hgW : ∀ w ∈ B.orthogonal Vb, g w - w ∈ Vb) (hhW : ∀ w ∈ B.orthogonal Vb, h w - w ∈ Vb)
    (e : E) : (g * h * g⁻¹ * h⁻¹) e - e ∈ Vb := by
  have hrefl : B.IsRefl := (show B.IsAlt from halt).isRefl
  have hndB : B.Nondegenerate := hrefl.nondegenerate_iff_separatingLeft.mpr hnd
  let W : Submodule K E := B.orthogonal Vb
  have hgi : ∀ w ∈ W, g⁻¹ w - w = -(g w - w) := opm_inv_apply_eq_neg hgV hgW
  have hhi : ∀ w ∈ W, h⁻¹ w - w = -(h w - w) := opm_inv_apply_eq_neg hhV hhW
  have hgiW : ∀ w ∈ W, g⁻¹ w - w ∈ Vb := by
    intro w hw
    rw [hgi w hw]
    exact Vb.neg_mem (hgW w hw)
  have hhiW : ∀ w ∈ W, h⁻¹ w - w ∈ Vb := by
    intro w hw
    rw [hhi w hw]
    exact Vb.neg_mem (hhW w hw)
  have hghV : ∀ v ∈ Vb, (g * h) v = v := fixes_mul hgV hhV
  have hghW : ∀ w ∈ W, (g * h) w - w ∈ Vb := by
    intro w hw
    rw [opm_mul_apply_eq_add hgV hhW w hw]
    exact Vb.add_mem (hgW w hw) (hhW w hw)
  have hghgV : ∀ v ∈ Vb, ((g * h) * g⁻¹) v = v :=
    fixes_mul hghV (fixes_inv hgV)
  have hghgW : ∀ w ∈ W, ((g * h) * g⁻¹) w - w ∈ Vb := by
    intro w hw
    rw [opm_mul_apply_eq_add hghV hgiW w hw]
    exact Vb.add_mem (hghW w hw) (hgiW w hw)
  have hkey : ∀ w ∈ W, (g * h * g⁻¹ * h⁻¹) w - w = 0 := by
    intro w hw
    have h1 := opm_mul_apply_eq_add hghgV hhiW w hw
    have h2 := opm_mul_apply_eq_add hghV hgiW w hw
    have h3 := opm_mul_apply_eq_add hgV hhW w hw
    rw [h1, h2, h3, hgi w hw, hhi w hw]
    abel
  have hfixW : ∀ w ∈ W, (g * h * g⁻¹ * h⁻¹) w = w := by
    intro w hw
    exact sub_eq_zero.mp (hkey w hw)
  have hu : ∀ a b, B ((g * h * g⁻¹ * h⁻¹) a) ((g * h * g⁻¹ * h⁻¹) b) = B a b :=
    isometry_mul (isometry_mul (isometry_mul hgB hhB) (isometry_inv hgB)) (isometry_inv hhB)
  have hlast := sub_mem_orthogonal_of_fixes B (g * h * g⁻¹ * h⁻¹) hu W hfixW e
  rwa [show W = B.orthogonal Vb from rfl,
    LinearMap.BilinForm.orthogonal_orthogonal hndB hrefl Vb] at hlast

theorem sq_apply_sub_mem_of_radical {K E : Type} [Field K] [CharP K 2] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (halt : ∀ e, B e e = 0) {Vb : Submodule K E}
    {g : E ≃ₗ[K] E} (hgB : ∀ e f, B (g e) (g f) = B e f) (hgV : ∀ v ∈ Vb, g v = v)
    (hgW : ∀ w ∈ B.orthogonal Vb, g w - w ∈ Vb) (e : E) : (g * g) e - e ∈ Vb := by
  have hrefl : B.IsRefl := (show B.IsAlt from halt).isRefl
  have hndB : B.Nondegenerate := hrefl.nondegenerate_iff_separatingLeft.mpr hnd
  let W : Submodule K E := B.orthogonal Vb
  have hfixW : ∀ w ∈ W, (g * g) w = w := by
    intro w hw
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hzero : (g w - w) + (g w - w) = 0 := by
      rw [← two_smul K (g w - w), h2, zero_smul]
    have h := opm_mul_apply_eq_add hgV hgW w hw
    rw [hzero] at h
    exact sub_eq_zero.mp h
  have hu : ∀ a b, B ((g * g) a) ((g * g) b) = B a b := isometry_mul hgB hgB
  have hlast := sub_mem_orthogonal_of_fixes B (g * g) hu W hfixW e
  rwa [show W = B.orthogonal Vb from rfl,
    LinearMap.BilinForm.orthogonal_orthogonal hndB hrefl Vb] at hlast

end CFSG.RankThree.GF2n.Stroth80
