module

public import CFSG.RankThree.Classical.TransvectionReciprocalPair
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.RankThree.Classical

open Module

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

section Setting

variable {H : Subgroup (V ≃ₗ[F] V)} {v w z : V}
  (hli : LinearIndependent F ![v, w, z])
  (hspan : Submodule.span F (Set.range ![v, w, z]) = ⊤)
  (hext : ∀ φ : Submodule.span F {v, w} →ₗ[F] Submodule.span F {v, w},
    LinearMap.det φ = 1 → ∃ h ∈ H, (∀ u : Submodule.span F {v, w}, h (u : V) = (φ u : V)) ∧
      h z = z)

noncomputable def basis3 : Basis (Fin 3) F V :=
  Basis.mk hli (by rw [hspan])

theorem basis3_apply (i : Fin 3) : basis3 hli hspan i = ![v, w, z] i :=
  Basis.mk_apply _ _ _

include hli in
theorem pair_li : LinearIndependent F ![v, w] := by
  have := hli.comp (fun i : Fin 2 => (Fin.castSucc i : Fin 3)) (Fin.castSucc_injective 2)
  convert this using 1
  ext i
  fin_cases i <;> rfl

noncomputable def zstar : Dual F V := (basis3 hli hspan).coord 2

theorem zstar_v : zstar hli hspan v = 0 := by
  have : zstar hli hspan v = zstar hli hspan (basis3 hli hspan 0) := by rw [basis3_apply]; rfl
  rw [this, zstar, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]

theorem zstar_w : zstar hli hspan w = 0 := by
  have : zstar hli hspan w = zstar hli hspan (basis3 hli hspan 1) := by rw [basis3_apply]; rfl
  rw [this, zstar, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]

theorem zstar_z : zstar hli hspan z = 1 := by
  have : zstar hli hspan z = zstar hli hspan (basis3 hli hspan 2) := by rw [basis3_apply]; rfl
  rw [this, zstar, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

theorem zstar_pair (α β : F) : zstar hli hspan (α • v + β • w) = 0 := by
  rw [map_add, map_smul, map_smul, zstar_v, zstar_w, smul_zero, smul_zero, add_zero]

include hli hspan in
theorem exists_coords (x : V) : ∃ α β γ : F, x = α • v + β • w + γ • z := by
  refine ⟨(basis3 hli hspan).repr x 0, (basis3 hli hspan).repr x 1,
    (basis3 hli hspan).repr x 2, ?_⟩
  conv_lhs => rw [← (basis3 hli hspan).sum_repr x]
  rw [Fin.sum_univ_three, basis3_apply, basis3_apply, basis3_apply]
  rfl

noncomputable def pairBasisF {v w : V} (hvw : LinearIndependent F ![v, w]) :
    Basis (Fin 2) F (Submodule.span F {v, w}) :=
  Basis.mk (v := ![⟨v, Submodule.subset_span (by simp)⟩, ⟨w, Submodule.subset_span (by simp)⟩])
    (LinearIndependent.of_comp (Submodule.span F {v, w}).subtype (by
      convert hvw using 1
      ext i
      fin_cases i <;> rfl))
    (by
      rintro ⟨x, hx⟩ -
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
      have : (⟨a • v + b • w, hx⟩ : Submodule.span F {v, w}) =
          a • (⟨v, Submodule.subset_span (by simp)⟩ : Submodule.span F {v, w}) +
            b • ⟨w, Submodule.subset_span (by simp)⟩ := rfl
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))

theorem coe_pairBasisF_zero {v w : V} (hvw : LinearIndependent F ![v, w]) :
    (pairBasisF hvw 0 : V) = v := by
  rw [pairBasisF, Basis.mk_apply]
  rfl

theorem coe_pairBasisF_one {v w : V} (hvw : LinearIndependent F ![v, w]) :
    (pairBasisF hvw 1 : V) = w := by
  rw [pairBasisF, Basis.mk_apply]
  rfl

include hli hext in
theorem exists_mem_mat (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) :
    ∃ h ∈ H, h v = M 0 0 • v + M 1 0 • w ∧ h w = M 0 1 • v + M 1 1 • w ∧ h z = z := by
  set B := pairBasisF (pair_li hli)
  obtain ⟨h, hh, hU, hz⟩ := hext (Matrix.toLin B B M) (by rw [LinearMap.det_toLin, hM])
  refine ⟨h, hh, ?_, ?_, hz⟩
  · have := hU (B 0)
    rw [coe_pairBasisF_zero, Matrix.toLin_self, Fin.sum_univ_two] at this
    rw [this, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, coe_pairBasisF_zero,
      coe_pairBasisF_one]
  · have := hU (B 1)
    rw [coe_pairBasisF_one, Matrix.toLin_self, Fin.sum_univ_two] at this
    rw [this, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, coe_pairBasisF_zero,
      coe_pairBasisF_one]

theorem zstar_comp {h : V ≃ₗ[F] V} (hv : ∃ α β : F, h v = α • v + β • w)
    (hw : ∃ α β : F, h w = α • v + β • w) (hz : h z = z) (x : V) :
    zstar hli hspan (h x) = zstar hli hspan x := by
  obtain ⟨α, β, γ, rfl⟩ := exists_coords hli hspan x
  obtain ⟨a, b, ha⟩ := hv
  obtain ⟨c, d, hc⟩ := hw
  simp only [map_add, map_smul, ha, hc, hz, zstar_v, zstar_w, zstar_z, smul_zero, add_zero,
    zero_add]

end Setting

section Roots

variable {v w z : V} (hli : LinearIndependent F ![v, w, z])
  (hspan : Submodule.span F (Set.range ![v, w, z]) = ⊤)

@[expose] noncomputable def up (u : V) (hu : zstar hli hspan u = 0) : V ≃ₗ[F] V :=
  LinearEquiv.transvection hu

@[expose] noncomputable def lo (z : V) (ψ : Dual F V) (hψ : ψ z = 0) : V ≃ₗ[F] V :=
  LinearEquiv.transvection hψ

theorem up_apply (u : V) (hu : zstar hli hspan u = 0) (x : V) :
    up hli hspan u hu x = x + zstar hli hspan x • u :=
  rfl

theorem lo_apply (ψ : Dual F V) (hψ : ψ z = 0) (x : V) : lo z ψ hψ x = x + ψ x • z :=
  rfl

theorem up_mul_up (u u' : V) (hu : zstar hli hspan u = 0) (hu' : zstar hli hspan u' = 0) :
    up hli hspan u hu * up hli hspan u' hu' =
      up hli hspan (u + u') (by rw [map_add, hu, hu', add_zero]) := by
  ext x
  rw [LinearEquiv.mul_apply, up_apply, up_apply, up_apply, map_add, map_smul, hu', smul_zero,
    add_zero, smul_add]
  abel

theorem lo_mul_lo (ψ ψ' : Dual F V) (hψ : ψ z = 0) (hψ' : ψ' z = 0) :
    lo z ψ hψ * lo z ψ' hψ' = lo z (ψ + ψ') (by rw [LinearMap.add_apply, hψ, hψ', add_zero]) := by
  ext x
  rw [LinearEquiv.mul_apply, lo_apply, lo_apply, lo_apply, map_add, map_smul, hψ, smul_zero,
    add_zero, LinearMap.add_apply, add_smul]
  abel

theorem conj_up {h : V ≃ₗ[F] V} (hz : ∀ x, zstar hli hspan (h x) = zstar hli hspan x)
    (u : V) (hu : zstar hli hspan u = 0) :
    h * up hli hspan u hu * h⁻¹ = up hli hspan (h u) (by rw [hz, hu]) := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, up_apply, up_apply, map_add, map_smul]
  change h (h.symm x) + zstar hli hspan (h.symm x) • h u = x + zstar hli hspan x • h u
  rw [LinearEquiv.apply_symm_apply, ← hz (h.symm x), LinearEquiv.apply_symm_apply]

theorem symm_apply_of_apply_eq {h : V ≃ₗ[F] V} (hz : h z = z) : h.symm z = z := by
  rw [LinearEquiv.symm_apply_eq]
  exact hz.symm

theorem conj_lo {h : V ≃ₗ[F] V} (hz : h z = z) (ψ : Dual F V) (hψ : ψ z = 0) :
    h * lo z ψ hψ * h⁻¹ = lo z (ψ.comp (h.symm : V →ₗ[F] V)) (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, symm_apply_of_apply_eq hz, hψ]) := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, lo_apply, lo_apply, map_add, map_smul, hz]
  change h (h.symm x) + ψ (h.symm x) • z = x + ψ (h.symm x) • z
  rw [LinearEquiv.apply_symm_apply]

theorem up_congr {u u' : V} (hu : zstar hli hspan u = 0) (huu' : u = u') :
    up hli hspan u hu = up hli hspan u' (huu' ▸ hu) := by
  subst huu'
  rfl

theorem lo_congr {ψ ψ' : Dual F V} (hψ : ψ z = 0) (hψψ' : ψ = ψ') :
    lo z ψ hψ = lo z ψ' (hψψ' ▸ hψ) := by
  subst hψψ'
  rfl

theorem up_zero : up hli hspan 0 (map_zero _) = 1 := by
  ext x
  rw [up_apply, smul_zero, add_zero]
  rfl

theorem lo_zero : lo z (0 : Dual F V) rfl = 1 := by
  ext x
  rw [lo_apply, LinearMap.zero_apply, zero_smul, add_zero]
  rfl

end Roots

section Transitivity

variable {H : Subgroup (V ≃ₗ[F] V)} {v w z : V}
  (hli : LinearIndependent F ![v, w, z])
  (hspan : Submodule.span F (Set.range ![v, w, z]) = ⊤)
  (hext : ∀ φ : Submodule.span F {v, w} →ₗ[F] Submodule.span F {v, w},
    LinearMap.det φ = 1 → ∃ h ∈ H, (∀ u : Submodule.span F {v, w}, h (u : V) = (φ u : V)) ∧
      h z = z)

include hli hspan hext in
theorem exists_mem_apply_v_eq {α β : F} (hαβ : α ≠ 0 ∨ β ≠ 0) :
    ∃ h ∈ H, h v = α • v + β • w ∧ (∀ x, zstar hli hspan (h x) = zstar hli hspan x) ∧
      h z = z := by
  have key : ∀ M : Matrix (Fin 2) (Fin 2) F, M.det = 1 → M 0 0 = α → M 1 0 = β →
      ∃ h ∈ H, h v = α • v + β • w ∧ (∀ x, zstar hli hspan (h x) = zstar hli hspan x) ∧
        h z = z := by
    intro M hM h0 h1
    obtain ⟨h, hh, hv, hw, hz⟩ := exists_mem_mat hli hext M hM
    exact ⟨h, hh, by rw [hv, h0, h1], zstar_comp hli hspan ⟨_, _, hv⟩ ⟨_, _, hw⟩ hz, hz⟩
  by_cases hα : α ≠ 0
  · exact key !![α, 0; β, α⁻¹] (by simp [Matrix.det_fin_two, hα]) rfl rfl
  · have hβ : β ≠ 0 := hαβ.resolve_left hα
    push Not at hα
    exact key !![0, -β⁻¹; β, 0] (by simp [Matrix.det_fin_two, hβ]) (by simp [hα]) rfl

include hli hspan hext in
theorem up_mem_of_up_mem {α₀ β₀ : F} (h0 : α₀ ≠ 0 ∨ β₀ ≠ 0)
    (hmem : up hli hspan (α₀ • v + β₀ • w) (zstar_pair hli hspan α₀ β₀) ∈ H) (α β : F) :
    up hli hspan (α • v + β • w) (zstar_pair hli hspan α β) ∈ H := by
  obtain ⟨h₀, hh₀, hv₀, hz₀, -⟩ := exists_mem_apply_v_eq hli hspan hext h0
  have hinv : ∀ x, zstar hli hspan (h₀⁻¹ x) = zstar hli hspan x := fun x => by
    rw [← hz₀ (h₀⁻¹ x)]
    change zstar hli hspan (h₀ (h₀.symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hv : up hli hspan v (zstar_v hli hspan) ∈ H := by
    have := H.mul_mem (H.mul_mem (H.inv_mem hh₀) hmem) (H.inv_mem (H.inv_mem hh₀))
    rw [conj_up hli hspan hinv] at this
    rwa [up_congr hli hspan _ (show h₀⁻¹ (α₀ • v + β₀ • w) = v by
      rw [← hv₀]; exact LinearEquiv.symm_apply_apply h₀ v)] at this
  by_cases hαβ : α ≠ 0 ∨ β ≠ 0
  · obtain ⟨h₁, hh₁, hv₁, hz₁, -⟩ := exists_mem_apply_v_eq hli hspan hext hαβ
    have := H.mul_mem (H.mul_mem hh₁ hv) (H.inv_mem hh₁)
    rw [conj_up hli hspan hz₁] at this
    rwa [up_congr hli hspan _ hv₁] at this
  · push Not at hαβ
    obtain ⟨rfl, rfl⟩ := hαβ
    rw [up_congr hli hspan _ (show (0 : F) • v + (0 : F) • w = 0 by simp), up_zero]
    exact H.one_mem

noncomputable def vstar : Dual F V := (basis3 hli hspan).coord 0

theorem vstar_v : vstar hli hspan v = 1 := by
  have : vstar hli hspan v = vstar hli hspan (basis3 hli hspan 0) := by rw [basis3_apply]; rfl
  rw [this, vstar, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

theorem vstar_w : vstar hli hspan w = 0 := by
  have : vstar hli hspan w = vstar hli hspan (basis3 hli hspan 1) := by rw [basis3_apply]; rfl
  rw [this, vstar, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]

theorem vstar_z : vstar hli hspan z = 0 := by
  have : vstar hli hspan z = vstar hli hspan (basis3 hli hspan 2) := by rw [basis3_apply]; rfl
  rw [this, vstar, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]

include hli hspan in
theorem dual_ext {ψ ψ' : Dual F V} (hv : ψ v = ψ' v) (hw : ψ w = ψ' w) (hz : ψ z = ψ' z) :
    ψ = ψ' := by
  refine (basis3 hli hspan).ext fun i => ?_
  fin_cases i <;> simp [basis3_apply, hv, hw, hz]

include hli hspan hext in
theorem exists_mem_comp_eq_vstar {ψ : Dual F V} (hψz : ψ z = 0) (hψ : ψ ≠ 0) :
    ∃ h ∈ H, h z = z ∧ ψ.comp (h : V →ₗ[F] V) = vstar hli hspan := by
  have hne : ψ v ≠ 0 ∨ ψ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hψ (dual_ext hli hspan (by rw [hcon.1]; rfl) (by rw [hcon.2]; rfl) (by rw [hψz]; rfl))
  by_cases h0 : ψ v ≠ 0
  · obtain ⟨h, hh, hv, hw, hz⟩ := exists_mem_mat hli hext !![(ψ v)⁻¹, -ψ w; 0, ψ v]
      (by simp [Matrix.det_fin_two, h0])
    refine ⟨h, hh, hz, dual_ext hli hspan ?_ ?_ ?_⟩
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hv, vstar_v]
      simp [h0]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hw, vstar_w]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, map_add, map_smul, smul_eq_mul]
      ring
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hz, hψz, vstar_z]
  · push Not at h0
    have h1 : ψ w ≠ 0 := hne.resolve_left (not_not.mpr h0)
    obtain ⟨h, hh, hv, hw, hz⟩ := exists_mem_mat hli hext !![0, -ψ w; (ψ w)⁻¹, 0]
      (by simp [Matrix.det_fin_two, h1])
    refine ⟨h, hh, hz, dual_ext hli hspan ?_ ?_ ?_⟩
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hv, vstar_v]
      simp [h1]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hw, vstar_w]
      simp [h0]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hz, hψz, vstar_z]

include hli hspan hext in
theorem lo_mem_of_lo_mem {ψ₀ : Dual F V} (hψ₀z : ψ₀ z = 0) (hψ₀ : ψ₀ ≠ 0)
    (hmem : lo z ψ₀ hψ₀z ∈ H) (ψ : Dual F V) (hψz : ψ z = 0) : lo z ψ hψz ∈ H := by
  obtain ⟨h₀, hh₀, hz₀, hcomp₀⟩ := exists_mem_comp_eq_vstar hli hspan hext hψ₀z hψ₀
  have hzinv : h₀⁻¹ z = z := symm_apply_of_apply_eq hz₀
  have hv : lo z (vstar hli hspan) (vstar_z hli hspan) ∈ H := by
    have := H.mul_mem (H.mul_mem (H.inv_mem hh₀) hmem) (H.inv_mem (H.inv_mem hh₀))
    rw [conj_lo hzinv] at this
    rwa [lo_congr _ (show ψ₀.comp ((h₀⁻¹).symm : V →ₗ[F] V) = vstar hli hspan by
      rw [← hcomp₀]; rfl)] at this
  by_cases hψ : ψ = 0
  · subst hψ
    rw [lo_zero]
    exact H.one_mem
  · obtain ⟨h₁, hh₁, hz₁, hcomp₁⟩ := exists_mem_comp_eq_vstar hli hspan hext hψz hψ
    have := H.mul_mem (H.mul_mem hh₁ hv) (H.inv_mem hh₁)
    rw [conj_lo hz₁] at this
    rwa [lo_congr _ (show (vstar hli hspan).comp (h₁.symm : V →ₗ[F] V) = ψ by
      rw [← hcomp₁]
      ext x
      change ψ (h₁ (h₁.symm x)) = ψ x
      rw [LinearEquiv.apply_symm_apply])] at this

end Transitivity

section Cases

variable {H : Subgroup (V ≃ₗ[F] V)} {v w z : V}
  (hli : LinearIndependent F ![v, w, z])
  (hspan : Submodule.span F (Set.range ![v, w, z]) = ⊤)
  (hext : ∀ φ : Submodule.span F {v, w} →ₗ[F] Submodule.span F {v, w},
    LinearMap.det φ = 1 → ∃ h ∈ H, (∀ u : Submodule.span F {v, w}, h (u : V) = (φ u : V)) ∧
      h z = z)

theorem exists_pair_of_zstar {x : V} (hx : zstar hli hspan x = 0) :
    ∃ α β : F, x = α • v + β • w := by
  obtain ⟨α, β, γ, rfl⟩ := exists_coords hli hspan x
  have hγ : γ = 0 := by
    have := hx
    simp only [map_add, map_smul, zstar_v, zstar_w, zstar_z, smul_eq_mul, mul_zero, mul_one,
      zero_add] at this
    exact this
  exact ⟨α, β, by rw [hγ, zero_smul, add_zero]⟩

theorem transvection_symm_apply {c : V} {ψ : Dual F V} (h : ψ c = 0) (x : V) :
    (LinearEquiv.transvection h).symm x = x - ψ x • c := by
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.transvection.apply, map_sub, map_smul, h,
    smul_eq_mul, mul_zero, sub_zero, sub_add_cancel]

theorem IsTransvectionWith.conj {τ : V ≃ₗ[F] V} {c : V} {ψ : Dual F V}
    (ht : IsTransvectionWith τ c ψ) (σ : V ≃ₗ[F] V) :
    IsTransvectionWith (σ * τ * σ⁻¹) (σ c) (ψ.comp (σ.symm : V →ₗ[F] V)) := by
  refine ⟨fun h0 => ht.1 (by simpa using h0), fun h0 => ht.2.1 ?_, ?_, fun x => ?_⟩
  · ext x
    have := congrArg (fun χ : Dual F V => χ (σ x)) h0
    simpa using this
  · simp [ht.2.2.1]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht.2.2.2, map_add, map_smul]
    change σ (σ.symm x) + ψ (σ.symm x) • σ c = x + ψ (σ.symm x) • σ c
    rw [LinearEquiv.apply_symm_apply]

include hext in
theorem transvection_mem {c' : V} {χ : Dual F V} (hc' : zstar hli hspan c' = 0)
    (hχz : χ z = 0) (hχc : χ c' = 0) : LinearEquiv.transvection hχc ∈ H := by
  have : Module.Finite F V := Module.Finite.of_basis (basis3 hli hspan)
  obtain ⟨α, β, hc⟩ := exists_pair_of_zstar hli hspan hc'
  have hcU : c' ∈ Submodule.span F {v, w} := hc ▸ Submodule.mem_span_pair.mpr ⟨α, β, rfl⟩
  set φ : Submodule.span F {v, w} →ₗ[F] Submodule.span F {v, w} :=
    LinearMap.transvection (χ.comp (Submodule.span F {v, w}).subtype) ⟨c', hcU⟩
  have hdet : LinearMap.det φ = 1 := by
    rw [LinearMap.transvection.det]
    simp [hχc]
  obtain ⟨h, hh, hU, hz⟩ := hext φ hdet
  convert hh using 1
  refine (basis3 hli hspan).ext' fun i => ?_
  rw [LinearEquiv.transvection.apply]
  fin_cases i
  · have := hU ⟨v, Submodule.subset_span (by simp)⟩
    simp only [basis3_apply, Fin.zero_eta, Matrix.cons_val_zero]
    rw [this]
    rfl
  · have := hU ⟨w, Submodule.subset_span (by simp)⟩
    simp only [basis3_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [this]
    rfl
  · simp only [basis3_apply]
    change z + χ z • c' = h z
    rw [hχz, zero_smul, add_zero, hz]

include hext in
theorem exists_lo_of_case_a {τ : V ≃ₗ[F] V} {c : V} {ψ : Dual F V} (hτ : τ ∈ H)
    (ht : IsTransvectionWith τ c ψ) (hb : ψ z = 0) (ha : zstar hli hspan c ≠ 0) :
    ∃ χ : Dual F V, ∃ hχ : χ z = 0, χ ≠ 0 ∧ lo z χ hχ ∈ H := by
  set a := zstar hli hspan c
  set cU := c - a • z
  have hcU : zstar hli hspan cU = 0 := by
    simp only [cU, map_sub, map_smul, zstar_z, smul_eq_mul, mul_one]
    exact sub_self _
  have hψcU : ψ cU = 0 := by
    simp only [cU, map_sub, map_smul, ht.2.2.1, hb, smul_eq_mul, mul_zero, sub_self]
  have hk := transvection_mem hli hspan hext hcU hb hψcU
  have hχ : (a • ψ) z = 0 := by rw [LinearMap.smul_apply, hb, smul_zero]
  refine ⟨a • ψ, hχ, smul_ne_zero ha ht.2.1, ?_⟩
  have heq : τ * (LinearEquiv.transvection hψcU)⁻¹ = lo z (a • ψ) hχ := by
    ext x
    rw [LinearEquiv.mul_apply, lo_apply]
    change τ ((LinearEquiv.transvection hψcU).symm x) = _
    rw [transvection_symm_apply, ht.2.2.2, map_sub, map_smul, hψcU, smul_eq_mul, mul_zero,
      sub_zero, LinearMap.smul_apply, smul_eq_mul]
    simp only [cU]
    module
  rw [← heq]
  exact H.mul_mem hτ (H.inv_mem hk)

include hext in
theorem exists_up_of_case_b {τ : V ≃ₗ[F] V} {c : V} {ψ : Dual F V} (hτ : τ ∈ H)
    (ht : IsTransvectionWith τ c ψ) (ha : zstar hli hspan c = 0) (hb : ψ z ≠ 0) :
    ∃ α β : F, (α ≠ 0 ∨ β ≠ 0) ∧ up hli hspan (α • v + β • w) (zstar_pair hli hspan α β) ∈ H := by
  set b := ψ z
  set ψU := ψ - b • zstar hli hspan
  have hψUz : ψU z = 0 := by
    simp only [ψU, LinearMap.sub_apply, LinearMap.smul_apply, zstar_z, smul_eq_mul, mul_one]
    exact sub_self _
  have hψUc : ψU c = 0 := by
    simp only [ψU, LinearMap.sub_apply, LinearMap.smul_apply, ha, ht.2.2.1, smul_zero, sub_zero]
  have hk := transvection_mem hli hspan hext ha hψUz hψUc
  obtain ⟨α, β, hc⟩ := exists_pair_of_zstar hli hspan ha
  have hαβ : α ≠ 0 ∨ β ≠ 0 := by
    by_contra h0
    push Not at h0
    apply ht.1
    rw [hc, h0.1, h0.2, zero_smul, zero_smul, add_zero]
  refine ⟨b * α, b * β, ?_, ?_⟩
  · rcases hαβ with h | h
    · exact Or.inl (mul_ne_zero hb h)
    · exact Or.inr (mul_ne_zero hb h)
  have heq : τ * (LinearEquiv.transvection hψUc)⁻¹ =
      up hli hspan ((b * α) • v + (b * β) • w) (zstar_pair hli hspan _ _) := by
    ext x
    rw [LinearEquiv.mul_apply, up_apply]
    change τ ((LinearEquiv.transvection hψUc).symm x) = _
    rw [transvection_symm_apply, ht.2.2.2, map_sub, map_smul, ht.2.2.1, smul_eq_mul, mul_zero,
      sub_zero]
    simp only [ψU, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hc]
    module
  rw [← heq]
  exact H.mul_mem hτ (H.inv_mem hk)

include hext in
theorem exists_up_of_case_c {τ : V ≃ₗ[F] V} {c : V} {ψ : Dual F V} (hτ : τ ∈ H)
    (ht : IsTransvectionWith τ c ψ) (ha : zstar hli hspan c ≠ 0) (hb : ψ z ≠ 0) :
    ∃ α β : F, (α ≠ 0 ∨ β ≠ 0) ∧ up hli hspan (α • v + β • w) (zstar_pair hli hspan α β) ∈ H := by
  set a := zstar hli hspan c
  set b := ψ z
  set ψU := ψ - b • zstar hli hspan
  have hψU : ∀ x, ψU x = ψ x - b * zstar hli hspan x := fun x => by
    simp only [ψU, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hψUz : ψU z = 0 := by rw [hψU, zstar_z, mul_one]; exact sub_self _
  obtain ⟨α₀, β₀, hcU⟩ := exists_pair_of_zstar hli hspan (x := c - a • z) (by
    simp only [map_sub, map_smul, zstar_z, smul_eq_mul, mul_one]; exact sub_self _)
  have hψUcU : ψU (c - a • z) = -(a * b) := by
    rw [hψU, map_sub, map_smul, ht.2.2.1, map_sub, map_smul, zstar_z]
    simp only [smul_eq_mul, mul_one]
    ring
  have hne : ψU v ≠ 0 ∨ ψU w ≠ 0 := by
    by_contra h0
    push Not at h0
    have : ψU (c - a • z) = 0 := by
      rw [hcU, map_add, map_smul, map_smul, h0.1, h0.2, smul_zero, smul_zero, add_zero]
    rw [hψUcU, neg_eq_zero] at this
    exact mul_ne_zero ha hb this
  set w₀ := ψU w • v - ψU v • w
  have hw₀ : ψU w₀ = 0 := by
    simp only [w₀, map_sub, map_smul, smul_eq_mul]
    ring
  have hzw₀ : zstar hli hspan w₀ = 0 := by
    simp only [w₀, map_sub, map_smul, zstar_v, zstar_w, smul_zero, sub_self]
  have hψw₀ : ψ w₀ = 0 := by
    have := hψU w₀
    rw [hw₀, hzw₀, mul_zero, sub_zero] at this
    exact this.symm
  set μ := ψU c
  have hk := transvection_mem hli hspan hext hzw₀ hψUz hw₀
  have hμw₀ : ψU (μ • w₀) = 0 := by rw [map_smul, hw₀, smul_zero]
  have hzμw₀ : zstar hli hspan (μ • w₀) = 0 := by rw [map_smul, hzw₀, smul_zero]
  have hk₂ := transvection_mem hli hspan hext hzμw₀ hψUz hμw₀
  have hprod : LinearEquiv.transvection hw₀ * τ * (LinearEquiv.transvection hw₀)⁻¹ * τ⁻¹ *
      (LinearEquiv.transvection hμw₀)⁻¹ =
      up hli hspan ((μ * b * ψU w) • v + (-(μ * b * ψU v)) • w) (zstar_pair hli hspan _ _) := by
    ext x
    simp only [LinearEquiv.mul_apply, up_apply]
    change LinearEquiv.transvection hw₀ (τ ((LinearEquiv.transvection hw₀).symm
      (τ.symm ((LinearEquiv.transvection hμw₀).symm x)))) = _
    have hτsymm : ∀ y, τ.symm y = y - ψ y • c := ht.inv_apply
    rw [transvection_symm_apply, hτsymm, transvection_symm_apply, ht.2.2.2,
      LinearEquiv.transvection.apply]
    simp only [w₀, μ, hψU, map_add, map_sub, map_smul, smul_eq_mul, ht.2.2.1, zstar_v, zstar_w,
      mul_zero, sub_zero]
    module
  refine ⟨μ * b * ψU w, -(μ * b * ψU v), ?_, ?_⟩
  · have hμ : μ ≠ 0 := by
      have : μ = ψU (c - a • z) := by rw [map_sub, map_smul, hψUz, smul_zero, sub_zero]
      rw [this, hψUcU]
      exact neg_ne_zero.mpr (mul_ne_zero ha hb)
    rcases hne with h | h
    · exact Or.inr (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hμ hb) h))
    · exact Or.inl (mul_ne_zero (mul_ne_zero hμ hb) h)
  · rw [← hprod]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hk hτ) (H.inv_mem hk)) (H.inv_mem hτ))
      (H.inv_mem hk₂)

include hext in
theorem exists_lo_of_case_c
    (hup : ∀ α β : F, up hli hspan (α • v + β • w) (zstar_pair hli hspan α β) ∈ H)
    {τ : V ≃ₗ[F] V} {c : V} {ψ : Dual F V} (hτ : τ ∈ H)
    (ht : IsTransvectionWith τ c ψ) (ha : zstar hli hspan c ≠ 0) (hb : ψ z ≠ 0) :
    ∃ χ : Dual F V, ∃ hχ : χ z = 0, χ ≠ 0 ∧ lo z χ hχ ∈ H := by
  set b := ψ z
  set ψU := ψ - b • zstar hli hspan
  have hψU : ∀ x, ψU x = ψ x - b * zstar hli hspan x := fun x => by
    simp only [ψU, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨α, β, hu₀⟩ : ∃ α β : F, ψ (α • v + β • w) = b := by
    obtain ⟨α₀, β₀, hcU⟩ := exists_pair_of_zstar hli hspan
      (x := c - zstar hli hspan c • z) (by
        simp only [map_sub, map_smul, zstar_z, smul_eq_mul, mul_one]; exact sub_self _)
    have hne : ψ v ≠ 0 ∨ ψ w ≠ 0 := by
      by_contra h0
      push Not at h0
      have h1 : ψ (c - zstar hli hspan c • z) = 0 := by
        rw [hcU, map_add, map_smul, map_smul, h0.1, h0.2, smul_zero, smul_zero, add_zero]
      rw [map_sub, map_smul, ht.2.2.1, zero_sub, neg_eq_zero, smul_eq_mul] at h1
      exact mul_ne_zero ha hb h1
    rcases hne with h | h
    · exact ⟨b / ψ v, 0, by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
        div_mul_cancel₀ _ h, zero_mul, add_zero]⟩
    · exact ⟨0, b / ψ w, by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
        div_mul_cancel₀ _ h, zero_mul, zero_add]⟩
  set σ := up hli hspan (α • v + β • w) (zstar_pair hli hspan α β)
  have hσ := hup α β
  have ht' := ht.conj σ
  have hform : ψ.comp (σ.symm : V →ₗ[F] V) = ψU := by
    ext x
    change ψ (σ.symm x) = ψU x
    rw [show σ.symm x = x - zstar hli hspan x • (α • v + β • w) from
      transvection_symm_apply _ x, map_sub, map_smul, hu₀, hψU, smul_eq_mul, mul_comm]
  have hψUz : ψU z = 0 := by rw [hψU, zstar_z, mul_one]; exact sub_self _
  rw [hform] at ht'
  refine exists_lo_of_case_a hli hspan hext (H.mul_mem (H.mul_mem hσ hτ) (H.inv_mem hσ)) ht'
    hψUz ?_
  rw [up_apply, map_add, map_smul, zstar_pair, smul_zero, add_zero]
  exact ha

end Cases

section Main

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem invariant_of_generators {H : Subgroup (V ≃ₗ[ZMod p] V)} {S : Set (V ≃ₗ[ZMod p] V)}
    (hHS : H = Subgroup.closure S) {W : Submodule (ZMod p) V}
    (hW : ∀ t ∈ S, ∀ x ∈ W, t x ∈ W ∧ t⁻¹ x ∈ W) : ∀ h ∈ H, ∀ x ∈ W, h x ∈ W := by
  intro h hh
  rw [hHS] at hh
  refine Subgroup.closure_induction'' (p := fun h _ => ∀ x ∈ W, h x ∈ W) ?_ ?_ ?_ ?_ hh
  · exact fun t ht x hx => (hW t ht x hx).1
  · exact fun t ht x hx => (hW t ht x hx).2
  · exact fun x hx => hx
  · intro a b _ _ ha hb x hx
    rw [LinearEquiv.mul_apply]
    exact ha _ (hb x hx)

noncomputable def slAct (b : Basis (Fin 3) (ZMod p) V) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod p) →* (V ≃ₗ[ZMod p] V) where
  toFun A := Matrix.toLinearEquiv b A (by rw [A.2]; exact isUnit_one)
  map_one' := LinearEquiv.ext fun x => by
    rw [Matrix.toLinearEquiv_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin_one]
    rfl
  map_mul' A B := LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, Matrix.toLinearEquiv_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin_mul b b b]
    rfl

theorem slAct_apply_basis (b : Basis (Fin 3) (ZMod p) V)
    (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) (k : Fin 3) :
    slAct b A (b k) = ∑ l, (A : Matrix (Fin 3) (Fin 3) (ZMod p)) l k • b l := by
  rw [show slAct b A (b k) = Matrix.toLin b b (A : Matrix (Fin 3) (Fin 3) (ZMod p)) (b k) from
    rfl, Matrix.toLin_self]

theorem prime_three_space_irreducible_transvection_generation [FiniteDimensional (ZMod p) V]
    (hV : Module.finrank (ZMod p) V = 3) (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hSL : ∀ h ∈ H, LinearMap.det (h : V →ₗ[ZMod p] V) = 1)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S) :
    ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ LinearMap.det (g : V →ₗ[ZMod p] V) = 1 := by
  obtain ⟨S, hS, hHS⟩ := hgen
  have hmemS : ∀ t ∈ S, t ∈ H := fun t ht => hHS ▸ Subgroup.subset_closure ht
  have hSne : S.Nonempty := by
    by_contra hS0
    rw [Set.not_nonempty_iff_eq_empty] at hS0
    have hH : H = ⊥ := by rw [hHS, hS0, Subgroup.closure_empty]
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hV]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    rcases hirr (Submodule.span (ZMod p) {x}) (fun h hh y hy => by
        rw [hH, Subgroup.mem_bot] at hh
        rw [hh]
        exact hy) with h | h
    · exact hx (Submodule.span_singleton_eq_bot.mp h)
    · have := finrank_span_singleton (K := ZMod p) hx
      rw [h, finrank_top, hV] at this
      omega
  obtain ⟨t₁, t₂, v, w, f, g, ht₁, ht₂, h₁, h₂, hfg, hcompl, hext⟩ :=
    prime_three_space_transvection_reciprocal_pair hV H hSL hirr ⟨S, hSne, hS, hHS⟩
  have hfw : f w ≠ 0 := left_ne_zero_of_mul hfg
  have hvw : LinearIndependent (ZMod p) ![v, w] := LinearIndependent.pair_iff.mpr fun s t hst => by
    have hf := congrArg f hst
    rw [map_add, map_smul, map_smul, h₁.2.2.1, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
      map_zero] at hf
    have ht : t = 0 := (mul_eq_zero.mp hf).resolve_right hfw
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right h₁.1, ht⟩
  have hU2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v, w}) = 2 := by
    have := finrank_span_eq_card hvw
    rw [Fintype.card_fin] at this
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.union_singleton, Set.pair_comm] at this
    exact this
  have hL1 := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hU2, hV] at hL1
  obtain ⟨zL, hzL0, hzL⟩ := (finrank_eq_one_iff' (K := ZMod p)
    (V := ↥(LinearMap.ker f ⊓ LinearMap.ker g))).mp (by omega)
  set z : V := (zL : V)
  have hz0 : z ≠ 0 := fun h0 => hzL0 (Subtype.ext h0)
  have hzL' : z ∈ LinearMap.ker f ⊓ LinearMap.ker g := zL.2
  have hli : LinearIndependent (ZMod p) ![v, w, z] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hc
    have hmem : c 2 • z ∈ Submodule.span (ZMod p) {v, w} ⊓ (LinearMap.ker f ⊓ LinearMap.ker g) := by
      refine Submodule.mem_inf.mpr ⟨?_, Submodule.smul_mem _ _ hzL'⟩
      have : c 2 • z = -(c 0 • v + c 1 • w) := eq_neg_of_add_eq_zero_right hc
      rw [this]
      exact Submodule.neg_mem _ (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩)
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
    have h2 : c 2 = 0 := (smul_eq_zero.mp hmem).resolve_right hz0
    rw [h2, zero_smul, add_zero] at hc
    have h01 := LinearIndependent.pair_iff.mp hvw (c 0) (c 1) hc
    intro i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2
  have hspan : Submodule.span (ZMod p) (Set.range ![v, w, z]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hV])
  have hext' : ∀ φ : Submodule.span (ZMod p) {v, w} →ₗ[ZMod p] Submodule.span (ZMod p) {v, w},
      LinearMap.det φ = 1 → ∃ h ∈ H,
        (∀ u : Submodule.span (ZMod p) {v, w}, h (u : V) = (φ u : V)) ∧ h z = z := by
    intro φ hφ
    obtain ⟨h, hh, hU, hL⟩ := hext φ hφ
    exact ⟨h, hh, hU, hL z hzL'⟩
  set zs := zstar hli hspan
  have hgen_z : ∃ t ∈ S, ∃ c ψ, IsTransvectionWith t c ψ ∧ ψ z ≠ 0 := by
    by_contra hno
    push Not at hno
    have hinv := invariant_of_generators hHS (W := Submodule.span (ZMod p) {z}) fun t ht x hx => by
      obtain ⟨c, ψ, hcψ⟩ := hS t ht
      have hψz := hno t ht c ψ hcψ
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
      refine ⟨?_, ?_⟩
      · rw [map_smul, hcψ.2.2.2, hψz, zero_smul, add_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
      · rw [map_smul, hcψ.inv_apply, hψz, zero_smul, sub_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
    rcases hirr _ hinv with h | h
    · exact hz0 (Submodule.span_singleton_eq_bot.mp h)
    · have := finrank_span_singleton (K := ZMod p) hz0
      rw [h, finrank_top, hV] at this
      omega
  have hgen_c : ∃ t ∈ S, ∃ c ψ, IsTransvectionWith t c ψ ∧ zs c ≠ 0 := by
    by_contra hno
    push Not at hno
    have hinv := invariant_of_generators hHS (W := LinearMap.ker zs) fun t ht x hx => by
      obtain ⟨c, ψ, hcψ⟩ := hS t ht
      have hzc := hno t ht c ψ hcψ
      rw [LinearMap.mem_ker] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [hcψ.2.2.2, map_add, map_smul, hzc, smul_zero, add_zero, hx]
      · rw [LinearMap.mem_ker, hcψ.inv_apply, map_sub, map_smul, hzc, smul_zero]
        exact (sub_zero _).trans hx
    rcases hirr _ hinv with h | h
    · have hv : v ∈ LinearMap.ker zs := zstar_v hli hspan
      rw [h, Submodule.mem_bot] at hv
      exact h₁.1 hv
    · have hz : z ∈ LinearMap.ker zs := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hz
      exact one_ne_zero ((zstar_z hli hspan).symm.trans hz)
  obtain ⟨t, htS, c, ψ, ht, hψz⟩ := hgen_z
  have hupper : ∃ α β : ZMod p, (α ≠ 0 ∨ β ≠ 0) ∧
      up hli hspan (α • v + β • w) (zstar_pair hli hspan α β) ∈ H := by
    by_cases ha : zs c = 0
    · exact exists_up_of_case_b hli hspan hext' (hmemS t htS) ht ha hψz
    · exact exists_up_of_case_c hli hspan hext' (hmemS t htS) ht ha hψz
  obtain ⟨α₀, β₀, hαβ₀, hup₀⟩ := hupper
  have hup := up_mem_of_up_mem hli hspan hext' hαβ₀ hup₀
  obtain ⟨t', ht'S, c', ψ', ht', hzc'⟩ := hgen_c
  have hlower : ∃ χ : Dual (ZMod p) V, ∃ hχ : χ z = 0, χ ≠ 0 ∧ lo z χ hχ ∈ H := by
    by_cases hb : ψ' z = 0
    · exact exists_lo_of_case_a hli hspan hext' (hmemS t' ht'S) ht' hb hzc'
    · exact exists_lo_of_case_c hli hspan hext' hup (hmemS t' ht'S) ht' hzc' hb
  obtain ⟨χ₀, hχ₀z, hχ₀, hlo₀⟩ := hlower
  have hlo := lo_mem_of_lo_mem hli hspan hext' hχ₀z hχ₀ hlo₀
  set bV := basis3 hli hspan
  have hbV : ∀ k, bV k = ![v, w, z] k := basis3_apply hli hspan
  have hcoord : ∀ j : Fin 3, j ≠ 2 → bV.coord j z = 0 := fun j hj => by
    rw [show z = bV 2 by rw [hbV]; rfl, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_of_ne hj]
  have hzsb : ∀ i : Fin 3, i ≠ 2 → zs (bV i) = 0 := fun i hi => by
    rw [hbV]
    fin_cases i
    · exact zstar_v hli hspan
    · exact zstar_w hli hspan
    · exact absurd rfl hi
  have hEmem : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod p),
      slAct bV (Matrix.SpecialLinearGroup.transvection hij c) ∈ H := by
    intro i j hij c
    have hform : ∀ x, slAct bV (Matrix.SpecialLinearGroup.transvection hij c) x =
        x + (c • bV.coord j) x • bV i := by
      intro x
      have hlin : (slAct bV (Matrix.SpecialLinearGroup.transvection hij c) : V →ₗ[ZMod p] V) =
          LinearMap.transvection (c • bV.coord j) (bV i) := by
        refine bV.ext fun k => ?_
        rw [LinearEquiv.coe_coe, slAct_apply_basis, LinearMap.transvection.apply,
          CFSG.LinearGroups.coe_transvection, LinearMap.smul_apply, Basis.coord_apply,
          Basis.repr_self, smul_eq_mul]
        simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
          Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        by_cases hk : k = j
        · subst hk
          simp
        · simp [Ne.symm hk]
      exact congrArg (fun φ : V →ₗ[ZMod p] V => φ x) hlin
    by_cases hj : j = 2
    ·
      subst hj
      have hi : i ≠ 2 := hij
      obtain ⟨α, β, hαβ⟩ := exists_pair_of_zstar hli hspan (x := c • bV i)
        (by rw [map_smul, hzsb i hi, smul_zero])
      have := hup α β
      convert this using 1
      ext x
      rw [hform, up_apply, ← hαβ, LinearMap.smul_apply, smul_eq_mul, mul_smul, smul_comm]
      rfl
    · by_cases hi : i = 2
      ·
        subst hi
        have := hlo (c • bV.coord j) (by rw [LinearMap.smul_apply, hcoord j hj, smul_zero])
        convert this using 1
        ext x
        rw [hform, lo_apply]
        simp only [show bV 2 = z by rw [hbV]; rfl]
      ·
        have hmem := transvection_mem hli hspan hext' (c' := bV i) (χ := c • bV.coord j)
          (hzsb i hi) (by rw [LinearMap.smul_apply, hcoord j hj, smul_zero])
          (by rw [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self,
            Finsupp.single_eq_of_ne (Ne.symm hij), smul_zero])
        convert hmem using 1
        ext x
        rw [hform, LinearEquiv.transvection.apply]
  have hall : ∀ A, slAct bV A ∈ H := by
    intro A
    have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 (ZMod p)) ≤
        H.comap (slAct bV) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      exact hEmem i j hij c
    rw [CFSG.LinearGroups.special_linear_elementary_generation] at hle
    exact hle (Subgroup.mem_top A)
  intro g'
  refine ⟨hSL g', fun hdet => ?_⟩
  have hA : (LinearMap.toMatrix bV bV (g' : V →ₗ[ZMod p] V)).det = 1 := by
    rw [LinearMap.det_toMatrix, hdet]
  have := hall ⟨_, hA⟩
  convert this using 1
  ext x
  change g' x = Matrix.toLin bV bV (LinearMap.toMatrix bV bV (g' : V →ₗ[ZMod p] V)) x
  rw [Matrix.toLin_toMatrix]
  rfl

end Main

end CFSG.RankThree.Classical
