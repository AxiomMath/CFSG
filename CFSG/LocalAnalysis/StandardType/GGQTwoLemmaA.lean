module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private theorem ggQ2la_refl_fixes {p : ℕ} [Fact p.Prime] {D : GGQ2Lin p} {v : D.V}
    (hv : ∀ j : {k // k ≠ D.a}, D.root j v = 0) (k : D.ι) (hk : k ≠ D.a) :
    D.simpleRefl k v = v := by
  show (Module.reflection (D.root_coroot_self k)) v = v
  rw [Module.reflection_apply]
  rw [show D.root k v = 0 from hv ⟨k, hk⟩, zero_smul, sub_zero]

private theorem ggQ2la_parab_fixes {p : ℕ} [Fact p.Prime] {D : GGQ2Lin p} {v : D.V}
    (hv : ∀ j : {k // k ≠ D.a}, D.root j v = 0) :
    ∀ w : D.V ≃ₗ[ZMod p] D.V, w ∈ D.parab {k | k ≠ D.a} → w v = v := by
  intro w hw
  have key : ∀ g ∈ D.parab {k | k ≠ D.a}, g v = v := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨k, hk, rfl⟩ := hx
        exact ggQ2la_refl_fixes hv k hk
    | one => rfl
    | mul x y hx hy ihx ihy =>
        rw [LinearEquiv.mul_apply, ihy, ihx]
    | inv x hx ih =>
        simpa only [LinearEquiv.coe_inv] using
          (LinearEquiv.symm_apply_eq (e := x)).mpr ih.symm
  exact key w hw

theorem ggQ2_lemmaA {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (xV yV : D.V)
    (hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0)
    (hyα : ∀ j : {k // k ≠ D.b}, D.root j yV = 0)
    (hV : Submodule.span (ZMod p)
      (insert xV (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) = ⊤)
    (hdet : ((D.cartan.submatrix (fun i : {k // k ≠ D.a} => (i : D.ι))
      (fun i : {k // k ≠ D.a} => (i : D.ι))).det : ZMod p) ≠ 0)
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod p}
    (hπ : D.ScaledAut D.a π μ) (hπb : π ⟨D.b, D.a_ne_b.symm⟩ = ⟨D.b, D.a_ne_b.symm⟩)
    {T : D.V →ₗ[ZMod p] D.V} {c : ZMod p} {w : D.V ≃ₗ[ZMod p] D.V}
    (hw : w ∈ D.parab {k | k ≠ D.a})
    (hT : ∀ i : {k // k ≠ D.a}, T (D.coroot i) = c • μ i • w (D.coroot (π i)))
    (hTx : T xV ∈ Submodule.span (ZMod p) {xV}) :
    ∃ w' ∈ D.parab {k | k ≠ D.a}, ∀ v ∈ Submodule.span (ZMod p) {xV, yV},
      w' (T v) ∈ Submodule.span (ZMod p) {xV, yV} := by
  classical
  let Λ := {k // k ≠ D.a}
  let bΛ : Λ := ⟨D.b, D.a_ne_b.symm⟩
  let C : Matrix Λ Λ (ZMod p) := fun i j => (D.cartan (i : D.ι) (j : D.ι) : ZMod p)
  have hC_apply : ∀ i j : Λ, C i j = (D.cartan (i : D.ι) (j : D.ι) : ZMod p) :=
    fun i j => rfl
  have hCeq : C = (Int.castRingHom (ZMod p)).mapMatrix
      (D.cartan.submatrix (fun i : Λ => (i : D.ι)) (fun i : Λ => (i : D.ι))) := by
    rw [RingHom.mapMatrix_apply]
    ext i j
    rfl
  have hCdet : IsUnit C.det := by
    rw [isUnit_iff_ne_zero]
    have hM : C.det = ((D.cartan.submatrix (fun i : Λ => (i : D.ι))
        (fun i : Λ => (i : D.ι))).det : ZMod p) := by
      rw [hCeq, ← RingHom.map_det]
      rfl
    rw [hM]
    exact hdet
  have hCunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hCdet
  have hCinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  have hinj : Function.Injective C.mulVec :=
    (Matrix.mulVec_injective_iff_isUnit).mpr hCunit
  let e : Λ → ZMod p := Pi.single bΛ 1
  let ω : Λ → ZMod p := C⁻¹.mulVec e
  let hω : D.V := ∑ i, ω i • D.coroot (i : D.ι)
  have hCω : C.mulVec ω = e := by
    show C.mulVec (C⁻¹.mulVec e) = e
    rw [Matrix.mulVec_mulVec, hCinv, Matrix.one_mulVec]
  have key : ∀ n : Λ → ZMod p, (∀ j : Λ, j ≠ bΛ → (C.mulVec n) j = 0) →
      n = ((C.mulVec n) bΛ) • ω := by
    intro n hn
    apply hinj
    have h3 : C.mulVec (((C.mulVec n) bΛ) • ω) = ((C.mulVec n) bΛ) • e := by
      rw [Matrix.mulVec_smul, hCω]
    have h4 : C.mulVec n = ((C.mulVec n) bΛ) • e := by
      funext j
      by_cases hj : j = bΛ
      · subst hj
        simp [e]
      · rw [hn j hj]
        simp [e, Pi.single_eq_of_ne hj]
    exact h4.trans h3.symm
  have hyV_mem : yV ∈ Submodule.span (ZMod p)
      (insert xV (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) := by
    rw [hV]
    exact Submodule.mem_top
  obtain ⟨s, u, hu_mem, hyV_eq⟩ := Submodule.mem_span_insert.mp hyV_mem
  obtain ⟨n, hn_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hu_mem
  have hroot : ∀ j : Λ, j ≠ bΛ → (C.mulVec n) j = 0 := by
    intro j hj
    have h1 : D.root (j : D.ι) u = (C.mulVec n) j := by
      rw [← hn_eq, Matrix.mulVec_apply_eq_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, D.pairing, hC_apply, smul_eq_mul, mul_comm]
    have h2 : D.root (j : D.ι) u = 0 := by
      have hy : D.root (j : D.ι) yV = 0 := by
        simpa using hyα ⟨(j : D.ι), fun h => hj (Subtype.ext h)⟩
      have hx : D.root (j : D.ι) xV = 0 := by
        simpa using hxα j
      have huv : u = yV - s • xV := by rw [hyV_eq]; abel
      rw [huv, map_sub, map_smul, hy, hx, smul_zero]
      abel
    rw [← h1, h2]
  have hn'' : ∀ i : Λ, n i = ((C.mulVec n) bΛ) * ω i := by
    intro i
    have h := congrFun (key n hroot) i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hnu : u = ((C.mulVec n) bΛ) • hω := by
    calc u = ∑ i, n i • D.coroot (i : D.ι) := hn_eq.symm
      _ = ∑ i, (((C.mulVec n) bΛ) * ω i) • D.coroot (i : D.ι) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hn'' i]
      _ = ((C.mulVec n) bΛ) • ∑ i, ω i • D.coroot (i : D.ι) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_smul]
      _ = ((C.mulVec n) bΛ) • hω := rfl
  have humem : u ∈ Submodule.span (ZMod p) ({xV, yV} : Set D.V) := by
    have huv : u = yV - s • xV := by rw [hyV_eq]; abel
    rw [huv]
    exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  let nhat : Λ → ZMod p := fun l => μ (π.symm l) * n (π.symm l)
  have hmul : ∀ k : Λ, (C.mulVec nhat) (π k) = μ k * (C.mulVec n) k := by
    intro k
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    rw [← Equiv.sum_comp π (fun l => C (π k) l * nhat l)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hni : nhat (π i) = μ i * n i := by
      show μ (π.symm (π i)) * n (π.symm (π i)) = μ i * n i
      rw [Equiv.symm_apply_apply]
    rw [hni]
    have hki : C (π k) (π i) * μ i = μ k * C k i := by
      have h := hπ.2 k i
      rw [hC_apply, hC_apply]
      rw [mul_comm (μ i)] at h
      exact h.symm
    calc C (π k) (π i) * (μ i * n i)
        = (C (π k) (π i) * μ i) * n i := (mul_assoc _ _ _).symm
      _ = (μ k * C k i) * n i := by rw [hki]
      _ = μ k * (C k i * n i) := mul_assoc _ _ _
  have hroot_hat : ∀ j : Λ, j ≠ bΛ → (C.mulVec nhat) j = 0 := by
    intro j hj
    have hk : π.symm j ≠ bΛ := by
      intro h
      apply hj
      rw [← π.apply_symm_apply j, h, hπb]
    have h := hmul (π.symm j)
    rw [π.apply_symm_apply] at h
    rw [h, hroot (π.symm j) hk, mul_zero]
  have hsum : (∑ i : Λ, n i • μ i • D.coroot ((π i : Λ) : D.ι))
      = ∑ l : Λ, nhat l • D.coroot (l : D.ι) := by
    rw [← Equiv.sum_comp π (fun l => nhat l • D.coroot (l : D.ι))]
    apply Finset.sum_congr rfl
    intro i _
    have hni : nhat (π i) = μ i * n i := by
      show μ (π.symm (π i)) * n (π.symm (π i)) = μ i * n i
      rw [Equiv.symm_apply_apply]
    rw [hni, smul_smul, mul_comm (n i) (μ i)]
  have hnhat'' : ∀ l : Λ, nhat l = ((C.mulVec nhat) bΛ) * ω l := by
    intro l
    have h := congrFun (key nhat hroot_hat) l
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hr : (∑ i : Λ, n i • μ i • D.coroot ((π i : Λ) : D.ι))
      = ((C.mulVec nhat) bΛ) • hω := by
    rw [hsum]
    calc (∑ l : Λ, nhat l • D.coroot (l : D.ι))
        = ∑ l : Λ, (((C.mulVec nhat) bΛ) * ω l) • D.coroot (l : D.ι) := by
            apply Finset.sum_congr rfl
            intro l _
            rw [hnhat'' l]
      _ = ((C.mulVec nhat) bΛ) • ∑ l : Λ, ω l • D.coroot (l : D.ι) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro l _
            rw [mul_smul]
      _ = ((C.mulVec nhat) bΛ) • hω := rfl
  have hTwr : T u = c • w (∑ i : Λ, n i • μ i • D.coroot ((π i : Λ) : D.ι)) := by
    calc T u = ∑ i : Λ, T (n i • D.coroot (i : D.ι)) := by
                rw [← hn_eq, map_sum]
      _ = ∑ i : Λ, n i • (c • μ i • w (D.coroot ((π i : Λ) : D.ι))) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [map_smul, hT i]
      _ = c • w (∑ i : Λ, n i • μ i • D.coroot ((π i : Λ) : D.ι)) := by
                rw [map_sum, Finset.smul_sum]
                apply Finset.sum_congr rfl
                intro i _
                simp only [map_smul, smul_smul]
                congr 1
                ring
  have hTu : T u = (c * ((C.mulVec nhat) bΛ)) • w hω := by
    rw [hTwr, hr, map_smul, smul_smul]
  have hwx : w⁻¹ xV = xV := ggQ2la_parab_fixes hxα w⁻¹ (Subgroup.inv_mem _ hw)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hTx
  have hTx' : w⁻¹ (T xV) = t • xV := by
    rw [← ht, map_smul, hwx]
  have hw'Tu : w⁻¹ (T u) ∈ Submodule.span (ZMod p) {xV, yV} := by
    by_cases hκ : (C.mulVec n) bΛ = 0
    · have hu0 : u = 0 := by rw [hnu, hκ, zero_smul]
      rw [hu0, map_zero, map_zero]
      exact Submodule.zero_mem _
    · have hωmem : hω ∈ Submodule.span (ZMod p) {xV, yV} := by
        have hh : hω = ((C.mulVec n) bΛ)⁻¹ • u := by
          rw [hnu, smul_smul, inv_mul_cancel₀ hκ, one_smul]
        rw [hh]
        exact Submodule.smul_mem _ _ humem
      have h1 : w⁻¹ (T u) = (c * ((C.mulVec nhat) bΛ)) • hω := by
        rw [hTu, LinearEquiv.coe_inv, map_smul, LinearEquiv.symm_apply_apply]
      rw [h1]
      exact Submodule.smul_mem _ _ hωmem
  refine ⟨w⁻¹, Subgroup.inv_mem _ hw, ?_⟩
  intro v hv
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hv
  rw [← hαβ]
  have hdecomp : α • xV + β • yV = (α + β * s) • xV + β • u := by
    rw [hyV_eq, smul_add, smul_smul, add_smul]
    abel
  rw [hdecomp]
  have hTA : T ((α + β * s) • xV + β • u) = (α + β * s) • T xV + β • T u := by
    rw [map_add, map_smul, map_smul]
  have hwA : w⁻¹ (T ((α + β * s) • xV + β • u))
      = (α + β * s) • (t • xV) + β • w⁻¹ (T u) := by
    rw [hTA, map_add, map_smul, map_smul, hTx']
  rw [hwA]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ hw'Tu)

end CFSG.StandardType

end
