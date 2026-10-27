module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private lemma ggQ2gw_h_coroot {p : ℕ} [Fact p.Prime] {D : GGQ2Lin p} {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (h : D.V ≃ₗ[ZMod p] D.V)
    (hchain : ∀ i : Fin m, 1 ≤ (i : ℕ) → (i : ℕ) + 3 ≤ m →
      h (D.coroot (e i)) = D.coroot (e i))
    (hm2 : h (D.coroot (e ⟨m - 2, by omega⟩)) = D.coroot (e ⟨m - 1, by omega⟩))
    (hm1 : h (D.coroot (e ⟨m - 1, by omega⟩)) = D.coroot (e ⟨m - 2, by omega⟩))
    (ha : D.a = e ⟨0, by omega⟩) :
    ∀ i : D.ι, i ≠ D.a →
      h (D.coroot i) =
        D.coroot (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i) := by
  intro i hi
  obtain ⟨j, rfl⟩ := e.surjective i
  have hjm : (j : ℕ) < m := j.isLt
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hj
    apply hi
    rw [ha]
    congr 1
    exact Fin.ext hj
  have hj1 : 1 ≤ (j : ℕ) := by omega
  by_cases hj2 : (j : ℕ) = m - 2
  · have hjeq : j = ⟨m - 2, by omega⟩ := Fin.ext hj2
    rw [hjeq, Equiv.swap_apply_left]
    exact hm2
  · by_cases hj1' : (j : ℕ) = m - 1
    · have hjeq : j = ⟨m - 1, by omega⟩ := Fin.ext hj1'
      rw [hjeq, Equiv.swap_apply_right]
      exact hm1
    · have hjle : (j : ℕ) + 3 ≤ m := by omega
      have hne2 : e j ≠ e ⟨m - 2, by omega⟩ := fun hh => hj2 (congrArg Fin.val (e.injective hh))
      have hne1 : e j ≠ e ⟨m - 1, by omega⟩ := fun hh => hj1' (congrArg Fin.val (e.injective hh))
      rw [Equiv.swap_apply_of_ne_of_ne hne2 hne1]
      exact hchain j hj1 hjle

theorem ggQ2g_swap_stable {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (D : GGQ2Lin p) (hbas : D.Basis)
    {m : ℕ} (hm : 5 ≤ m) (e : Fin m ≃ D.ι)
    (he : D.coxeter = (ggCoxeterMatrixD m).reindex e) (ha : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {x})
    (hV : Submodule.span (ZMod p)
      (insert x (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) = ⊤)
    {T : D.V →ₗ[ZMod p] D.V} {c μ₀ : ZMod p} {w : D.V ≃ₗ[ZMod p] D.V}
    (hw : w ∈ D.parab {k | k ≠ D.a})
    (hT : ∀ i : D.ι, i ≠ D.a → T (D.coroot i) = c • μ₀ • w (D.coroot
      (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i)))
    (hTx : T x ∈ Submodule.span (ZMod p) {x}) :
    ∃ w' ∈ D.weyl, ∀ y : D.V, ∀ v ∈ Submodule.span (ZMod p) {x, y},
      w' (T v) ∈ Submodule.span (ZMod p) {x, y} := by
  classical
  obtain ⟨h, hh, hxh, hchain, hfm2, hfm1⟩ :=
    ggQ2_D_swap_element hp2 D hbas hm e he ha x hx
  let w' : D.V ≃ₗ[ZMod p] D.V := h⁻¹ * w⁻¹
  have hparab_le_weyl : D.parab {k | k ≠ D.a} ≤ D.weyl :=
    Subgroup.closure_mono (Set.image_mono (Set.subset_univ _))
  have hwx : w x = x := (hx x).mpr (Submodule.subset_span (Set.mem_singleton x)) w hw
  have hw_weyl : w ∈ D.weyl := hparab_le_weyl hw
  have hw'weyl : w' ∈ D.weyl := by
    change h⁻¹ * w⁻¹ ∈ D.weyl
    exact D.weyl.mul_mem (D.weyl.inv_mem hh) (D.weyl.inv_mem hw_weyl)
  have hw'w : ∀ v : D.V, w' (w v) = h⁻¹ v := by
    intro v
    change (h⁻¹ * w⁻¹) (w v) = h⁻¹ v
    rw [LinearEquiv.mul_apply]
    show h⁻¹ (w.symm (w v)) = h⁻¹ v
    rw [LinearEquiv.symm_apply_apply]
  have hw'x : w' x = -x := by
    have hw1x : w⁻¹ x = x := by
      calc w⁻¹ x = w⁻¹ (w x) := by rw [hwx]
        _ = x := LinearEquiv.symm_apply_apply w x
    have hh1x : h⁻¹ x = -x := by
      have h2 : h (-x) = x := by rw [map_neg, hxh, neg_neg]
      calc h⁻¹ x = h⁻¹ (h (-x)) := by rw [h2]
        _ = -x := LinearEquiv.symm_apply_apply h (-x)
    change (h⁻¹ * w⁻¹) x = -x
    rw [LinearEquiv.mul_apply, hw1x, hh1x]
  have hcoroot : ∀ i : D.ι, i ≠ D.a →
      h (D.coroot i) = D.coroot (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i) :=
    ggQ2gw_h_coroot hm e h hchain hfm2 hfm1 ha
  have hcor : ∀ i : D.ι, i ≠ D.a → w' (T (D.coroot i)) = c • μ₀ • D.coroot i := by
    intro i hi
    have hhinv : h⁻¹ (D.coroot (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i))
        = D.coroot i := by
      rw [← hcoroot i hi]
      exact LinearEquiv.symm_apply_apply h (D.coroot i)
    calc w' (T (D.coroot i))
        = w' (c • μ₀ •
            w (D.coroot (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i))) := by
          rw [hT i hi]
      _ = c • μ₀ •
            w' (w (D.coroot (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i))) := by
          rw [map_smul, map_smul]
      _ = c • μ₀ •
            h⁻¹ (D.coroot (Equiv.swap (e ⟨m - 2, by omega⟩) (e ⟨m - 1, by omega⟩) i)) := by
          rw [hw'w]
      _ = c • μ₀ • D.coroot i := by rw [hhinv]
  have hspan : ∀ u ∈ Submodule.span (ZMod p)
      (Set.range fun i : {k // k ≠ D.a} => D.coroot (i : D.ι)),
      w' (T u) = c • μ₀ • u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro v ⟨i, rfl⟩
      exact hcor i i.2
    · simp
    · intro a b _ _ iha ihb
      rw [map_add, map_add, iha, ihb, smul_add, smul_add]
    · intro r a _ ih
      rw [map_smul, map_smul, ih]
      simp only [smul_smul]
      rw [show r * (c * μ₀) = c * (μ₀ * r) by ring]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hTx
  have hTx' : w' (T x) = (-t) • x := by
    rw [← ht, map_smul, hw'x, smul_neg]
    exact (neg_smul t x).symm
  refine ⟨w', hw'weyl, ?_⟩
  intro y v hv
  have hy_mem : y ∈ Submodule.span (ZMod p)
      (insert x (Set.range fun i : {k // k ≠ D.a} => D.coroot (i : D.ι))) := by
    rw [hV]
    exact Submodule.mem_top
  obtain ⟨s, u, hu_mem, hy_eq⟩ := Submodule.mem_span_insert.mp hy_mem
  have hu_xy : u ∈ Submodule.span (ZMod p) ({x, y} : Set D.V) := by
    have hu : u = y - s • x := by rw [hy_eq]; abel
    rw [hu]
    exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hTy_mem : w' (T y) ∈ Submodule.span (ZMod p) ({x, y} : Set D.V) := by
    have hTyeq : w' (T y) = s • ((-t) • x) + c • μ₀ • u := by
      rw [hy_eq]
      simp only [map_add, map_smul]
      rw [hTx', hspan u hu_mem]
    rw [hTyeq]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hu_xy)
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hv
  rw [← hαβ]
  have hcomp : w' (T (α • x + β • y)) = α • ((-t) • x) + β • w' (T y) := by
    simp only [map_add, map_smul]
    rw [hTx']
  rw [hcomp]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · exact Submodule.smul_mem _ _ hTy_mem

end CFSG.StandardType

end
