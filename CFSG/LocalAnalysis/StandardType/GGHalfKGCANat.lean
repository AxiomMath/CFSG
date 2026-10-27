module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCADefs
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.StandardType

private lemma ggKGCANat_eq_one_of_ne_zero (a : GGKGCF) (ha : a ≠ 0) : a = 1 := by
  have hcard : Nat.card GGKGCF = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  obtain ⟨y, _hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : GGKGCF)).mp hcard
  exact (huniq a ha).trans (huniq 1 one_ne_zero).symm

private noncomputable def ggKGCANat_shear
    {W : Type} [AddCommGroup W] [Module GGKGCF W]
    (v : W) (f : W →ₗ[GGKGCF] GGKGCF) :
    W →ₗ[GGKGCF] W :=
  LinearMap.id + (LinearMap.toSpanSingleton GGKGCF W v).comp f

private lemma ggKGCANat_shear_apply
    {W : Type} [AddCommGroup W] [Module GGKGCF W] [FiniteDimensional GGKGCF W]
    (v : W) (f : W →ₗ[GGKGCF] GGKGCF) (u : W) :
    ggKGCANat_shear v f u = u + f u • v := by
  simp [ggKGCANat_shear, LinearMap.toSpanSingleton_apply]

private lemma ggKGCANat_shear_involutive
    {W : Type} [AddCommGroup W] [Module GGKGCF W] [FiniteDimensional GGKGCF W]
    (v : W) (f : W →ₗ[GGKGCF] GGKGCF) (hv : f v = 0) :
    Function.Involutive (ggKGCANat_shear v f) := by
  intro u
  rw [ggKGCANat_shear_apply, ggKGCANat_shear_apply]
  rw [map_add, map_smul, hv, smul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem ggKGCANat_transitive
    {W : Type} [AddCommGroup W] [Module GGKGCF W] [FiniteDimensional GGKGCF W]
    (w w' : W) (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ∃ g : W ≃ₗ[GGKGCF] W, g w = w' := by
  by_cases hmem : w' ∈ Submodule.span GGKGCF ({w} : Set W)
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact hw' ha.symm
    exact ⟨LinearEquiv.smulOfNeZero GGKGCF W a ha0, by
      rw [LinearEquiv.smulOfNeZero_apply, ha]⟩
  · have hli : LinearIndepOn GGKGCF id ({w, w'} : Set W) := by
      have hs : LinearIndepOn GGKGCF id ({w} : Set W) := LinearIndepOn.singleton hw
      have hx : w' ∉ Submodule.span GGKGCF (id '' ({w} : Set W)) := by
        simpa using hmem
      have := hs.insert hx
      simpa [Set.pair_comm] using this
    obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hli
    have hfw : f w = 1 := hf w (by simp)
    have hfw' : f w' = 1 := hf w' (by simp)
    let d : W := w' - w
    have hfd : f d = 0 := by
      dsimp [d]
      rw [map_sub, hfw', hfw, sub_self]
    have hT : Function.Involutive (ggKGCANat_shear d f) :=
      ggKGCANat_shear_involutive d f hfd
    refine ⟨LinearEquiv.ofInvolutive (ggKGCANat_shear d f) hT, ?_⟩
    show ggKGCANat_shear d f w = w'
    rw [ggKGCANat_shear_apply, hfw, one_smul]
    show w + d = w'
    dsimp [d]
    rw [add_sub_cancel]

theorem ggKGCANat_no_fixed
    {W : Type} [AddCommGroup W] [Module GGKGCF W] [FiniteDimensional GGKGCF W]
    (h2 : 2 ≤ Module.finrank GGKGCF W) (w : W)
    (hw : ∀ g : W ≃ₗ[GGKGCF] W, g w = w) : w = 0 := by
  by_contra hw0
  have hspan : Submodule.span GGKGCF ({w} : Set W) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    by_cases hv : v = 0
    · rw [hv]; exact Submodule.zero_mem _
    · obtain ⟨g, hg⟩ := ggKGCANat_transitive w v hw0 hv
      rw [← hg, hw g]
      exact Submodule.mem_span_singleton_self w
  have hfr : Module.finrank GGKGCF W = 1 := by
    rw [← finrank_top GGKGCF W, ← hspan, finrank_span_singleton hw0]
  omega

theorem ggKGCANat_center
    {W : Type} [AddCommGroup W] [Module GGKGCF W] [FiniteDimensional GGKGCF W]
    (g : W ≃ₗ[GGKGCF] W) (hg : ∀ h : W ≃ₗ[GGKGCF] W, g * h = h * g) :
    g = 1 := by
  ext v
  change g v = v
  by_cases hv : v = 0
  · rw [hv]; simp
  · by_contra hne
    have hnotmem : g v ∉ Submodule.span GGKGCF ({v} : Set W) := by
      intro hmem
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        have hgv : g v ≠ 0 := by
          intro h0
          exact hv (g.injective (by rw [h0, map_zero]))
        exact hgv ha.symm
      have ha1 : a = 1 := ggKGCANat_eq_one_of_ne_zero a ha0
      exact hne (by rw [← ha, ha1, one_smul])
    obtain ⟨f, hfgv, hle⟩ := Submodule.exists_le_ker_of_notMem hnotmem
    have hfv : f v = 0 := by
      have hmem := hle (Submodule.mem_span_singleton_self v)
      rwa [LinearMap.mem_ker] at hmem
    let h : W ≃ₗ[GGKGCF] W := LinearEquiv.ofInvolutive (ggKGCANat_shear v f)
      (ggKGCANat_shear_involutive v f hfv)
    have hfix : h v = v := by
      show ggKGCANat_shear v f v = v
      rw [ggKGCANat_shear_apply, hfv, zero_smul, add_zero]
    have hhy : h (g v) ≠ g v := by
      show ggKGCANat_shear v f (g v) ≠ g v
      rw [ggKGCANat_shear_apply]
      intro hcon
      have hc : f (g v) • v = 0 := by
        have hsub : g v + f (g v) • v - g v = 0 := by rw [hcon, sub_self]
        simpa only [add_sub_cancel_left] using hsub
      exact (smul_ne_zero hfgv hv) hc
    have hcomm := congrArg (fun e : W ≃ₗ[GGKGCF] W => e v) (hg h)
    simp only [LinearEquiv.mul_apply] at hcomm
    rw [hfix] at hcomm
    exact hhy hcomm.symm

end CFSG.StandardType

end
