module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigHeart
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeSixNeg
import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2TN6_case1_apply (w : V ≃ₗ[ZMod 3] V) (f : Module.Dual (ZMod 3) V)
    (c₀ : V) (hfc : f c₀ = 2) (hw : w c₀ = -c₀) (v : V) :
    (Module.reflection hfc * (w * Module.reflection hfc * w⁻¹)) v
      = v - (f v + f (w.symm v)) • c₀ := by
  have hinner : w (Module.reflection hfc (w⁻¹ v)) = v + f (w.symm v) • c₀ := by
    rw [Module.reflection_apply, map_sub, map_smul, LinearEquiv.coe_inv]
    rw [LinearEquiv.apply_symm_apply, hw, smul_neg, sub_neg_eq_add]
  calc
    (Module.reflection hfc * (w * Module.reflection hfc * w⁻¹)) v
        = Module.reflection hfc (w (Module.reflection hfc (w⁻¹ v))) := by
          simp only [LinearEquiv.mul_apply]
    _ = Module.reflection hfc (v + f (w.symm v) • c₀) := by rw [hinner]
    _ = (v + f (w.symm v) • c₀) - f (v + f (w.symm v) • c₀) • c₀ := by
          rw [Module.reflection_apply]
    _ = v - (f v + f (w.symm v)) • c₀ := by
          rw [map_add, map_smul, smul_eq_mul, hfc]
          module

private theorem ggQ2TN6_case2_apply (s : V ≃ₗ[ZMod 3] V) (α : Module.Dual (ZMod 3) V)
    (c : V) (f : Module.Dual (ZMod 3) V) (c₀ : V) (hfc : f c₀ = 2)
    (hs : ∀ v, s v = v - α v • c) (hαc : α c = 2) (hfc0 : f c = 0) (v : V) :
    (Module.reflection hfc * s * Module.reflection hfc * s) v
      = v + (α c₀ * f v) • c := by
  simp only [LinearEquiv.mul_apply, Module.reflection_apply, hs, map_sub, map_smul,
    hfc, hαc, hfc0, zero_smul, sub_zero]
  module

theorem ggQ2TN6_absIrred [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (hdim : Module.finrank (ZMod 3) V = 5) (c : Fin 5 → V)
    (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hxH : x ∉ Submodule.span (ZMod 3) (Set.range c)) (hxfix : ∀ i, α i x = 0)
    (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (htR : IsReflLin t)
    (htx : t x ∉ Submodule.span (ZMod 3) {x}) :
    ZS.AbsIrred 3 (Subgroup.closure (Set.range s ∪ {t})) := by
  classical
  obtain ⟨c₀, f, hfc, rfl⟩ := htR
  have hfx : f x ≠ 0 := by
    intro hf0
    apply htx
    rw [Module.reflection_apply, hf0, zero_smul, sub_zero]
    exact Submodule.mem_span_singleton_self x
  have hc₀x : c₀ ∉ Submodule.span (ZMod 3) {x} := by
    intro hc0
    apply htx
    rw [Module.reflection_apply]
    exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self x)
      (Submodule.smul_mem _ _ hc0)
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    have h2 := hfc
    rw [h0, map_zero] at h2
    exact absurd h2 (by decide : ¬(0 : ZMod 3) = 2)
  have hαc : ∀ i, α i (c i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hcne : ∀ i, c i ≠ 0 := by
    intro i h0
    have h2 := hαc i
    rw [h0, map_zero] at h2
    exact absurd h2 (by decide : ¬(0 : ZMod 3) = 2)
  obtain ⟨-, hsup, hker, hfix⟩ := ggQ2TN_heart hdim c α hpair x hxH hxfix
  have hconn := ggQ2TN_conn c α hpair
  have hfix_closure : ∀ w ∈ Subgroup.closure (Set.range s), w x = x := by
    intro w hw
    refine Subgroup.closure_induction (p := fun g _ => g x = x) ?_ rfl ?_ ?_ hw
    · rintro g ⟨i, rfl⟩
      rw [hs i x, hxfix i, zero_smul, sub_zero]
    · intro a b _ _ ha hb
      rw [LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      change a.symm x = x
      rw [LinearEquiv.symm_apply_eq, ha]
  by_cases hc₀H : c₀ ∈ Submodule.span (ZMod 3) (Set.range c)
  ·
    exfalso
    have hdep : c 0 + (2 : ZMod 3) • c 1 + c 3 + (2 : ZMod 3) • c 4 = 0 := by
      apply hker
      · have h0 : c (0 : Fin 5) ∈ Submodule.span (ZMod 3) (Set.range c) :=
          Submodule.subset_span (Set.mem_range_self (0 : Fin 5))
        have h1 : c (1 : Fin 5) ∈ Submodule.span (ZMod 3) (Set.range c) :=
          Submodule.subset_span (Set.mem_range_self (1 : Fin 5))
        have h3 : c (3 : Fin 5) ∈ Submodule.span (ZMod 3) (Set.range c) :=
          Submodule.subset_span (Set.mem_range_self (3 : Fin 5))
        have h4 : c (4 : Fin 5) ∈ Submodule.span (ZMod 3) (Set.range c) :=
          Submodule.subset_span (Set.mem_range_self (4 : Fin 5))
        exact Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.add_mem _ h0 (Submodule.smul_mem _ _ h1)) h3)
          (Submodule.smul_mem _ _ h4)
      · intro i
        fin_cases i <;> simp [hpair, CartanMatrix.A] <;> decide
    obtain ⟨w, hwmem, hwneg⟩ := ggQ2TN6_neg c α hpair s hs hdep c₀ hc₀H
    have hwA : w ∈ A := by
      refine Subgroup.closure_induction (p := fun g _ => g ∈ A) ?_ A.one_mem ?_ ?_ hwmem
      · rintro g ⟨i, rfl⟩
        exact hsA i
      · intro a b _ _ ha hb
        exact A.mul_mem ha hb
      · intro a _ ha
        exact A.inv_mem ha
    have hwx : w x = x := hfix_closure w hwmem
    have hwinvx : w.symm x = x := by
      apply w.injective
      rw [LinearEquiv.apply_symm_apply, hwx]
    have hwinvneg : w.symm c₀ = -c₀ := by
      apply w.injective
      rw [map_neg, hwneg, neg_neg, LinearEquiv.apply_symm_apply]
    let ψ : Module.Dual (ZMod 3) V := -(f + f.comp (w.symm : V →ₗ[ZMod 3] V))
    have hψx : ψ x = f x := by
      simp only [ψ, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, hwinvx]
      have h : (-2 : ZMod 3) = 1 := by decide
      calc -(f x + f x) = (-2 : ZMod 3) * f x := by ring
        _ = 1 * f x := by rw [h]
        _ = f x := one_mul _
    have hψne : ψ ≠ 0 := by
      intro h0
      apply hfx
      rw [← hψx, h0]
      rfl
    have hψc₀ : ψ c₀ = 0 := by
      simp only [ψ, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, hwinvneg, map_neg, hfc]
      decide
    have htrans : IsTransvectionLin
        (Module.reflection hfc * (w * Module.reflection hfc * w⁻¹)) := by
      refine ⟨c₀, ψ, hc₀ne, hψne, hψc₀, fun v => ?_⟩
      rw [ggQ2TN6_case1_apply w f c₀ hfc hwneg v]
      have hψv : ψ v = -(f v + f (w.symm v)) := by
        simp only [ψ, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearEquiv.coe_toLinearMap]
      rw [hψv, neg_smul]
      abel
    have hgA : (Module.reflection hfc * (w * Module.reflection hfc * w⁻¹)) ∈ A :=
      A.mul_mem htA (A.mul_mem (A.mul_mem hwA htA) (A.inv_mem hwA))
    exact (hTF _ hgA) htrans
  · by_cases hfH : ∃ h ∈ Submodule.span (ZMod 3) (Set.range c), f h ≠ 0
    ·
      refine ⟨fun W hW => ?_, fun T hT => ?_⟩
      · refine ggQ2Mix_stable_eq_bot_or_top c α x hfix hconn hsup f c₀ hc₀H hc₀x hfx hfH W
          (fun i u hu => ?_) (fun u hu => ?_)
        · have hsu : s i u ∈ W := hW (s i) (Subgroup.subset_closure
            (Set.mem_union_left _ (Set.mem_range_self i))) u hu
          have hsub : α i u • c i = u - s i u := by rw [hs i u]; abel
          rw [hsub]
          exact W.sub_mem hu hsu
        · have htu : Module.reflection hfc u ∈ W := hW (Module.reflection hfc)
            (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))) u hu
          have hsub : f u • c₀ = u - Module.reflection hfc u := by
            rw [Module.reflection_apply]; abel
          rw [hsub]
          exact W.sub_mem hu htu
      · have hTs : ∀ i v, T (v - α i v • c i) = T v - α i (T v) • c i := by
          intro i v
          have hcomm : T (s i v) = s i (T v) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (hT (s i) (Subgroup.subset_closure
                (Set.mem_union_left _ (Set.mem_range_self i)))) v
          rw [← hs i v, hcomm, hs i (T v)]
        have hTt : ∀ v, T (v - f v • c₀) = T v - f (T v) • c₀ := by
          intro v
          have hcomm : T (Module.reflection hfc v) = Module.reflection hfc (T v) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (hT (Module.reflection hfc) (Subgroup.subset_closure
                (Set.mem_union_right _ (Set.mem_singleton _)))) v
          calc T (v - f v • c₀) = T (Module.reflection hfc v) := by
                rw [Module.reflection_apply]
            _ = Module.reflection hfc (T v) := hcomm
            _ = T v - f (T v) • c₀ := by rw [Module.reflection_apply]
        exact ggQ2Mix_commute_eq_smul (K := ZMod 3) (by decide) c α hαc x hxfix hxH hfix
          hconn hsup f c₀ hfc hc₀H hc₀x T hTs hTt
    ·
      exfalso
      have hfH0 : ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), f h = 0 := by
        intro h hh
        by_contra hne
        exact hfH ⟨h, hh, hne⟩
      have hfc_i : ∀ i, f (c i) = 0 :=
        fun i => hfH0 (c i) (Submodule.subset_span (Set.mem_range_self i))
      have hαc₀ : ∀ i, α i c₀ = 0 := by
        intro i
        by_contra hne
        have htrans : IsTransvectionLin
            (Module.reflection hfc * s i * Module.reflection hfc * s i) := by
          refine ⟨c i, (α i c₀) • f, hcne i, ?_, ?_, fun v => ?_⟩
          · intro h0
            apply hne
            have hx0 := congrArg (fun g : Module.Dual (ZMod 3) V => g x) h0
            simpa [hfx] using hx0
          · simp [hfc_i i]
          · rw [ggQ2TN6_case2_apply (s i) (α i) (c i) f c₀ hfc (hs i) (hαc i)
              (hfc_i i) v]
            rfl
        have hgA : (Module.reflection hfc * s i * Module.reflection hfc * s i) ∈ A :=
          A.mul_mem (A.mul_mem (A.mul_mem htA (hsA i)) htA) (hsA i)
        exact (hTF _ hgA) htrans
      exact hc₀x (hfix c₀ hαc₀)

end CFSG.StandardType

end
