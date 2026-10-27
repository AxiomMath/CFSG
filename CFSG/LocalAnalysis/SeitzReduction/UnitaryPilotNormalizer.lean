module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotOuter
import CFSG.GroupTheory.OddKernelImage

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_of_forall_map_primeFormConjHom_eq {F : Type} [Field F] {f n : ℕ}
    (h : UnitaryFieldData 2 f F) {C : GL (Fin n) F} {K : Type} [Group K] {X : Subgroup K}
    (e : primeFormP h (C : Matrix (Fin n) (Fin n) F) ≃* X)
    (hC : Subgroup.centralizer (X : Set K) = ⊥)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) F)) {w : K} {k : ℕ}
    (hw : w ^ 2 ^ k = 1)
    (hA : ∀ z, (e (primeFormConjHom h _ A z) : K) = w * e z * w⁻¹) :
    w ∈ X := by
  set β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) F)) := primeFormConjHom h _ A
    with hβdef
  have hβD : β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) F) := ⟨A, hβdef.symm⟩
  have hpow : ∀ (j : ℕ) (z : primeFormP h (C : Matrix (Fin n) (Fin n) F)),
      (e ((β ^ j) z) : K) = w ^ j * (e z : K) * (w ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ j ih =>
      intro z
      rw [pow_succ, MulAut.mul_apply, ih (β z), hβdef, hA z, pow_succ]
      group
  have hβk : β ^ 2 ^ k = 1 := by
    refine MulEquiv.ext fun z => ?_
    have h := hpow (2 ^ k) z
    rw [hw, one_mul, inv_one, mul_one] at h
    exact e.injective (Subtype.coe_injective h)
  obtain ⟨s, hs⟩ := mem_inner_of_mem_primeFormD_of_pow h C hβD hβk
  have hconj : ∀ y ∈ X, w * y * w⁻¹ = (e s : K) * y * (e s : K)⁻¹ := by
    intro y hy
    obtain ⟨z, hz⟩ := e.surjective ⟨y, hy⟩
    have hzy : (e z : K) = y := congrArg Subtype.val hz
    rw [← hzy]
    have h1 := hA z
    rw [← hs, MulAut.conj_apply] at h1
    have h2 : (e (s * z * s⁻¹) : K) = (e s : K) * (e z : K) * (e s : K)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      simp
    rw [h2] at h1
    exact h1.symm
  rw [CFSG.GroupTheory.eq_of_forall_conj_eq hC hconj]
  exact (e s).2

theorem isCyclic_of_inf_eq_bot {F : Type} [Field F] {f n : ℕ} (h : UnitaryFieldData 2 f F)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) F} (hCg : IsPrimeFormGram C)
    {K : Type} [Group K] {X : Subgroup K}
    (e : primeFormP h (C : Matrix (Fin n) (Fin n) F) ≃* X)
    (hC : Subgroup.centralizer (X : Set K) = ⊥) {W : Subgroup K}
    (hWN : W ≤ Subgroup.normalizer (X : Set K)) (hW2 : IsPGroup 2 W) (hWX : W ⊓ X = ⊥) :
    IsCyclic W := by
  let θ : W →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion hWN)
  let ψ : W →* Outer X := (QuotientGroup.mk' (inner X)).comp θ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hθ : θ w ∈ inner X := by
      have h1 : QuotientGroup.mk' (inner X) (θ w) = 1 := hw
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨s, hs⟩ := hθ
    have hconj : ∀ y ∈ X, w * y * w⁻¹ = (s : K) * y * (s : K)⁻¹ := by
      intro y hy
      have h1 := congrArg (fun γ : MulAut X => ((γ ⟨y, hy⟩ : X) : K)) hs
      rw [MulAut.conj_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have h2 : ((θ w) ⟨y, hy⟩ : K) = w * y * w⁻¹ := by
        simp [θ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [h2] at h1
      exact h1.symm
    have hwX : (w : K) ∈ X := by
      have h := CFSG.GroupTheory.eq_of_forall_conj_eq hC hconj
      rw [h]
      exact s.2
    have hmem : (w : K) ∈ W ⊓ X := ⟨w.2, hwX⟩
    rw [hWX] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hθ2 : IsPGroup 2 θ.range :=
    hW2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  haveI hcyc : IsCyclic ψ.range := by
    have h := isCyclic_map_outer_of_mulEquiv e.symm
      (fun B hB => isCyclic_map_outer_primeFormP h hn hq hCg hB) θ.range hθ2
    rw [← MonoidHom.range_comp] at h
    exact h
  exact isCyclic_of_injective ψ.rangeRestrict fun a b hab => hψ (Subtype.ext_iff.mp hab)

end CFSG.SeitzReduction.UnitaryPilot
