module

public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.GGCartanATypeArith
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import Mathlib.Algebra.Field.ZMod
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.StandardType in
private theorem ker_map_cartanMatrix_A {ℓ : ℕ} (hp : p ∣ ℓ + 1) (hn : 1 ≤ ℓ) :
    LinearMap.ker ((CartanMatrix.A ℓ).map (Int.cast : ℤ → ZMod p)).mulVecLin =
      Submodule.span (ZMod p) {ggCartanARad ℓ p} := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_span_singleton]
    have hx' : ∀ i, ∑ j, ggCartanAMod ℓ p i j * x j = 0 := by
      intro i
      have h := congrFun hx i
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum] at h
      simpa [Matrix.map_apply, ggCartanAMod] using h
    exact ⟨x ⟨0, hn⟩, (ggCartanAMod_ker ℓ p hn x hx').symm⟩
  · intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    have hvker : ((CartanMatrix.A ℓ).map (Int.cast : ℤ → ZMod p)).mulVecLin
        (ggCartanARad ℓ p) = 0 := by
      ext i
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
      simpa [Matrix.map_apply, ggCartanAMod] using ggCartanAMod_rad ℓ p hp i
    rw [map_smul, hvker, smul_zero]

theorem rank_map_cartanMatrix_A (ℓ : ℕ) :
    ((CartanMatrix.A ℓ).map (Int.cast : ℤ → ZMod p)).rank = if p ∣ ℓ + 1 then ℓ - 1 else ℓ := by
  classical
  by_cases hp : p ∣ ℓ + 1
  · rw [if_pos hp]
    have hn : 1 ≤ ℓ := by
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hle : p ≤ ℓ + 1 := Nat.le_of_dvd (by omega) hp
      omega
    have hv : CFSG.StandardType.ggCartanARad ℓ p ≠ 0 := by
      intro h
      have h0 := congrFun h ⟨0, hn⟩
      simp [CFSG.StandardType.ggCartanARad] at h0
    have hker := ker_map_cartanMatrix_A hp hn
    have hrank : ((CartanMatrix.A ℓ).map (Int.cast : ℤ → ZMod p)).rank = ℓ - 1 := by
      set f : (Fin ℓ → ZMod p) →ₗ[ZMod p] (Fin ℓ → ZMod p) :=
        ((CartanMatrix.A ℓ).map (Int.cast : ℤ → ZMod p)).mulVecLin with hf
      have hfker : LinearMap.ker f =
          Submodule.span (ZMod p) {CFSG.StandardType.ggCartanARad ℓ p} := by
        rw [hf]; exact hker
      have h := LinearMap.finrank_range_add_finrank_ker f
      rw [hfker, finrank_span_singleton hv] at h
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      rw [Matrix.rank, ← hf]
      omega
    exact hrank
  · rw [if_neg hp]
    have hdet : ((CartanMatrix.A ℓ).map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
      change ((CartanMatrix.A ℓ).map (fun x : ℤ => (x : ZMod p))).det ≠ 0
      rw [← Int.cast_det (R := ZMod p) (CartanMatrix.A ℓ), CartanMatrix.A_det]
      intro h
      apply hp
      have h' : (p : ℤ) ∣ (ℓ : ℤ) + 1 := by
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      exact_mod_cast h'
    simpa using Matrix.rank_of_det_ne_zero hdet

open CFSG.StandardType in
private theorem isLinRefl_conj {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {t g : V ≃ₗ[ZMod p] V} (h : IsLinRefl t) : IsLinRefl (g * t * g⁻¹) := by
  obtain ⟨x, f, hfx, hT⟩ := h
  refine ⟨g x, f.comp g.symm.toLinearMap, ?_, ?_⟩
  · simp [hfx]
  · intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hT (g⁻¹ v)]
    simp [map_sub, map_smul]

theorem isSwap_symm_apply_of_isRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2) {ℓ : ℕ}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (T : Equiv.Perm (Fin (ℓ + 1)) ≃* A)
    (hT : ∀ k : Fin ℓ, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U))
    {r : A} (hr : IsRefl p (r : U ≃ₗ[ZMod p] U)) : (T.symm r).IsSwap := by
  let τ : Equiv.Perm (Fin (ℓ + 1)) →* (U ≃ₗ[ZMod p] U) := A.subtype.comp T.toMonoidHom
  refine CFSG.StandardType.isSwap_of_isLinRefl hp τ ?_ ?_ ?_
  · exact A.subtype_injective.comp T.injective
  · intro x y hxy
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · subst hℓ
      exact absurd (Fin.ext (by omega)) hxy
    · let k : Fin ℓ := ⟨0, hℓ⟩
      have hk : k.castSucc ≠ k.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp [Fin.castSucc, Fin.succ] at hv
      have hbase : CFSG.StandardType.IsLinRefl
          (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U) := by
        obtain ⟨a, φ, hφ, hrfl⟩ := (isRefl_iff hp _).mp (hT k)
        exact ⟨a, φ, hφ, fun v => by rw [hrfl, Module.reflection_apply]⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp
        (Equiv.Perm.isConj_swap (w := k.castSucc) (x := k.succ) (y := x) (z := y) hk hxy)
      have hTconj : T (Equiv.swap x y) =
          T c * T (Equiv.swap k.castSucc k.succ) * (T c)⁻¹ := by
        rw [← hc, map_mul, map_mul, map_inv]
      show CFSG.StandardType.IsLinRefl ((T (Equiv.swap x y) : U ≃ₗ[ZMod p] U))
      rw [hTconj]
      simpa using isLinRefl_conj (g := (T c : U ≃ₗ[ZMod p] U)) hbase
  · have hτr : τ (T.symm r) = (r : U ≃ₗ[ZMod p] U) := by
      change A.subtype (T (T.symm r)) = (r : U ≃ₗ[ZMod p] U)
      rw [T.apply_symm_apply]
      rfl
    rw [hτr]
    obtain ⟨a, φ, hφ, hrfl⟩ := (isRefl_iff hp (r : U ≃ₗ[ZMod p] U)).mp hr
    exact ⟨a, φ, hφ, fun v => by rw [hrfl, Module.reflection_apply]⟩

theorem symmetric_row_of_isCartanModel_A [Module.Finite (ZMod p) U] (hp : p ≠ 2) {ℓ n : ℕ}
    (hn : Module.finrank (ZMod p) U = n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : IsCartanModel p (CartanMatrix.A ℓ) A) (T : Equiv.Perm (Fin (ℓ + 1)) ≃* A)
    (hT : ∀ k : Fin ℓ, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U)) :
    (¬ p ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
        ∀ r : A, IsRefl p (r : U ≃ₗ[ZMod p] U) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
      (p ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
        ∀ r : A, IsRefl p (r : U ≃ₗ[ZMod p] U) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) := by
  have hfin := hA.finrank_eq_rank
  rw [rank_map_cartanMatrix_A ℓ, hn] at hfin
  by_cases hpℓ : p ∣ ℓ + 1
  · right
    rw [if_pos hpℓ] at hfin
    have hnℓ : 1 ≤ ℓ := by
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hle : p ≤ ℓ + 1 := Nat.le_of_dvd (by omega) hpℓ
      omega
    have hn2 : n + 2 = ℓ + 1 := by omega
    refine ⟨?_, ?_⟩
    · rwa [hn2]
    · rw [hn2]
      exact ⟨T.symm, fun r hr => isSwap_symm_apply_of_isRefl hp T hT hr⟩
  · left
    rw [if_neg hpℓ] at hfin
    have hn1 : n + 1 = ℓ + 1 := by omega
    refine ⟨?_, ?_⟩
    · rwa [hn1]
    · rw [hn1]
      exact ⟨T.symm, fun r hr => isSwap_symm_apply_of_isRefl hp T hT hr⟩

end CFSG.StandardType.ZS

end
