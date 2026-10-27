module

import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.GraphOdd
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem false_of_borelStd_one_intertwiner_pair {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W)
    [ρ.IsIrreducible] {ε : Fin 2 → Finset (Fin 4)} (hε : HasTwistedLabel ρ ε)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K))
      ρ.asModule) = 2)
    {j : Fin 4} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 3) (h0 : ε 0 = {j}) (h1 : ε 1 = {j})
    {d : W ≃ₗ[ZMod 2] W} {B : Matrix.GeneralLinearGroup (Fin 4) K} (hB : IsUpperGL B)
    {τ : K ≃+* K} (hd2 : d * d = 1)
    (hd : ∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (w : W),
      d (ρ x w) = ρ (borelStd 4 K B τ 1 x) (d w)) : False := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin 4) K)) ρ.asModule
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, y, χ, J, _hε0, ht, _hεχ, hεJ, β, _hβ⟩ := hε
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra E k := hEalg
  letI : Algebra K k := hKalg
  have htwo : ∀ c : E, c = 0 ∨ c = 1 := by
    obtain ⟨y₀, hy₀, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : E)).1 hE
    haveI : Nontrivial E := ⟨⟨y₀, 0, hy₀⟩⟩
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h1y : (1 : E) = y₀ := hyuniq 1 one_ne_zero
      exact (hyuniq c hc).trans h1y.symm
  let D : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.zpowers d
  have hD2W : ∀ e ∈ D, e * e = 1 := by
    intro e he
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h := (Commute.refl d).mul_zpow z
    rw [hd2, one_zpow] at h
    exact h.symm
  let δ : Representation (ZMod 2) ↥D ρ.asModule :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.topActor ρ D
  have hδE : ∀ (e : ↥D) (c : E) (x : ρ.asModule), δ e (c • x) = c • δ e x := by
    intro e c x
    rcases htwo c with rfl | rfl
    · rw [zero_smul, map_zero, zero_smul]
    · rw [one_smul, one_smul]
  have hD2 : ∀ e, δ e * δ e = 1 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.topActor_mul_self ρ D hD2W
  have hgraph' : ∃ e : ↥D, ∃ A : Matrix.GeneralLinearGroup (Fin 4) K,
      IsUpperGL A ∧ ∃ τ : K ≃+* K, ∀ g x, δ e (CFSG.endFieldRep ρ g x) =
        CFSG.endFieldRep ρ (borelStd 4 K A τ 1 g) (δ e x) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.topActor_graph ρ D
      ⟨d, Subgroup.mem_zpowers d, B, hB, τ, hd⟩
  have hsimp := isSimpleRep_extendScalars_endFieldRep ρ k
  have hiff (s : Fin 3) : s.succ ≠ j ↔ (Fin.rev s).succ ≠ j := by
    have hJ := stage_mem_iff_rev_mem (n := 3) (σ := CFSG.endFieldRep ρ)
      hsimp ht δ hδE hD2 hgraph' s
    have hsJ : s ∈ J ↔ s.succ ≠ j := by
      rw [hεJ s, Fin.forall_fin_two, h0, h1]
      simp
    have hrJ : Fin.rev s ∈ J ↔ (Fin.rev s).succ ≠ j := by
      rw [hεJ (Fin.rev s), Fin.forall_fin_two, h0, h1]
      simp
    exact hsJ.symm.trans (hJ.trans hrJ)
  rcases hj with hj | hj
  · have h := hiff (0 : Fin 3)
    have heq : (0 : Fin 3).succ = j := by
      apply Fin.ext
      simp [Fin.val_succ, hj]
    have hne : (Fin.rev (0 : Fin 3)).succ ≠ j := by
      intro hc
      have hv := congrArg Fin.val hc
      simp [Fin.val_succ, Fin.val_rev] at hv
      omega
    exact (h.mpr hne) heq
  · have h := hiff (2 : Fin 3)
    have heq : (2 : Fin 3).succ = j := by
      apply Fin.ext
      simp [Fin.val_succ, hj]
    have hne : (Fin.rev (2 : Fin 3)).succ ≠ j := by
      intro hc
      have hv := congrArg Fin.val hc
      simp [Fin.val_succ, Fin.val_rev] at hv
      omega
    exact (h.mpr hne) heq

end CFSG.LocalAnalysis.WeakClosure81
