module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc.E6Three E6TwoPilot

@[expose] def normE6 (v : Fin 4 → ZMod 3) : ZMod 3 :=
  v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3

@[expose] def e0E6 : Fin 4 → ZMod 3 := Pi.single 0 1

@[expose] def d2E6 : Fin 4 → ZMod 3 := ![1, 1, 0, 0]

@[expose] def d0E6 : Fin 4 → ZMod 3 := ![1, 1, 1, 0]

@[expose] def sgnE6 (i : Fin 4) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  Function.update v i (-(v i))

theorem sgnE6_eq : ∀ (i : Fin 4) (v : Fin 4 → ZMod 3),
    sgnE6 i v = v - reflFunE6Two i v • Pi.single i 1 := by
  decide +kernel

theorem sgnE6_sgnE6 : ∀ (i : Fin 4) (v : Fin 4 → ZMod 3), sgnE6 i (sgnE6 i v) = v := by
  decide +kernel

@[expose] def reachB (b : Fin 4 → ZMod 3) : ℕ → (Fin 4 → ZMod 3) → Bool
  | 0, v => decide (v = b)
  | n + 1, v => reachB b n v || reachB b n (sgnE6 0 v) || reachB b n (sgnE6 1 v) ||
      reachB b n (sgnE6 2 v) || reachB b n (sgnE6 3 v) || reachB b n (mtFun (mtFun v)) ||
      reachB b n (msFun (msFun v))

theorem reachB_one : ∀ v : Fin 4 → ZMod 3, normE6 v = 1 → reachB e0E6 4 v = true := by
  decide +kernel

theorem reachB_two : ∀ v : Fin 4 → ZMod 3, normE6 v = 2 → reachB d2E6 5 v = true := by
  decide +kernel

theorem reachB_zero : ∀ v : Fin 4 → ZMod 3, normE6 v = 0 → v ≠ 0 → reachB d0E6 4 v = true := by
  decide +kernel

section Weyl

variable
  {K : Type} [Field K] [CharP K 2]

theorem nE6Two_mem_normalizer (h2 : (2 : K) = 0) (i : Fin 4) :
    nE6Two i ∈ Subgroup.normalizer
      (((torusE6Two (K := K) h2).range : Subgroup (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K)) :=
  ggE6TwoThree_normalizer_of_action (torusE6Two h2) (nE6Two i) (ggE6TwoThree_reflEquiv i)
    (fun m => by
      have h := nE6Two_conj_torus h2 i (Multiplicative.toAdd m)
      rwa [ofAdd_toAdd m] at h)

theorem tE6Two_mem_normalizer (h2 : (2 : K) = 0) :
    tE6Two K ∈ Subgroup.normalizer
      (((torusE6Two (K := K) h2).range : Subgroup (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K)) :=
  ggE6TwoThree_normalizer_of_action (torusE6Two h2) (tE6Two K) mtAut
    (fun m => torusE6Two_mtAut h2 m)

theorem sE6Two_mem_normalizer (h2 : (2 : K) = 0) :
    sE6Two K ∈ Subgroup.normalizer
      (((torusE6Two (K := K) h2).range : Subgroup (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K)) :=
  ggE6TwoThree_normalizer_of_action (torusE6Two h2) (sE6Two K) msAut
    (fun m => torusE6Two_msAut h2 m)

@[expose] def InOrbit (h2 : (2 : K) = 0) (b v : Fin 4 → ZMod 3) : Prop :=
  ∃ g ∈ Subgroup.normalizer
      (((torusE6Two (K := K) h2).range : Subgroup (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K)),
    g * torusE6Two h2 (.ofAdd b) * g⁻¹ = torusE6Two h2 (.ofAdd v)

theorem inOrbit_sgn (h2 : (2 : K) = 0) {b : Fin 4 → ZMod 3} (i : Fin 4) {v : Fin 4 → ZMod 3}
    (h : InOrbit h2 b (sgnE6 i v)) : InOrbit h2 b v := by
  obtain ⟨g, hg, hgv⟩ := h
  refine ⟨nE6Two i * g, mul_mem (nE6Two_mem_normalizer h2 i) hg, ?_⟩
  calc nE6Two i * g * torusE6Two h2 (.ofAdd b) * (nE6Two i * g)⁻¹
      = nE6Two i * (g * torusE6Two h2 (.ofAdd b) * g⁻¹) * (nE6Two i)⁻¹ := by group
    _ = torusE6Two h2 (.ofAdd v) := by
      rw [hgv, nE6Two_conj_torus h2 i, ← sgnE6_eq i (sgnE6 i v), sgnE6_sgnE6]

theorem inOrbit_mt (h2 : (2 : K) = 0) {b v : Fin 4 → ZMod 3}
    (h : InOrbit h2 b (mtFun (mtFun v))) : InOrbit h2 b v := by
  obtain ⟨g, hg, hgv⟩ := h
  refine ⟨tE6Two K * g, mul_mem (tE6Two_mem_normalizer h2) hg, ?_⟩
  calc tE6Two K * g * torusE6Two h2 (.ofAdd b) * (tE6Two K * g)⁻¹
      = tE6Two K * (g * torusE6Two h2 (.ofAdd b) * g⁻¹) * (tE6Two K)⁻¹ := by group
    _ = torusE6Two h2 (.ofAdd v) := by
      rw [hgv, torusE6Two_mtAut h2, mtAut_ofAdd, mtFun_cube]

theorem inOrbit_ms (h2 : (2 : K) = 0) {b v : Fin 4 → ZMod 3}
    (h : InOrbit h2 b (msFun (msFun v))) : InOrbit h2 b v := by
  obtain ⟨g, hg, hgv⟩ := h
  refine ⟨sE6Two K * g, mul_mem (sE6Two_mem_normalizer h2) hg, ?_⟩
  calc sE6Two K * g * torusE6Two h2 (.ofAdd b) * (sE6Two K * g)⁻¹
      = sE6Two K * (g * torusE6Two h2 (.ofAdd b) * g⁻¹) * (sE6Two K)⁻¹ := by group
    _ = torusE6Two h2 (.ofAdd v) := by
      rw [hgv, torusE6Two_msAut h2, msAut_ofAdd, msFun_cube]

theorem inOrbit_of_reachB (h2 : (2 : K) = 0) (b : Fin 4 → ZMod 3) :
    ∀ (n : ℕ) (v : Fin 4 → ZMod 3), reachB b n v = true → InOrbit h2 b v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have hv' : v = b := of_decide_eq_true hv
    subst hv'
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ n ih =>
    intro v hv
    simp only [reachB, Bool.or_eq_true] at hv
    rcases hv with (((((h | h) | h) | h) | h) | h) | h
    · exact ih v h
    · exact inOrbit_sgn h2 0 (ih _ h)
    · exact inOrbit_sgn h2 1 (ih _ h)
    · exact inOrbit_sgn h2 2 (ih _ h)
    · exact inOrbit_sgn h2 3 (ih _ h)
    · exact inOrbit_mt h2 (ih _ h)
    · exact inOrbit_ms h2 (ih _ h)

end Weyl

end CFSG.StandardType.SmallExc

end
