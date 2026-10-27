module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphWord
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFourLeafNorm
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType

open Module

@[expose] def ggQ2gwD4C : Fin 4 → Fin 4 → ZMod 3 :=
  ![![2, -1, 0, 0], ![-1, 2, -1, -1], ![0, -1, 2, 0], ![0, -1, 0, 2]]

theorem ggQ2gwD4C_eq : ∀ i j : Fin 4, ((CartanMatrix.D 4 i j : ℤ) : ZMod 3) = ggQ2gwD4C i j := by
  decide +kernel

@[expose] def ggQ2gwD4Kill : List GGQ2gwKill := [
  { d := ![0, 0, 1, 1], w := ![[2, 1], [], [3, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 1, 0], ![1, 0, 0, 0], ![1, 1, 0, 1]],
    φ := ![![1, 0, 1, 2], ![2, 2, 0, 0], ![1, 0, 2, 1]],
    inv := ![![0, 1, 0, 0], ![2, 2, 2, 1], ![2, 0, 1, 2], ![1, 0, 2, 2]] },
  { d := ![0, 0, 1, 2], w := ![[1], [], [3, 2, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 1, 1]],
    φ := ![![1, 1, 2, 2], ![2, 2, 0, 0], ![1, 2, 1, 1]],
    inv := ![![0, 1, 0, 0], ![1, 2, 0, 0], ![1, 0, 2, 2], ![1, 0, 2, 1]] },
  { d := ![0, 0, 2, 1], w := ![[1], [], [3, 2, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 1, 1]],
    φ := ![![1, 1, 2, 2], ![2, 2, 0, 0], ![1, 2, 1, 1]],
    inv := ![![0, 1, 0, 0], ![1, 2, 0, 0], ![1, 0, 2, 1], ![1, 0, 2, 2]] },
  { d := ![0, 0, 2, 2], w := ![[2, 1], [], [3, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 1, 0], ![1, 0, 0, 0], ![1, 1, 0, 1]],
    φ := ![![1, 0, 1, 2], ![2, 2, 0, 0], ![1, 0, 2, 1]],
    inv := ![![0, 1, 0, 0], ![2, 2, 2, 2], ![2, 0, 1, 1], ![1, 0, 2, 1]] },
  { d := ![0, 1, 2, 2], w := ![[2, 1], [1], [3, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 1, 0], ![1, 1, 0, 0], ![1, 1, 0, 1]],
    φ := ![![1, 0, 1, 2], ![1, 1, 2, 2], ![1, 0, 2, 1]],
    inv := ![![2, 0, 2, 2], ![1, 1, 1, 1], ![1, 2, 0, 0], ![0, 2, 1, 0]] },
  { d := ![0, 2, 1, 1], w := ![[2, 1], [1], [3, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 1, 0], ![1, 1, 0, 0], ![1, 1, 0, 1]],
    φ := ![![1, 0, 1, 2], ![1, 1, 2, 2], ![1, 0, 2, 1]],
    inv := ![![2, 0, 2, 1], ![1, 1, 1, 2], ![1, 2, 0, 0], ![0, 2, 1, 0]] },
  { d := ![1, 0, 0, 1], w := ![[1], [2, 1], [3, 0, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 0, 0], ![1, 1, 1, 0], ![0, 1, 0, 1]],
    φ := ![![1, 1, 2, 2], ![1, 0, 1, 2], ![2, 1, 2, 1]],
    inv := ![![2, 0, 1, 2], ![2, 0, 2, 1], ![2, 1, 0, 0], ![1, 0, 2, 2]] },
  { d := ![1, 0, 0, 2], w := ![[0, 1], [2, 0, 1], [3, 1]], j := ![0, 0, 0],
    c := ![![0, 1, 0, 0], ![0, 1, 1, 0], ![1, 1, 0, 1]],
    φ := ![![2, 2, 2, 2], ![2, 1, 1, 2], ![1, 0, 2, 1]],
    inv := ![![1, 0, 2, 2], ![1, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 2, 1]] },
  { d := ![1, 0, 1, 0], w := ![[1], [3, 1], [2, 0, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 0, 0], ![1, 1, 0, 1], ![0, 1, 1, 0]],
    φ := ![![1, 1, 2, 2], ![1, 0, 2, 1], ![2, 1, 1, 2]],
    inv := ![![2, 0, 1, 2], ![2, 0, 2, 1], ![1, 0, 2, 2], ![2, 1, 0, 0]] },
  { d := ![1, 0, 2, 0], w := ![[0, 1], [3, 0, 1], [2, 1]], j := ![0, 0, 0],
    c := ![![0, 1, 0, 0], ![0, 1, 0, 1], ![1, 1, 1, 0]],
    φ := ![![2, 2, 2, 2], ![2, 1, 2, 1], ![1, 0, 1, 2]],
    inv := ![![1, 0, 2, 2], ![1, 0, 0, 0], ![1, 0, 2, 1], ![2, 1, 0, 0]] },
  { d := ![1, 1, 2, 2], w := ![[2, 0, 1], [0, 1], [3, 0, 1]], j := ![0, 0, 0],
    c := ![![0, 1, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 1]],
    φ := ![![2, 1, 1, 2], ![2, 2, 2, 2], ![2, 1, 2, 1]],
    inv := ![![1, 0, 1, 1], ![0, 1, 0, 0], ![1, 2, 0, 0], ![0, 2, 1, 0]] },
  { d := ![1, 2, 0, 1], w := ![[], [2, 1], [3, 2, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1]],
    φ := ![![2, 2, 0, 0], ![1, 0, 1, 2], ![1, 2, 1, 1]],
    inv := ![![1, 0, 0, 0], ![1, 2, 1, 2], ![1, 2, 2, 1], ![0, 2, 1, 0]] },
  { d := ![1, 2, 1, 0], w := ![[], [3, 1], [3, 2, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 1]],
    φ := ![![2, 2, 0, 0], ![1, 0, 2, 1], ![1, 2, 1, 1]],
    inv := ![![1, 0, 0, 0], ![1, 2, 1, 2], ![0, 2, 1, 0], ![1, 2, 2, 1]] },
  { d := ![1, 2, 1, 2], w := ![[], [1], [2, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0]],
    φ := ![![2, 2, 0, 0], ![1, 1, 2, 2], ![1, 0, 1, 2]],
    inv := ![![1, 0, 0, 0], ![2, 1, 0, 0], ![0, 2, 1, 0], ![2, 1, 1, 2]] },
  { d := ![1, 2, 2, 1], w := ![[], [1], [3, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 1]],
    φ := ![![2, 2, 0, 0], ![1, 1, 2, 2], ![1, 0, 2, 1]],
    inv := ![![1, 0, 0, 0], ![2, 1, 0, 0], ![2, 1, 1, 2], ![0, 2, 1, 0]] },
  { d := ![2, 0, 0, 1], w := ![[0, 1], [2, 0, 1], [3, 1]], j := ![0, 0, 0],
    c := ![![0, 1, 0, 0], ![0, 1, 1, 0], ![1, 1, 0, 1]],
    φ := ![![2, 2, 2, 2], ![2, 1, 1, 2], ![1, 0, 2, 1]],
    inv := ![![1, 0, 2, 1], ![1, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 2, 2]] },
  { d := ![2, 0, 0, 2], w := ![[1], [2, 1], [3, 0, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 0, 0], ![1, 1, 1, 0], ![0, 1, 0, 1]],
    φ := ![![1, 1, 2, 2], ![1, 0, 1, 2], ![2, 1, 2, 1]],
    inv := ![![2, 0, 1, 1], ![2, 0, 2, 2], ![2, 1, 0, 0], ![1, 0, 2, 1]] },
  { d := ![2, 0, 1, 0], w := ![[0, 1], [3, 0, 1], [2, 1]], j := ![0, 0, 0],
    c := ![![0, 1, 0, 0], ![0, 1, 0, 1], ![1, 1, 1, 0]],
    φ := ![![2, 2, 2, 2], ![2, 1, 2, 1], ![1, 0, 1, 2]],
    inv := ![![1, 0, 2, 1], ![1, 0, 0, 0], ![1, 0, 2, 2], ![2, 1, 0, 0]] },
  { d := ![2, 0, 2, 0], w := ![[1], [3, 1], [2, 0, 1]], j := ![0, 0, 0],
    c := ![![1, 1, 0, 0], ![1, 1, 0, 1], ![0, 1, 1, 0]],
    φ := ![![1, 1, 2, 2], ![1, 0, 2, 1], ![2, 1, 1, 2]],
    inv := ![![2, 0, 1, 1], ![2, 0, 2, 2], ![1, 0, 2, 1], ![2, 1, 0, 0]] },
  { d := ![2, 1, 0, 2], w := ![[], [2, 1], [3, 2, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1]],
    φ := ![![2, 2, 0, 0], ![1, 0, 1, 2], ![1, 2, 1, 1]],
    inv := ![![1, 0, 0, 0], ![1, 2, 1, 1], ![1, 2, 2, 2], ![0, 2, 1, 0]] },
  { d := ![2, 1, 1, 2], w := ![[], [1], [3, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 1]],
    φ := ![![2, 2, 0, 0], ![1, 1, 2, 2], ![1, 0, 2, 1]],
    inv := ![![1, 0, 0, 0], ![2, 1, 0, 0], ![2, 1, 1, 1], ![0, 2, 1, 0]] },
  { d := ![2, 1, 2, 0], w := ![[], [3, 1], [3, 2, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 1]],
    φ := ![![2, 2, 0, 0], ![1, 0, 2, 1], ![1, 2, 1, 1]],
    inv := ![![1, 0, 0, 0], ![1, 2, 1, 1], ![0, 2, 1, 0], ![1, 2, 2, 2]] },
  { d := ![2, 1, 2, 1], w := ![[], [1], [2, 1]], j := ![0, 0, 0],
    c := ![![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0]],
    φ := ![![2, 2, 0, 0], ![1, 1, 2, 2], ![1, 0, 1, 2]],
    inv := ![![1, 0, 0, 0], ![2, 1, 0, 0], ![0, 2, 1, 0], ![2, 1, 1, 1]] },
  { d := ![2, 2, 1, 1], w := ![[2, 0, 1], [0, 1], [3, 0, 1]], j := ![0, 0, 0],
    c := ![![0, 1, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 1]],
    φ := ![![2, 1, 1, 2], ![2, 2, 2, 2], ![2, 1, 2, 1]],
    inv := ![![1, 0, 1, 2], ![0, 1, 0, 0], ![1, 2, 0, 0], ![0, 2, 1, 0]] }
]

@[expose] def ggQ2gwD4Word0 : List ((Fin 4 → ZMod 3) × List (Fin 4)) := [
  (![0, 1, 0, 2], []),
  (![0, 1, 1, 2], [2]),
  (![0, 1, 2, 0], [0, 1, 2, 3, 1, 0]),
  (![0, 1, 2, 1], [0, 1, 2, 1, 3, 1, 0]),
  (![0, 2, 0, 1], [0, 1, 2, 1, 0, 3, 1, 0, 2]),
  (![0, 2, 1, 0], [2, 1, 3]),
  (![0, 2, 1, 2], [2, 1]),
  (![0, 2, 2, 1], [0, 1, 2, 1, 0, 3, 1, 0]),
  (![1, 0, 1, 1], [0, 2, 1, 3]),
  (![1, 0, 1, 2], [0, 2, 1]),
  (![1, 0, 2, 1], [0, 1, 2, 1, 3]),
  (![1, 0, 2, 2], [0, 1, 2, 1]),
  (![1, 1, 0, 2], [0]),
  (![1, 1, 1, 2], [0, 2]),
  (![1, 1, 2, 0], [0, 1, 2, 3, 1]),
  (![1, 1, 2, 1], [0, 1, 2, 1, 3, 1]),
  (![1, 2, 0, 0], [0, 1, 3]),
  (![1, 2, 0, 2], [0, 1]),
  (![1, 2, 2, 0], [0, 1, 2, 3]),
  (![1, 2, 2, 2], [0, 1, 2]),
  (![2, 0, 1, 1], [0, 2, 1, 0, 3]),
  (![2, 0, 1, 2], [0, 2, 1, 0]),
  (![2, 0, 2, 1], [0, 1, 2, 1, 0, 3]),
  (![2, 0, 2, 2], [0, 1, 2, 1, 0]),
  (![2, 1, 0, 0], [2, 1, 0, 3, 1, 2]),
  (![2, 1, 0, 1], [0, 2, 1, 0, 3, 1, 2]),
  (![2, 1, 1, 0], [2, 1, 0, 3, 1]),
  (![2, 1, 1, 1], [0, 2, 1, 0, 3, 1]),
  (![2, 2, 0, 1], [0, 1, 2, 1, 0, 3, 1, 2]),
  (![2, 2, 1, 0], [2, 1, 0, 3]),
  (![2, 2, 1, 2], [2, 1, 0]),
  (![2, 2, 2, 1], [0, 1, 2, 1, 0, 3, 1])
]

@[expose] def ggQ2gwD4Word2 : List ((Fin 4 → ZMod 3) × List (Fin 4)) := [
  (![0, 0, 0, 1], []),
  (![0, 0, 0, 2], [3]),
  (![0, 0, 1, 0], [1, 2, 3, 1]),
  (![0, 0, 2, 0], [1, 2, 3, 1, 2]),
  (![0, 1, 0, 0], [1, 3]),
  (![0, 1, 0, 1], [1]),
  (![0, 1, 1, 0], [1, 2, 3]),
  (![0, 1, 1, 1], [1, 2]),
  (![0, 2, 0, 0], [1, 3, 1]),
  (![0, 2, 0, 2], [3, 1]),
  (![0, 2, 2, 0], [1, 3, 1, 2]),
  (![0, 2, 2, 2], [3, 1, 2]),
  (![1, 0, 0, 0], [1, 0, 3, 1]),
  (![1, 1, 0, 0], [1, 0, 3]),
  (![1, 1, 0, 1], [1, 0]),
  (![1, 1, 1, 0], [1, 0, 2, 3]),
  (![1, 1, 1, 1], [1, 0, 2]),
  (![1, 2, 1, 1], [1, 0, 2, 1]),
  (![2, 0, 0, 0], [1, 0, 3, 1, 0]),
  (![2, 1, 2, 2], [3, 1, 0, 2, 1]),
  (![2, 2, 0, 0], [1, 3, 1, 0]),
  (![2, 2, 0, 2], [3, 1, 0]),
  (![2, 2, 2, 0], [1, 3, 1, 0, 2]),
  (![2, 2, 2, 2], [3, 1, 0, 2])
]

@[expose] def ggQ2gwD4WordOf (tab : List ((Fin 4 → ZMod 3) × List (Fin 4)))
    (x : Fin 4 → ZMod 3) : List (Fin 4) :=
  ((tab.find? fun p => decide (p.1 0 = x 0) && decide (p.1 1 = x 1) &&
    decide (p.1 2 = x 2) && decide (p.1 3 = x 3)).map Prod.snd).getD []

open scoped CFSG.Decide.Bounded in
theorem ggQ2gwD4Kill_ok : ∀ E ∈ ggQ2gwD4Kill, E.OK ggQ2gwD4C := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggQ2gwD4_cover_one : ∀ x : Fin 4 → ZMod 3,
    ggQ2gwQ ggQ2gwD4C (fun _ => 1) x = 1 → ∃ E ∈ ggQ2gwD4Kill, E.d = x := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggQ2gwD4_word_two : ∀ x : Fin 4 → ZMod 3,
    ggQ2gwQ ggQ2gwD4C (fun _ => 1) x = 2 →
    ggQ2gwAct ggQ2gwD4C (ggQ2gwD4WordOf ggQ2gwD4Word2 x) x = ![0, 0, 0, 1] ∨
      ggQ2gwAct ggQ2gwD4C (ggQ2gwD4WordOf ggQ2gwD4Word2 x) x = -![0, 0, 0, 1] := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggQ2gwD4_word_zero : ∀ x : Fin 4 → ZMod 3, x ≠ 0 →
    ggQ2gwQ ggQ2gwD4C (fun _ => 1) x = 0 →
    ggQ2gwAct ggQ2gwD4C (ggQ2gwD4WordOf ggQ2gwD4Word0 x) x = ![0, 1, 0, 2] ∨
      ggQ2gwAct ggQ2gwD4C (ggQ2gwD4WordOf ggQ2gwD4Word0 x) x = -![0, 1, 0, 2] := by
  decide +kernel

theorem ggQ2gwD4_symm : ∀ i j : Fin 4,
    (fun _ => (1 : ZMod 3)) i * ggQ2gwD4C i j = (fun _ => 1) j * ggQ2gwD4C j i := by
  decide +kernel

theorem ggQ2gwD4_diag : ∀ j : Fin 4, ggQ2gwD4C j j = 2 := by
  decide +kernel

theorem ggQ2gwD4_lam : ∀ lam : Fin 4 → ZMod 3,
    (∀ i j : Fin 4, ggQ2gwD4C i j * lam i = ggQ2gwD4C j i * lam j) →
    ∃ μ : ZMod 3, ∀ i : Fin 4, 2 * lam i = μ * 1 := by
  decide +kernel

theorem ggQ2gwD4_QE : ∀ k : Fin 4, ggQ2gwQ ggQ2gwD4C (fun _ => 1) (ggQ2gwE k) = 2 := by
  decide +kernel

private theorem ggQ2gwForm_smul {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (wt : Fin n → ZMod 3) (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Dual (ZMod 3) U) (c : ZMod 3) (u v : U) :
    ggQ2gwForm wt h hli hsp α (c • u) (c • v) =
      c * c * ggQ2gwForm wt h hli hsp α u v := by
  simp only [ggQ2gwForm, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem ggQ2gwD4_form_preserves {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin 4 → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin 4 → Dual (ZMod 3) U)
    (hα : ∀ i j : Fin 4, α i (h j) = ((CartanMatrix.D 4 i j : ℤ) : ZMod 3))
    (d : U) (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U))) :
    ggQ2gwQ ggQ2gwD4C (fun _ => 1) (ggQ2gwCoord h hli hsp (T.symm d)) =
      ggQ2gwQ ggQ2gwD4C (fun _ => 1) (ggQ2gwCoord h hli hsp d) := by
  have hα' : ∀ i j : Fin 4, α i (h j) = ggQ2gwD4C i j := by
    intro i j
    rw [hα i j]
    exact ggQ2gwD4C_eq i j
  have hdiag : ∀ j : Fin 4, ggQ2gwD4C j j = 2 := ggQ2gwD4_diag
  have hTin : T⁻¹ ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) :=
    Subgroup.inv_mem _ hT
  obtain ⟨μ, hμ⟩ := ggQ2gwForm_normalizer ggQ2gwD4C (fun _ => 1) ggQ2gwD4_symm ggQ2gwD4_lam
    h hli hsp α hα' hdiag T⁻¹ hTin
  obtain ⟨w, hw, ε, hε0, π, hπ, hTπ⟩ := ggQ2WeylDiag_D4 h hli hsp α hα T⁻¹ hTin
  have hQe : ∀ k : Fin 4, ggQ2gwQ ggQ2gwD4C (fun _ => 1) (ggQ2gwE k) = 2 := ggQ2gwD4_QE
  have hB0 : ggQ2gwForm (fun _ => 1) h hli hsp α (h 0) (h 0) = 2 := by
    rw [ggQ2gwForm_self ggQ2gwD4C (fun _ => 1) h hli hsp α hα' (h 0), ggQ2gwCoord_h]
    exact hQe 0
  have hBk : ∀ k : Fin 4, ggQ2gwForm (fun _ => 1) h hli hsp α (h k) (h k) = 2 := by
    intro k
    rw [ggQ2gwForm_self ggQ2gwD4C (fun _ => 1) h hli hsp α hα' (h k), ggQ2gwCoord_h]
    exact hQe k
  have hsq : ∀ ε : ZMod 3, ε ≠ 0 → ε * ε = 1 := by decide
  have heps2 : ε * ε = 1 := hsq ε hε0
  have hBeps : ggQ2gwForm (fun _ => 1) h hli hsp α (T⁻¹ (h 0)) (T⁻¹ (h 0)) = 2 := by
    rw [hTπ 0, ggQ2gwForm_smul, heps2, one_mul,
      ggQ2gwForm_mem_weyl ggQ2gwD4C (fun _ => 1) ggQ2gwD4_symm h hli hsp α hα' hdiag hw]
    exact hBk (π 0)
  have hmu2 : μ * 2 = 2 := by
    rw [← hB0, ← hμ (h 0) (h 0), hBeps, hB0]
  have htwo : (2 : ZMod 3) * 2 = 1 := by decide
  have hμ1 : μ = 1 := by
    calc μ = μ * 2 * 2 := by rw [mul_assoc, htwo, mul_one]
      _ = 2 * 2 := by rw [hmu2]
      _ = 1 := htwo
  have hBd : ggQ2gwForm (fun _ => 1) h hli hsp α (T.symm d) (T.symm d) =
      ggQ2gwForm (fun _ => 1) h hli hsp α d d := by
    have h := hμ d d
    rw [hμ1, one_mul] at h
    rw [show T⁻¹ d = T.symm d from rfl] at h
    exact h
  calc
    ggQ2gwQ ggQ2gwD4C (fun _ => 1) (ggQ2gwCoord h hli hsp (T.symm d)) =
        ggQ2gwForm (fun _ => 1) h hli hsp α (T.symm d) (T.symm d) :=
      (ggQ2gwForm_self ggQ2gwD4C (fun _ => 1) h hli hsp α hα' (T.symm d)).symm
    _ = ggQ2gwForm (fun _ => 1) h hli hsp α d d := hBd
    _ = ggQ2gwQ ggQ2gwD4C (fun _ => 1) (ggQ2gwCoord h hli hsp d) :=
      ggQ2gwForm_self ggQ2gwD4C (fun _ => 1) h hli hsp α hα' d

theorem ggQ2GraphAbsCore_D4 : GGQ2GraphAbsCore 4 (CartanMatrix.D 4) := by
  intro U _ _ h hli hsp α hα d hd0
  have hα' : ∀ i j : Fin 4, α i (h j) = ggQ2gwD4C i j := by
    intro i j
    rw [hα i j]
    exact ggQ2gwD4C_eq i j
  have hdiag : ∀ j : Fin 4, ggQ2gwD4C j j = 2 := ggQ2gwD4_diag
  have h2 : ∀ j : Fin 4, α j (h j) = 2 := by
    intro j
    rw [hα' j j]
    exact hdiag j
  let x : Fin 4 → ZMod 3 := ggQ2gwCoord h hli hsp d
  have hx0 : x ≠ 0 := by
    intro hx
    exact hd0 ((ggQ2gwCoord h hli hsp).map_eq_zero_iff.mp hx)
  have hQ3 : ∀ q : ZMod 3, q = 0 ∨ q = 1 ∨ q = 2 := by decide
  rcases hQ3 (ggQ2gwQ ggQ2gwD4C (fun _ => 1) x) with hQ0 | hQ1 | hQ2
  ·
    right
    refine ggQ2gw_line_of_trans ggQ2gwD4C h hli hsp α hα' h2
      (fun y => y ≠ 0 ∧ ggQ2gwQ ggQ2gwD4C (fun _ => 1) y = 0) ![0, 1, 0, 2]
      (ggQ2gwD4WordOf ggQ2gwD4Word0) ?_ d ⟨hx0, hQ0⟩ ?_
    · intro y hy
      exact ggQ2gwD4_word_zero y hy.1 hy.2
    · intro T hT
      refine ⟨?_, ?_⟩
      · intro h0
        exact hd0 (T.symm.map_eq_zero_iff.mp ((ggQ2gwCoord h hli hsp).map_eq_zero_iff.mp h0))
      · rw [ggQ2gwD4_form_preserves h hli hsp α hα d T hT]
        exact hQ0
  ·
    left
    obtain ⟨E, hE, hEd⟩ := ggQ2gwD4_cover_one x hQ1
    exact ggQ2gw_kill_of_entry ggQ2gwD4C h hli hsp α hα' hdiag E
      (ggQ2gwD4Kill_ok E hE) d hEd.symm
  ·
    right
    refine ggQ2gw_line_of_trans ggQ2gwD4C h hli hsp α hα' h2
      (fun y => ggQ2gwQ ggQ2gwD4C (fun _ => 1) y = 2) ![0, 0, 0, 1]
      (ggQ2gwD4WordOf ggQ2gwD4Word2) ?_ d hQ2 ?_
    · intro y hy
      exact ggQ2gwD4_word_two y hy
    · intro T hT
      rw [ggQ2gwD4_form_preserves h hli hsp α hα d T hT]
      exact hQ2

end CFSG.StandardType

end
