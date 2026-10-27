module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType.GGKG3.K3dCheck

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.E6 CFSG.LieType.SeitzGeneration

@[expose] def dot6 (x y : Fin 6 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5

@[expose] def mv (M : Fin 6 → Fin 6 → ℤ) (x : Fin 6 → ℤ) : Fin 6 → ℤ := fun i =>
  M i 0 * x 0 + M i 1 * x 1 + M i 2 * x 2 + M i 3 * x 3 + M i 4 * x 4 + M i 5 * x 5

@[expose] def kC : Fin 6 → Fin 6 → ℤ := fun i j => (Tag.E6.cartan i j)

@[expose] def kMw : Fin 6 → Fin 6 → ℤ := fun i j => (e6ThreeMat.getD i []).getD j 0

@[expose] def kAdjC : Fin 6 → Fin 6 → ℤ := fun i j =>
  (([[4, 3, 5, 6, 4, 2], [3, 6, 6, 9, 6, 3], [5, 6, 10, 12, 8, 4], [6, 9, 12, 18, 12, 6],
    [4, 6, 8, 12, 10, 5], [2, 3, 4, 6, 5, 4]] : List (List ℤ)).getD i []).getD j 0

@[expose] def kN (γ δ : Fin 6 → ℤ) : ℤ × (Fin 6 → Fin 6 → ℤ) :=
  let u : Fin 6 → ℤ := fun i => γ i - δ i
  let v := mv kMw u
  let uC := mv kC u
  let vC := mv kC v
  let guu := dot6 u uC
  let guv := dot6 u vC
  let gvv := dot6 v vC
  let D := guu * gvv - guv * guv
  (D, fun i j => (if i = j then D else 0) -
    2 * (u i * (gvv * uC j - guv * vC j) + v i * (guu * vC j - guv * uC j)))

@[expose] def k3dBad (γ δ : Fin 6 → ℤ) : Bool :=
  let nd := kN γ δ
  let D := nd.1
  let N := nd.2
  decide (D ≠ 0) &&
    (List.finRange 6).all (fun i => (List.finRange 6).all (fun j => decide (D ∣ N i j))) &&
    (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      decide (3 * D ∣ ((N i 0 - if i = 0 then D else 0) * kAdjC 0 j +
        (N i 1 - if i = 1 then D else 0) * kAdjC 1 j +
        (N i 2 - if i = 2 then D else 0) * kAdjC 2 j +
        (N i 3 - if i = 3 then D else 0) * kAdjC 3 j +
        (N i 4 - if i = 4 then D else 0) * kAdjC 4 j +
        (N i 5 - if i = 5 then D else 0) * kAdjC 5 j))))

@[expose] def k3Roots : List (Fin 6 → ℤ) := (List.range 72).map e6Certificate.root

theorem k3d_check :
    (k3Roots.all fun γ => k3Roots.all fun δ => (γ == δ) || !k3dBad γ δ) = true := by
  decide +kernel

theorem k3d_gram_ne :
    (k3Roots.all fun γ => k3Roots.all fun δ => (γ == δ) || decide ((kN γ δ).1 ≠ 0)) = true := by
  decide +kernel

theorem k3dBad_eq_false {γ δ : Fin 6 → ℤ} (hγ : γ ∈ k3Roots) (hδ : δ ∈ k3Roots) (h : γ ≠ δ) :
    k3dBad γ δ = false := by
  have := k3d_check
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  rcases this γ hγ δ hδ with h' | h'
  · exact absurd h' h
  · exact h'

theorem kN_fst_ne_zero {γ δ : Fin 6 → ℤ} (hγ : γ ∈ k3Roots) (hδ : δ ∈ k3Roots) (h : γ ≠ δ) :
    (kN γ δ).1 ≠ 0 := by
  have := k3d_gram_ne
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this γ hγ δ hδ with h' | h'
  · exact absurd h' h
  · exact h'

end CFSG.StandardType.GGKG3.K3dCheck
