module

public import CFSG.Blueprint.ChevalleyRootsInputs
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType.LatPerpChecks

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def ggCertMatList : (τ : Tag) → List (List (List ℤ))
  | .F4 => [
      [[1, 0, 0, 0], [1, 2, 2, 0], [0, 0, 0, 1], [0, 0, 1, 0]],
      [[0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 2, 0], [1, 1, 1, 0]],
      [[0, 1, 2, 2], [0, 1, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]],
      [[1, 0, 0, 0], [0, 1, 2, 1], [0, 1, 0, 0], [0, 0, 1, 0]]]
  | .E6 => [
      [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [1, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 1]],
      [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 1, 2, 1, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
      [[1, 0, 1, 1, 0, 0], [0, 1, 1, 2, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
      [[1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 0, 0]],
      [[1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 1, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 1, 1]],
      [[0, 1, 1, 2, 2, 1], [1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0]]]
  | .E7 => [
      [[1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 2, 2, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0]],
      [[0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 1, 2, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0]],
      [[0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 1, 0, 0]],
      [[0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]],
      [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 1, 1, 2, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0]],
      [[0, 0, 0, 1, 0, 0, 0], [0, 1, 1, 2, 2, 1, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 1]],
      [[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 1, 2, 2, 2, 1], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]]]
  | .E8 => [
      [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 2, 2, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
      [[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
      [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0], [0, 1, 1, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
      [[0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
      [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 1, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 1, 0, 0]],
      [[0, 1, 1, 2, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0]],
      [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 2, 2, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
      [[0, 1, 1, 2, 2, 2, 2, 1], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]
  | _ => []

@[expose] def ggCertA0List : (τ : Tag) → List (List ℤ)
  | .F4 => [[1, 2, 2, 0], [0, 0, 0, 1], [0, 1, 2, 2], [1, 0, 0, 0]]
  | .E6 => [[0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 2, 1]]
  | .E7 => [[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]]
  | .E8 => [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 2, 2, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 1, 2, 2, 2, 2, 1]]
  | _ => []

@[expose] def ggCertDetList : (τ : Tag) → List ℤ
  | .F4 => [-2, 1, 2, 1]
  | .E6 => [-2, -2, 1, -1, 1, 1]
  | .E7 => [2, -2, -1, 1, -1, -1, 1]
  | .E8 => [-2, 2, -1, -1, 1, -1, -1, 1]
  | _ => []

@[expose] def ggVec {n : ℕ} (l : List ℤ) : Fin n → ℤ := fun i => l.getD i.val 0

@[expose] def ggMat {n : ℕ} (l : List (List ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (l.getD i.val []).getD j.val 0

@[expose] def ggCertMat (τ : Tag) (j : Fin τ.rank) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  ggMat ((ggCertMatList τ).getD j.val [])

@[expose] def ggCertA0 (τ : Tag) (j : Fin τ.rank) : Fin τ.rank → ℤ :=
  ggVec ((ggCertA0List τ).getD j.val [])

@[expose] def ggCertDet (τ : Tag) (j : Fin τ.rank) : ℤ :=
  (ggCertDetList τ).getD j.val 0

@[expose] def ggDList : Tag → List ℤ
  | .G2 => [3, 1]
  | .F4 => [2, 2, 1, 1]
  | _ => [1]

@[expose] def ggD (τ : Tag) (i : Fin τ.rank) : ℤ := (ggDList τ).getD i.val 1

@[expose] def ggB (τ : Tag) (i j : Fin τ.rank) : ℤ := ggD τ i * Tag.cartan τ i j

theorem ggB_eq (τ : Tag) (i j : Fin τ.rank) : ggB τ i j = Tag.symmetrizedCartan τ i j := by
  cases τ <;> fin_cases i <;> fin_cases j <;> decide +kernel

@[expose] def ggGram (τ : Tag) (α β : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, ∑ j, α i * ggB τ i j * β j

@[expose] def ggRootList (τ : Tag) : List (Fin τ.rank → ℤ) :=
  (List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root

@[expose] def ggPerpFinset (τ : Tag) (α : Fin τ.rank → ℤ) : Finset (Fin τ.rank → ℤ) :=
  (rootFinset τ).filter fun β => ggGram τ α β == 0

@[expose] def ggPerpList (τ : Tag) (α : Fin τ.rank → ℤ) : List (Fin τ.rank → ℤ) :=
  (ggRootList τ).filter fun β => ggGram τ α β == 0

@[expose] def ggCartInt (τ : Tag) (α β : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, β i * (2 * ggGram τ (Pi.single i 1) α / ggGram τ α α)

@[expose] def ggMulB (τ : Tag) (α : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun j => ∑ i, α i * ggB τ i j

@[expose] def ggPairVec {N : ℕ} (m β : Fin N → ℤ) : ℤ := ∑ j, m j * β j

@[expose] def ggCartRow (τ : Tag) (α : Fin τ.rank → ℤ) : Bool :=
  let w := ggMulB τ α
  let den := ggPairVec w α
  (ggRootList τ).all fun β =>
    let c := ∑ i, β i * (2 * (∑ k, ggB τ i k * α k) / den)
    decide (-2 ≤ c ∧ c ≤ 2 ∧ (c = 0 ↔ ggPairVec w β = 0))

@[expose] def ggCartCheck (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun j => ggCartRow τ (Pi.single j 1)

@[expose] def ggConnCheck (τ : Tag) (α a₀ : Fin τ.rank → ℤ) : Bool :=
  let am := ggMulB τ α
  let a0m := ggMulB τ a₀
  let plist := ggPerpList τ α
  let neigh := (plist.filter fun γ => decide (ggPairVec a0m γ ≠ 0)).map fun γ =>
    (γ, ggMulB τ γ)
  decide (ggPairVec am a₀ = 0) &&
    plist.all fun β =>
      decide (ggPairVec a0m β ≠ 0) ||
      neigh.any fun p => decide (ggPairVec p.2 β ≠ 0)

@[expose] def ggBasisCheck (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun j =>
    ggConnCheck τ (Pi.single j 1) (ggCertA0 τ j) &&
    decide (ggCertA0 τ j ∈ ggRootList τ) &&
    decide (7 ≤ (ggPerpFinset τ (Pi.single j 1)).card) &&
    ((List.finRange τ.rank).all fun k =>
      decide (k = j) || (decide (ggCertMat τ j k ∈ ggRootList τ) &&
        decide (ggGram τ (Pi.single j 1) (ggCertMat τ j k) = 0))) &&
    decide (ggCertDet τ j = 1 ∨ ggCertDet τ j = -1 ∨ ggCertDet τ j = 2 ∨ ggCertDet τ j = -2)

theorem ggCartCheck_F4 : ggCartCheck .F4 = true := by decide +kernel
theorem ggCartCheck_E6 : ggCartCheck .E6 = true := by decide +kernel
theorem ggCartCheck_E7 : ggCartCheck .E7 = true := by decide +kernel
theorem ggCartCheck_E8 : ggCartCheck .E8 = true := by decide +kernel

theorem ggBasisCheck_F4 : ggBasisCheck .F4 = true := by decide +kernel
theorem ggBasisCheck_E6 : ggBasisCheck .E6 = true := by decide +kernel
theorem ggBasisCheck_E7 : ggBasisCheck .E7 = true := by decide +kernel
theorem ggBasisCheck_E8 : ggBasisCheck .E8 = true := by decide +kernel

theorem ggCertMat_laplace (τ : Tag) (j : Fin τ.rank) :
    laplaceDet τ.rank (ggCertMat τ j) = ggCertDet τ j := by
  cases τ <;> fin_cases j <;> decide +kernel

end CFSG.StandardType.LatPerpChecks
