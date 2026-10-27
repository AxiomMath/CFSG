module

public import CFSG.Quasithin.Background.KG82CoverModel

public section

namespace CFSG.Quasithin.H.L34Cov

open CFSG.ComponentClassification.GrSLit.L34Facts

structure StdData where
  p : ℕ
  K : List ℕ
  pW : List (List ℕ)
  eW : List (List ℕ)
  vW : List (List ℕ)
  nB : List (List (List ℕ))
  nBi : List (List (List ℕ))
  yW : List ℕ
  xB : List (List ℕ)
  dE : List (List ℕ)
  dV : List (List ℕ)
  hW : List ℕ
  aW : List (List ℕ)
  bW : List (List ℕ)

@[expose] def StdData.AV (d : StdData) : List (List ℕ) :=
  [[], d.vW.getD 0 [], d.vW.getD 1 [], d.vW.getD 0 [] ++ d.vW.getD 1 []]

@[expose] def StdFix (d : StdData) : Prop :=
  d.p < 42 ∧ (∀ k ∈ d.K, k < 42) ∧
    (∀ w ∈ d.eW ++ d.vW ++ [d.yW, d.hW] ++ d.aW ++ d.bW ++ wT₀, (wordL w).getD d.p 0 = d.p) ∧
    ∀ w ∈ d.eW, ∀ k ∈ d.K, (wordL w).getD k 0 = k

@[expose] def StdAb (d : StdData) : Prop :=
  (∀ u ∈ d.eW, ∀ v ∈ d.eW, wordL (u ++ v) = wordL (v ++ u)) ∧
    (∀ u ∈ d.eW, wordL (u ++ u) = List.range 42) ∧
    (∀ u ∈ d.vW, ∀ v ∈ d.vW, wordL (u ++ v) = wordL (v ++ u)) ∧
    (∀ u ∈ d.vW, wordL (u ++ u) = List.range 42) ∧ d.vW.length = 2

@[expose] def StdNorm (d : StdData) : Prop :=
  ∀ k < d.pW.length, ∀ j < d.eW.length,
    wordL (d.pW.getD k [] ++ d.eW.getD j [] ++ invW (d.pW.getD k [])) =
        wordL (prodW d.eW ((d.nB.getD k []).getD j [])) ∧
      wordL (invW (d.pW.getD k []) ++ d.eW.getD j [] ++ d.pW.getD k []) =
        wordL (prodW d.eW ((d.nBi.getD k []).getD j [])) ∧
      (∀ i ∈ (d.nB.getD k []).getD j [], i < d.eW.length) ∧
      ∀ i ∈ (d.nBi.getD k []).getD j [], i < d.eW.length

@[expose] def StdComm (d : StdData) : Prop :=
  (∀ j < d.eW.length,
    wordL (prodW d.eW (d.xB.getD j []) ++ d.yW ++ invW (prodW d.eW (d.xB.getD j [])) ++
        invW d.yW) = wordL (d.eW.getD j []) ∧
      ∀ i ∈ d.xB.getD j [], i < d.eW.length) ∧
    ∀ k < wT₀.length,
      wordL (wT₀.getD k []) = wordL (prodW d.eW (d.dE.getD k []) ++ prodW d.vW (d.dV.getD k [])) ∧
        (∀ i ∈ d.dE.getD k [], i < d.eW.length) ∧ ∀ i ∈ d.dV.getD k [], i < d.vW.length

@[expose] def StdV (d : StdData) : Prop :=
  (∀ g ∈ d.vW, ∀ a ∈ d.AV, ∃ a' ∈ d.AV, wordL (g ++ a) = wordL a') ∧
    (∀ g ∈ d.vW, ∀ a ∈ d.AV, ∃ a' ∈ d.AV, wordL (invW g ++ a) = wordL a') ∧
    ∀ b ∈ d.AV, b ≠ [] → ∀ b' ∈ d.AV,
      ∃ k ∈ d.K, (wordL (invW d.hW ++ b ++ d.hW ++ invW b')).getD k 0 ≠ k

@[expose] def StdPerf (d : StdData) : Prop :=
  ∀ k < d.pW.length,
    wordL (d.aW.getD k [] ++ d.bW.getD k [] ++ invW (d.aW.getD k []) ++
      invW (d.bW.getD k [])) = wordL (d.pW.getD k [])

@[expose] def StdOk (d : StdData) : Prop :=
  StdFix d ∧ StdAb d ∧ StdNorm d ∧ StdComm d ∧ StdV d ∧ StdPerf d

@[expose] def std₁ : StdData where
  p := 2
  K := [2, 23, 26, 31, 36, 41]
  pW := wP₁
  eW := [[0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 1, 0, 0], [1, 2, 0, 2, 0, 1, 0, 2, 0, 2],
    [2, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 2]]
  vW := [[0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 1, 0, 0, 2, 0, 1, 0, 0]]
  nB := [[[0, 2, 3], [1, 3], [0, 1], [1]], [[0], [1], [0, 1, 2], [1, 3]],
    [[0], [1], [0, 2], [0, 1, 3]]]
  nBi := [[[2, 3], [3], [0, 1, 2], [1, 3]], [[0], [1], [0, 1, 2], [1, 3]],
    [[0], [1], [0, 2], [0, 1, 3]]]
  yW := [1, 0, 1]
  xB := [[0, 2, 3], [1, 3], [0, 1], [1]]
  dE := [[2, 3], [], [], [1]]
  dV := [[0], [1], [0], []]
  hW := [1, 0, 1]
  aW := [[1, 0, 1, 1, 0, 1], [0, 0, 2, 0], [0, 0, 1, 0]]
  bW := [[0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0],
    [1, 0, 1, 0, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 1],
    [1, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 2, 0, 1, 0, 1]]

@[expose] def std₂ : StdData where
  p := 23
  K := [23, 2, 5, 10, 15, 20]
  pW := wP₂
  eW := [[0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 1, 0, 0, 2, 0, 1, 0, 0],
    [0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 2, 0], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]]
  vW := [[0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 1, 0, 0]]
  nB := [[[0], [1], [0, 1, 2], [0, 3]], [[0], [1], [0, 2], [1, 3]],
    [[3], [2, 3], [0, 1, 2], [0, 3]]]
  nBi := [[[0], [1], [0, 1, 2], [0, 3]], [[0], [1], [0, 2], [1, 3]],
    [[0, 3], [1, 2, 3], [0, 1], [0]]]
  yW := [0, 0, 1, 0, 1, 0]
  xB := [[3], [2, 3], [0, 1, 2], [0, 3]]
  dE := [[0], [1], [0], []]
  dV := [[0], [], [], [1]]
  hW := [1]
  aW := [[2], [1], [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0]]
  bW := [[0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 2, 0, 0, 1, 0, 1, 0],
    [0, 0, 1, 0, 1, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0],
    [1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1]]

theorem std₁_fix : StdFix std₁ := by
  unfold StdFix
  decide +kernel

theorem std₁_ab : StdAb std₁ := by
  unfold StdAb
  decide +kernel

theorem std₁_norm : StdNorm std₁ := by
  unfold StdNorm
  decide +kernel

theorem std₁_comm : StdComm std₁ := by
  unfold StdComm
  decide +kernel

theorem std₁_v : StdV std₁ := by
  unfold StdV
  decide +kernel

theorem std₁_perf : StdPerf std₁ := by
  unfold StdPerf
  decide +kernel

theorem std₁_ok : StdOk std₁ :=
  ⟨std₁_fix, std₁_ab, std₁_norm, std₁_comm, std₁_v, std₁_perf⟩

theorem std₂_fix : StdFix std₂ := by
  unfold StdFix
  decide +kernel

theorem std₂_ab : StdAb std₂ := by
  unfold StdAb
  decide +kernel

theorem std₂_norm : StdNorm std₂ := by
  unfold StdNorm
  decide +kernel

theorem std₂_comm : StdComm std₂ := by
  unfold StdComm
  decide +kernel

theorem std₂_v : StdV std₂ := by
  unfold StdV
  decide +kernel

theorem std₂_perf : StdPerf std₂ := by
  unfold StdPerf
  decide +kernel

theorem std₂_ok : StdOk std₂ :=
  ⟨std₂_fix, std₂_ab, std₂_norm, std₂_comm, std₂_v, std₂_perf⟩

@[expose] def triW : List (List ℕ) :=
  let e₀ := std₁.eW.getD 0 []
  let e₁ := std₁.eW.getD 1 []
  let e₂ := std₁.eW.getD 2 []
  [e₀, e₁, e₂, e₀ ++ e₁, e₀ ++ e₂, e₁ ++ e₂, e₀ ++ (e₁ ++ e₂)]

theorem triW_ne : ∀ w ∈ triW, wordL w ≠ List.range 42 := by
  unfold triW
  decide +kernel

end CFSG.Quasithin.H.L34Cov
