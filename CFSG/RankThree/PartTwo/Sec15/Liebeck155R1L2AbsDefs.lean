module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

structure Res1L2Abs (P : Type*) [Group P] [Finite P] (Y : Type*) [Group Y] (p : ℕ) where
  hp : p.Prime
  hp5 : 5 ≤ p
  n : ℕ
  hn4 : 4 ≤ n
  hn : 4 ∣ n
  e : Nonempty (Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))
  ρ : P →* MulAut Y
  hinn : ∀ y : Y, ∃ u : P, ρ u = MulAut.conj y
  Θ : Subgroup P
  hΘn : Θ.Normal
  hΘker : Θ ≤ ρ.ker
  hker : ∀ X : Subgroup P, X ≤ ρ.ker → IsPGroup p X → X ≤ Θ
  j : P
  hj : j ^ p = 1
  hρj : ρ j ≠ 1
  hjinn : ∃ y : Y, ρ j = MulAut.conj y
  z : P
  hzj : z * j * z⁻¹ = j⁻¹
  M : Subgroup P
  hzM : z ∈ M
  hjM : j ∈ M
  hCM : Subgroup.centralizer ({j} : Set P) ≤ M
  U : Sylow 2 Y
  hBorel : ∀ w ∈ M, ∀ u ∈ (U : Subgroup Y), ρ w u ∈ (U : Subgroup Y)
  hrank : ∀ E : Subgroup P, E ≤ M → CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p ^ 2
  hloc : CFSG.Assembly.RankThreeEven.localRank p P < 3
  Cc : Subgroup P
  hCcM : ∀ m ∈ M, ∀ x ∈ Cc, m * x * m⁻¹ ∈ Cc
  hzCc : z ∈ Cc
  hCT : ∀ x ∈ Cc ⊓ Θ, z * x * z⁻¹ = x

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
