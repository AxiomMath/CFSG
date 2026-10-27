module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Triple
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed points of a nonidentity element of `PSL₂`

Sharp three-transitivity of the natural `PGL₂` action implies that a
nonidentity element of `PSL₂` fixes at most two projective-line points.
This is the point-action form of the bound on normalized defining-
characteristic Sylow subgroups.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

/-- A nonidentity element of `PSL₂(K)` fixes at most two points of the
projective line. -/
public theorem psl2_fixedPoint_card_le_two
    (K : Type u) [Field K] [Finite K]
    (g : PSL2 K) (hg : g ≠ 1) :
    Nat.card {x : PSL2ProjectiveLine K // g • x = x} ≤ 2 := by
  classical
  by_contra hle
  have hthree : 3 ≤
      Nat.card {x : PSL2ProjectiveLine K // g • x = x} := by
    omega
  let : Fintype {x : PSL2ProjectiveLine K // g • x = x} :=
    Fintype.ofFinite _
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 3) ≤
        Fintype.card {x : PSL2ProjectiveLine K // g • x = x} by
      simpa using hthree)
  let a : PSL2ProjectiveLine K := (f 0).1
  let b : PSL2ProjectiveLine K := (f 1).1
  let c : PSL2ProjectiveLine K := (f 2).1
  have hab : a ≠ b := by
    intro h
    have hf : f 0 = f 1 := Subtype.ext h
    have : (0 : Fin 3) = 1 := f.injective hf
    omega
  have hac : a ≠ c := by
    intro h
    have hf : f 0 = f 2 := Subtype.ext h
    have : (0 : Fin 3) = 2 := f.injective hf
    omega
  have hbc : b ≠ c := by
    intro h
    have hf : f 1 = f 2 := Subtype.ext h
    have : (1 : Fin 3) = 2 := f.injective hf
    omega
  obtain ⟨_z, _hz, huniq⟩ := pgl2_sharply_three_transitive K
    a b c a b c hab hac hbc hab hac hbc
  have hgfix :
      Matrix.ProjectiveSpecialLinearGroup.toPGL g • a = a ∧
      Matrix.ProjectiveSpecialLinearGroup.toPGL g • b = b ∧
      Matrix.ProjectiveSpecialLinearGroup.toPGL g • c = c := by
    simpa [a, b, c, psl2ToPGL_smul] using
      And.intro (f 0).2 (And.intro (f 1).2 (f 2).2)
  have honefix :
      (1 : PGL2 K) • a = a ∧
      (1 : PGL2 K) • b = b ∧
      (1 : PGL2 K) • c = c := by
    simp
  have heq : Matrix.ProjectiveSpecialLinearGroup.toPGL g =
      (1 : PGL2 K) :=
    (huniq _ hgfix).trans (huniq _ honefix).symm
  apply hg
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  simpa using heq

end CFSG.GorensteinWalter
