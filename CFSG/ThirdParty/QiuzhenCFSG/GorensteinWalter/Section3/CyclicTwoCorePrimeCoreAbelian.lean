module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter
universe u

/-- In the cyclic first case, the selected odd core `P = O_p(U)` is abelian:
`t₂` inverts `P`, so inversion is an automorphism of `P`. -/
public theorem firstCase_cyclic_primeCore_abelian
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c) :
    IsMulCommutative (↥(qCoreOf od.d.bg.U od.p)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [isMulCommutative_iff]
  intro a b
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have h1 : od.d.bg.t2 * ((a : G) * (b : G)) * od.d.bg.t2⁻¹ =
      ((a : G) * (b : G))⁻¹ :=
    firstCase_t2_inverts_primeCore c od ((a : G) * (b : G)) (P.mul_mem a.2 b.2)
  have h2 : od.d.bg.t2 * (a : G) * od.d.bg.t2⁻¹ = (a : G)⁻¹ :=
    firstCase_t2_inverts_primeCore c od (a : G) a.2
  have h3 : od.d.bg.t2 * (b : G) * od.d.bg.t2⁻¹ = (b : G)⁻¹ :=
    firstCase_t2_inverts_primeCore c od (b : G) b.2
  have hconj : od.d.bg.t2 * ((a : G) * (b : G)) * od.d.bg.t2⁻¹ =
      (od.d.bg.t2 * (a : G) * od.d.bg.t2⁻¹) *
        (od.d.bg.t2 * (b : G) * od.d.bg.t2⁻¹) := by group
  have hconj' : od.d.bg.t2 * ((a : G) * (b : G)) * od.d.bg.t2⁻¹ =
      (a : G)⁻¹ * (b : G)⁻¹ := by
    simpa [h2, h3] using hconj
  have hab : (a : G)⁻¹ * (b : G)⁻¹ = (b : G)⁻¹ * (a : G)⁻¹ := by
    calc
      (a : G)⁻¹ * (b : G)⁻¹ =
          od.d.bg.t2 * ((a : G) * (b : G)) * od.d.bg.t2⁻¹ := hconj'.symm
      _ = ((a : G) * (b : G))⁻¹ := h1
      _ = (b : G)⁻¹ * (a : G)⁻¹ := by group
  apply Subtype.ext
  have hinv : ((a : G)⁻¹ * (b : G)⁻¹)⁻¹ =
      ((b : G)⁻¹ * (a : G)⁻¹)⁻¹ := congrArg (fun z : G => z⁻¹) hab
  change (a : G) * (b : G) = (b : G) * (a : G)
  simpa using hinv.symm

end CFSG.GorensteinWalter
