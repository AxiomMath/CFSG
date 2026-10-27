module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4 shared component-quotient vocabulary

These definitions are owned by `GorensteinWalter.Section4.Defs` so that the
per-theorem Section 4 modules can state their theorems without importing
`GorensteinWalter.Section4.Basic` (which will import them at landing).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The two component quotients left by the `D`-group classification of a
proper maximal subgroup: `A₇` or `PSL(2,q)` for odd `q`. -/
public inductive ComponentQuotientModel
    {G : Type u} [Group G] (E : Subgroup G) : Prop
  | alternating
      (e : Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)))
  | projectiveSpecialLinear
      (K : Type u) [Field K] [Finite K]
      (hKprimePower : IsOddPrimePower (Nat.card K))
      (e : Nonempty ((E ⧸ Subgroup.center E) ≃* PSL2 K))

/-- The component selected in the second case. -/
public structure SecondCaseComponentData
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c) where
  E : Subgroup G
  E_component : IsComponentOf E w.M
  t_mem_E : c.t ∈ E
  model : ComponentQuotientModel E
  E_normal : IsNormalIn E w.M
  center_odd : Odd (Nat.card (Subgroup.center E))

/-- The numerical parameters retained from the `PSL(2,q)` branch.  The last
conjunct is the inequality obtained from equations (10)--(12) on page 228. -/
@[expose] public def LinearCaseContradictionData : Prop :=
  ∃ q k k' p p0 p1 u : ℕ,
    7 ≤ q ∧
      Even k ∧
        Odd k' ∧
          (3 ≤ p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k) ∧
            u ≤ p ∧
              q * (q - 4) < 7

end CFSG.GorensteinWalter
