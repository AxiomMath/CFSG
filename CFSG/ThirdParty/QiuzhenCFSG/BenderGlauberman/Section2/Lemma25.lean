module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma25Core

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Lemma 2.5

The statement of Lemma 2.5: if `m ≥ 4` and `λ̃₃(t) = 2λ₃(t)`, then the
non-trivial constituent `φ` of `1̃_{H0}` satisfies `φ(t) = 1` and
`2/3 ≤ 1−3/φ(1) < 2k²|G:H|⁻¹ < 2`.  The proof helpers (including the slow
Lemma-2.2 sum evaluation) live in `BenderGlauberman.Section2.Lemma25Core`;
this module re-exports the core and assembles `lemma_2_5` from
`lemma_2_5_assembly`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section2

variable {G : Type u} [Group G] [Finite G]
variable (c : Hyp11 G)

/-- Lemma 2.5: if `m ≥ 4` and `λ̃₃(t) = 2λ₃(t)`, then the non-trivial
constituent `φ` of `1̃_{H0}` satisfies `φ(t) = 1` and
`2/3 ≤ 1−3/φ(1) < 2k²|G:H|⁻¹ < 2`. -/
public theorem lemma_2_5 (c : Hyp11 G) (h12 : Hyp12 c) {l3 : LambdaHom c.H0 c.U}
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index) (hl3 : l3 ^ 2 ≠ 1)
    (hl3t : tildeNu c h12 ⟨LambdaChar l3.1, (isLinearCharacter_of_hom l3.1).1⟩ c.t =
      2 * (l3.1 (tH0 c) : ℂ)) :
    ∃ φ : ClassFunction G,
      IsConstituentOf φ (tildeNu c h12 ⟨(1 : ClassFunction (↥c.H0)),
        (isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)).1⟩) ∧
      φ ≠ 1 ∧ φ c.t = 1 ∧
      (2 / 3 : ℝ) ≤ 1 - 3 / (φ 1).re ∧
      1 - 3 / (φ 1).re < ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) ∧
      ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) < (2 : ℝ) := by
  exact lemma_2_5_assembly c h12 hm hl3 hl3t


end Section2

end CFSG.BenderGlauberman
