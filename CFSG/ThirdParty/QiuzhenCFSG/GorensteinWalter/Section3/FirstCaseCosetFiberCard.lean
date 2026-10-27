module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount

namespace CFSG
end CFSG
open CFSG

/-!
# The first-case coset fibre

The source writes the number of involutions in `Ĥ x` directly as a coset
count.  The generic involution projection uses the corresponding fibre of
`x ↦ x⁻¹ mod Ĥ`; this theorem identifies the two cardinalities.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem cosetInvolution_base_eq_mem
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (x : G) :
    cosetInvolution_proj c.Hhat x = cosetInvolution_base c.Hhat ↔ x ∈ c.Hhat := by
  unfold cosetInvolution_proj cosetInvolution_base
  rw [QuotientGroup.eq]
  simp

/-- The source coset count equals the cardinality of the generic coset fibre. -/
public theorem firstCase_coset_fiber_card_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {x : G} (hx : IsInvolution x) :
    firstCaseCosetInvolutions c x =
      Nat.card (cosetInvolution_fiber c.Hhat
        (cosetInvolution_proj c.Hhat x)) := by
  unfold firstCaseCosetInvolutions cosetInvolution_fiber
  have h1 := involution_coset_fiber_card c.Hhat hx
  have h2 := Nat.card_congr (involution_coset_fiber_equiv_inverted c.Hhat hx)
  exact h1.trans h2.symm

end CFSG.GorensteinWalter
