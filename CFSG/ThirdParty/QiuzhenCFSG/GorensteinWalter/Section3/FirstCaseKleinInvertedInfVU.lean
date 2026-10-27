module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# An outside-inverted subgroup misses `VU`

Restriction (5) says that the identity is the only element of `VU` inverted
by an involution outside `Ĥ`.  Consequently every subgroup of `Ĥ` inverted
by that involution has trivial intersection with `VU`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If an outside involution inverts `X ≤ Ĥ`, then
`X ∩ (O₂(Ĥ) U) = 1`. -/
public theorem firstCase_klein_inverted_subgroup_inf_VU_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    {X : Subgroup G} (_hXle : X ≤ c.Hhat)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) :
    X ⊓ (twoCoreOf c.Hhat ⊔ c.U) = ⊥ := by
  classical
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  have hBcard : Nat.card {z : G // z ∈ invertedElements B y} = 1 := by
    simpa [B] using firstCase_klein_restrictionFive
      hmin c hfirst hklein y hy hyH
  apply le_antisymm
  · intro z hz
    have hzI : z ∈ invertedElements B y := ⟨hz.2, (hXinv z hz.1).2⟩
    have hone : (1 : G) ∈ invertedElements B y := ⟨B.one_mem, by simp⟩
    obtain ⟨z0, hz0⟩ := Nat.card_eq_one_iff_exists.mp hBcard
    have hzEq : (⟨z, hzI⟩ : {w : G // w ∈ invertedElements B y}) = z0 := hz0 _
    have h1Eq : (⟨1, hone⟩ : {w : G // w ∈ invertedElements B y}) = z0 := hz0 _
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (hzEq.trans h1Eq.symm))
  · exact bot_le

end CFSG.GorensteinWalter
