module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCosetFiberCard
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount

namespace CFSG
end CFSG
open CFSG

/-!
# The first-case `J_n` fibres

The source's `J_n` is the generic non-base involution fibre for the coset
projection over `G ⧸ Ĥ`.  This gives the exact cardinality identity needed for
the first line of the source count.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The source `J_n` has the same cardinality as the generic coset `J_n`. -/
public theorem firstCase_J_n_card_eq_cosetInvolution
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (n : ℕ) :
    Nat.card {x : G // x ∈ firstCaseJ c n} =
      Nat.card (cosetInvolution_J_n c.Hhat n) := by
  classical
  let e : {x : G // x ∈ firstCaseJ c n} ≃ cosetInvolution_J_n c.Hhat n := by
    refine {
      toFun := fun x => ⟨x.1, ?_⟩
      invFun := fun x => ⟨x.1, ?_⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    · rcases x.2 with ⟨hx, hxout, hxn⟩
      refine ⟨hx, ?_, ?_⟩
      · intro hbase
        have hmem : x.1 ∈ c.Hhat := by
          unfold cosetInvolution_proj cosetInvolution_base at hbase
          rw [QuotientGroup.eq] at hbase
          simpa using hbase
        exact hxout hmem
      · change Nat.card (cosetInvolution_fiber c.Hhat
          (cosetInvolution_proj c.Hhat x.1)) = n
        rw [← firstCase_coset_fiber_card_eq c hx]
        exact hxn
    · rcases x.2 with ⟨hx, hxout, hxn⟩
      refine ⟨hx, ?_, ?_⟩
      · intro hmem
        apply hxout
        have hbase :
            cosetInvolution_proj c.Hhat x.1 = cosetInvolution_base c.Hhat := by
          unfold cosetInvolution_proj cosetInvolution_base
          rw [QuotientGroup.eq]
          simpa using hmem
        exact hbase
      · rw [firstCase_coset_fiber_card_eq c x.2.1]
        exact hxn
  exact Nat.card_congr e

/-- The source identity `|J_n| = n b_n`, using the generic coset count. -/
public theorem firstCase_J_n_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (n : ℕ) :
    Nat.card {x : G // x ∈ firstCaseJ c n} =
      n * cosetInvolution_b c.Hhat n := by
  rw [firstCase_J_n_card_eq_cosetInvolution]
  exact cosetInvolution_J_n_card c.Hhat n

end CFSG.GorensteinWalter
