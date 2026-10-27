module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldPSL
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

@[expose] def K419PinPSp : Prop :=
  ∀ (r : ℕ) (F : Type) [Field F] [Finite F], (3 ≤ r ∨ (r = 2 ∧ ringChar F ≠ 2)) →
    IsList46 (StatedProj (StatedSp r F)) → (Nat.card F).Prime

theorem k419OneFieldPSp_of_pin (hpin : K419PinPSp) : K419OneFieldPSp := by
  intro G _ _ L hL h46 r F _ _ hr x a hx3 hxa hxk haL ha3 haC hdiag K hKle hKc ht
  obtain ⟨e, σ, hσ⟩ : ∃ (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp r F))
      (σ : F ≃+* F), σ ≠ 1 := by
    rcases hxk with ⟨e, hx, hk⟩ | ⟨e, hx, hk⟩
    · obtain ⟨φ, ⟨σ, rfl⟩, h1, -⟩ := hk
      exact ⟨e, σ, fun h => h1 (by rw [h, map_one])⟩
    · obtain ⟨γ, hγ, -⟩ := hk
      exact absurd hγ (Set.notMem_empty γ)
  have hlist : IsList46 (StatedProj (StatedSp r F)) :=
    CFSG.RankThree.PartTwo.Sec21.Item223PrintProof.isList46_of_mulEquiv e h46
  exact hσ (HeringOF.ringEquiv_eq_one_of_prime_card (hpin r F hr hlist) σ)

end CFSG.RankThree.PartTwo.Sec4
