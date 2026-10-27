module

import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.LieType.Universal.Spin

theorem w135c2_omMinus_model
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) {n f : ℕ} (hn : 4 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (b c : F), Nat.card F = 2 ^ f ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧ Subgroup.center ↥L = ⊥ ∧
      Nonempty (spinGroup (quadMinus n F b c) ≃* ↥L) := by
  classical
  obtain ⟨-, F, instF, instFin, hF, b, c, hirr, ⟨eZ⟩⟩ :=
    LieModel.statedClassicalModel hlie (by decide)
  let instField : Field F := instF
  let instFiniteF : Finite F := instFin
  let instFintypeF : Fintype F := Fintype.ofFinite F
  let instFactPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let instCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hZ : Subgroup.center ↥L = ⊥ := by
    let instPerfect : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1
    exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_nonsplit_orthogonal (n := n) hn hirr
      (hodd := w135_odd_card_center hctx) eZ
  let q : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e : spinGroup (quadMinus n F b c) ≃* ↥L :=
    (CFSG.SeitzReduction.SeitzQ2.spinMinusEquivStatedProj (K := F) hn hirr).trans
      (q.symm.trans eZ).symm
  exact ⟨F, instField, instFiniteF, instCharP, b, c, hF, hirr, hZ, ⟨e⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
