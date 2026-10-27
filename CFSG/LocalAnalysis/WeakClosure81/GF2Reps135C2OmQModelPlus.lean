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

theorem w135c2_omPlus_model
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) {n f : ℕ} (hn : 3 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
      Subgroup.center ↥L = ⊥ ∧ Nonempty (spinGroup (quadPlus n F) ≃* ↥L) := by
  classical
  obtain ⟨-, F, instF, instFin, hF, ⟨eZ⟩⟩ := LieModel.statedClassicalModel hlie (by decide)
  let instField : Field F := instF
  let instFiniteF : Finite F := instFin
  let instFintypeF : Fintype F := Fintype.ofFinite F
  let instFactPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let instCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hZ : Subgroup.center ↥L = ⊥ := by
    let instPerfect : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1
    exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_split_orthogonal (n := n) hn
      (hodd := w135_odd_card_center hctx) eZ
  let q : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e : spinGroup (quadPlus n F) ≃* ↥L :=
    (CFSG.SeitzReduction.SeitzQ2.spinPlusEquivStatedProj hn F).trans
      (q.symm.trans eZ).symm
  exact ⟨F, instField, instFiniteF, instCharP, hF, hZ, ⟨e⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
