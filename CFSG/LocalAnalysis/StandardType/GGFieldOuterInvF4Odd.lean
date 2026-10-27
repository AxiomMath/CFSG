module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvF4OddModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.Open (IsElemAbelian)

theorem ggFieldOuterInvF4Odd_holds
    : GGFieldOuterInvF4Odd := by
  intro G _ _ p B Bs x L D J n f ψ hf hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb hrnot
  obtain ⟨m, rfl⟩ := hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have hπker : (MonoidHom.id (ggU .F4 n (2 * m + 1)).K).ker =
      Subgroup.center (ggU .F4 n (2 * m + 1)).K := by
    rw [MonoidHom.ker_id]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 (2 * m + 1))).symm
  exact ggFieldOuterInvAt_of_modelData (t := .F4) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (fieldOuterInvModel_F4_odd m (GaloisField 2 (2 * m + 1)) hK) (MonoidHom.id _)
    Function.surjective_id hπker hctx s1 hb hb1 hL₁ hrM hr2 hrb hrnot

end CFSG.StandardType
