module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_L27PermutesS3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsL2Odd Y 7 →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∀ X : Subgroup Y, Nat.card X = 3 → Permutes X S →
        Nat.card ↥(X ⊔ S) = 24 ∧
          Nat.card ↥(CFSG.Open.pCoreOf 2 (X ⊔ S)) = 4 ∧
          Nonempty (Bar2 (X ⊔ S) ≃* Equiv.Perm (Fin 3)) ∧
          ∃ d ∈ S, d ∉ CFSG.Open.pCoreOf 2 (X ⊔ S) ∧
            ∀ x ∈ X, d * x * d⁻¹ * x ∈ CFSG.Open.pCoreOf 2 (X ⊔ S)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
