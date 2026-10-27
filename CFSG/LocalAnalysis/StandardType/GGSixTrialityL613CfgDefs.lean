module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613CfgFrame

public section

namespace CFSG.StandardType

open Multiplicative CFSG.StandardType.Triality CFSG.StandardType.D4Rank

@[expose] def GGOmegaFourFactorInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K,
      (∀ s s' : Fin 4 → ZMod 3,
        (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ NoOffOm.SuppLE s s') →
      (∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (OrthD4.supp s).card = 8) →
      ∀ i j k l : Fin 4, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      ∀ J : Subgroup (Om8 K),
        CFSG.Assembly.IsComponentOf J (Subgroup.centralizer
          {ι₁ (ofAdd (Pi.single i 1)), ι₁ (ofAdd (Pi.single j 1))}) →
        (∀ g ∈ J, ∀ w, act g (act (ι₁ (ofAdd (Pi.single i 1 + Pi.single j 1))) w - w) =
          act (ι₁ (ofAdd (Pi.single i 1 + Pi.single j 1))) w - w) →
        J ≤ Subgroup.centralizer {ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1))} ∨
          J ≤ Subgroup.centralizer {ι₁ (ofAdd (Pi.single k 1 - Pi.single l 1))}

end CFSG.StandardType
