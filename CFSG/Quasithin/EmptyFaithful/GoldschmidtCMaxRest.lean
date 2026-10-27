module

public import CFSG.Quasithin.EmptyFaithful.S151S9H
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxHS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxJ2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxHe

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def CentMaxU33 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    IsPSU 3 3 1 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))

@[expose] def CentMax3D4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    Is3D4 2 1 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))

@[expose] def CentMaxM11 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    IsSporadic .M11 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))

@[expose] def CentMaxM12 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    IsSporadic .M12 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))

theorem input15120CentMaxRest_of_three
    (hU33 : CentMaxU33) (h3D4 : CentMax3D4) (hM11 : CentMaxM11) (hM12 : CentMaxM12) :
    Input15120CentMaxRest := by
  intro Q _ _ P hP2 hPi hT W hW hW0
  rcases hT with (h | h) | (h | h | h | h | h)
  · exact hU33 Q P hP2 hPi h W hW hW0
  · exact h3D4 Q P hP2 hPi h W hW hW0
  · exact hM11 Q P hP2 hPi h W hW hW0
  · exact hM12 Q P hP2 hPi h W hW hW0
  · exact centMax_j2 Q P hP2 hPi h W hW hW0
  · exact centMax_hs Q P hP2 hPi h W hW hW0
  · exact centMax_he Q P hP2 hPi h W hW hW0

end CFSG.Quasithin
