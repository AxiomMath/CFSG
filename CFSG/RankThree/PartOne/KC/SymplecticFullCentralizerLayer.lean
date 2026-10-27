module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizer
public import CFSG.RankThree.PartOne.KC.CommonLayerFromComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank

theorem symplectic_inner_plane_common_centralizer {ℓ f r p : ℕ}
    (hadm : StatedLieAdmissible .PSp r ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) :
    CommonLayerCentralizerTrivial (StatedProj (StatedSp r K)) p := by
  obtain ⟨hℓ, hf, hr, hne⟩ := hadm
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => hne (by rw [h.1, h.2])
  exact commonLayerCentralizerTrivial_of_components_inner_aut fun A hAH hA hAcard =>
    (symplectic_inner_plane_local_components_full_automorphism_centralizer hℓ hf hK hp hp3 hpℓ
      hr hrq A hAH hA hAcard).1

end CFSG.RankThree.PartOne
