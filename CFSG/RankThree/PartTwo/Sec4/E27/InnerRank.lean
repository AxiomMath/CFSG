module

public import CFSG.RankThree.PartTwo.Sec4.E27.G2Inputs
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem hinner_of_rankLE2 {X : Type} [Group X] (h : RankLE2 3 X) :
    ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 27 → HyperGen 3 (⊤ : Subgroup X) E := by
  intro E hE hc
  exfalso
  have h1 := h E hE
  rw [hc] at h1
  norm_num at h1


theorem seitz27_g2_of_plane {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hP : FixPlaneGen (adjointGroup .G2 K) 3) :
    Seitz27 (adjointGroup .G2 K) := by
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  exact seitz27_g2_of_inputs hf hK hP
    (hinner_of_rankLE2 (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 K h3))

end CFSG.RankThree.PartTwo.Sec4.E27
