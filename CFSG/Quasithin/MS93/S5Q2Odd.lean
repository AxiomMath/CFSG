module

public import CFSG.Quasithin.MS93.S5Q2X52Cent

public section

namespace CFSG.Quasithin.MS93.S5Q2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace UC

variable (h : PUHyp M T L)

theorem jOff_ne_of_not_case56 (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L 1 F a) (h54 : S54)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {δ : Vtx (puAmalgam h.le)}
    (hcase : ∀ l, ¬ S5.Case56 h 2 a δ l) :
    S5.jOff h.le L 2 δ (baseB _) ≠ S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) := by
  intro heq
  rcases h54 G M T L h hmin hb 1 F _ _ a hd with ⟨-, ⟨l₁, hl₁, hT₁, hJl₁⟩, -⟩ |
      ⟨-, -, p, hp, hTq⟩
  · exact hcase l₁ ⟨heq, hl₁, hT₁, by simpa using hJl₁⟩
  · exact X52.vIm_qv_baseB_ne_qPoint h hd hC hp hTq

end UC

end CFSG.Quasithin.MS93.S5Q2
