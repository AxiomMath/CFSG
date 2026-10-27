module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem two_lt_qInt
    (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h521 : Stmt5_1_21) (hD : D310L34Fact) (hB : B45L34Fact)
    (hnot : ¬ Concl5_1_14_four T L V B D n)
    (hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H))) :
    2 < qInt (tildeOf Z₁ H) (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H)) hU := by
  have key := s.two_lt_qhatInt h5114 hF h510 h521 hD hB hnot hU
  let := commGroupOfElemAbelian hU
  exact lt_of_lt_of_le key (qhatOf_le_qOf _)

end Setup521

theorem stmt5_1_14_qBound_of_inputs
    (h5114 : Stmt5_1_14_first) (h510 : Stmt5_1_10)
    (h520 : Stmt5_1_20) (h521 : Stmt5_1_21) (hF : L2TorusFact) (hD : D310L34Fact)
    (hB : B45L34Fact) : Stmt5_1_14_qBound := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1 hU
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨⟨hyp, not59, hmod, hl34⟩, hD₃, h3,
      (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).1, hz1⟩
  exact s.two_lt_qInt h5114 hF h510 h521 hD hB hnot hU

end CFSG.Quasithin.H13
