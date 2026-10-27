module

public import CFSG.Quasithin.MS93.S5BStmt
public import CFSG.Quasithin.MS93.SkAssembly

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

@[expose] def S511Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      (∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        ∃ l : Submodule F (MSP.V4 F),
          S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) →
      False

theorem s511_of (h510 : S510) (hcore : S511Core) : S511 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd
  obtain ⟨c, hc⟩ := h.critDist_even
  by_contra hne
  have hb4 : 4 < critDist (puAmalgam h.le) := by omega
  exact hcore G M T L h hmin hb4 k F _ _ a hd fun α' hc' hαβ =>
    h510 G M T L h hmin hb4 k F _ _ a hd α' hc' hαβ

end S5B

end CFSG.Quasithin.MS93
