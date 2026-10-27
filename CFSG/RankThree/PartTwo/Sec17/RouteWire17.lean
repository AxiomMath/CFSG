module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item131Facts

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] noncomputable def NoPGL131S17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ Sec8.IsZ3PGLThreePi ↥(lBarA c L A)

theorem prodLBarS17_of_wired
    (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hN : NoPGL131S17) : ProdLBarS17 := by
  intro G _ _ A c L Y₀ hs
  have hD : Sec13Data G A c L := hs.toSec15R.toSec14Std.toSec13Data
  rcases cases131 h131 hspor hSLC hD with ⟨-, -, hprod, -⟩ | ⟨-, -, hφ, -⟩ | ⟨-, hPGL, -⟩ |
      ⟨hcL, -⟩
  · exact hprod
  · obtain ⟨-, ⟨hM12p, -⟩, ⟨hJ2p, -⟩⟩ := hspor
    rcases hφ with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      exact nonempty_lBarA_equiv_prod hD hM12p φ
    · obtain ⟨φ⟩ := hφ
      exact nonempty_lBarA_equiv_prod hD hJ2p φ
  · exact absurd hPGL (hN G A c L Y₀ hs)
  · exact absurd hcL (hs.toSec15R.hypS.2.2 c hD.zpowers_mem_omegaA L hD.mem_lA)

end CFSG.RankThree.PartTwo.Sec17
