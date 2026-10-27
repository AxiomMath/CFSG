module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartOne.K1320.L4Psl2
public import CFSG.RankThree.PartOne.K1327.StepA
public import CFSG.RankThree.PartOne.Q1327.Defs
public import CFSG.RankThree.PartOne.S13K.Pair134Embed

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.Q1327
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem c_mem_autMoved (H : Hyp G p A c L E f r R s s' zs) (hcE : c ∈ E) :
    (⟨c, hcE⟩ : E) ∈ autMoved E zs := by
  have h1 : c ∈ autMovedInG E zs := by
    rw [H.hmov]
    exact Subgroup.mem_zpowers c
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 h1
  have : x = ⟨c, hcE⟩ := Subtype.ext hxc
  rwa [this] at hx

end Main

end CFSG.RankThree.PartOne.Q1327T
