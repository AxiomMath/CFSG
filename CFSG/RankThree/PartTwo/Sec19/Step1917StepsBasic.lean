module

public import CFSG.RankThree.PartTwo.Sec19.Statements
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate3086
import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2
import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2Tools
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1917Steps

variable {G : Type} [Group G] [Finite G]

theorem le_M
    (h1913 : Step1913) {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M) : A ≤ M := by
  have hA := Step1916Proof2.isE27_A hctx
  have hD9 : Nat.card (A ⊓ E : Subgroup G) = 9 := step1916D_of h1913 G A c L E M hctx
  have hND : Subgroup.normalizer ((A ⊓ E : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_gamma inf_le_right (two_le_pRank_of_elemAbelian
      (isElemAbelian_of_le hA.1 inf_le_left) hD9.ge)).trans hctx.mem_scriptM.2
  intro a ha
  refine hND ((Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr ?_))
  intro x hx
  exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx.1⟩ ⟨a, ha⟩)

omit [Finite G] in
theorem le_H {X H : Subgroup G} (hX : IsMulCommutative X) {d : G} (hdX : d ∈ X)
    (hH : Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ H) : X ≤ H := fun _ hx =>
  hH ((centralizer_le_normalizer_zpowers d) (le_centralizer_of_mem hX hdX hx))

end Step1917Steps

end CFSG.RankThree.PartTwo.Sec19
