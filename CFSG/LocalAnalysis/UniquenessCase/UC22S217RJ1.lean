module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Chev
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_17RJ1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal → IsJ1 (Bar2 L) →
    (conjSetOf D.M L).ncard = 2 ∧ c.n = 3 ∧ conjClosure D.M L = Opp 7 D.M ∧
      ∀ A : Subgroup G, A ≤ L → Nat.card A = 7 → A ∈ uniqueSet D.M

theorem s21_17RT2_of_s21_17RJ1 {D : Data G} {Ch : Choice2011 G} (he : evenRank G = 3)
    (hK3 : StronglyEmbeddedThree) (h82 : F08.R82 D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (h : S21_17RJ1 D Ch) : S21_17RT2 D Ch := fun hH c L hL hnN =>
  ⟨fun _ hn hL2 => uc22s217l2t_ncard_le_two D Ch he hK3 h82 hH c (hn3 hH c) hL hn hL2,
    h hH c L hL hnN⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
