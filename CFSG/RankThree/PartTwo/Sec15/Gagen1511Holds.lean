module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1511Main
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProof
import CFSG.RankThree.PartTwo.Sec15.Gagen1511Field

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14


theorem not_case148Five_of_sec15R (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Item1510R) (hBr : Sec16.Step169TwoBridge) (h134 : Item134)
    (h48 : Sec4.Item4_8) {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) :
    letI := ker148_normal hY.1.1.2
    ¬ Case148Five A (lB A) Y := by
  letI := ker148_normal hY.1.1.2
  rintro ⟨c', hc'A, L', n, m, hc', hL', hn, hm, hX, hsplit, -, hfield, hε, -, K, hKLY, hKn, hKp,
    hKΔ⟩
  exact Proof1511Field.false_of_field_point h158 hset h133 h159 h1510 hBr h134 h48 h hY hc'A hc'
    hL' hn hm hX hsplit hfield hε hKp hKΔ hKLY hKn

theorem step1511Field_of (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Item1510R) (hBr : Sec16.Step169TwoBridge) (h134 : Item134)
    (h48 : Sec4.Item4_8) : Step1511Field :=
  fun _ _ _ _ _ _ h _ hY => not_case148Five_of_sec15R h158 hset h133 h159 h1510 hBr h134 h48 h hY

theorem step1511Point_of_items (h148 : Item148R) (h131a : Item131a) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Item1510R) (hBr : Sec16.Step169TwoBridge) : Step1511Point :=
  step1511Point_of h148 h131a h134 h48 (step1511Field_of h158 hset h133 h159 h1510 hBr h134 h48)

theorem item1511R_of_items (h142 : Item142R) (h148 : Item148R) (h131a : Item131a)
    (h133 : Item133) (h134 : Item134) (h48 : Sec4.Item4_8) (hset : Item13SetupAt)
    (h158 : Item158Y0R) (h159 : Item159R) (h1510 : Item1510R) (hBr : Sec16.Step169TwoBridge) :
    Item1511R :=
  item1511R_of_steps h158 hset h133 h159 h1510 hBr
    (step1511Point_of_items h148 h131a h134 h48 h158 hset h133 h159 h1510 hBr) h142

end CFSG.RankThree.PartTwo.Sec15
