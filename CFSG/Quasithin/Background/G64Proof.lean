module

public import CFSG.Quasithin.Background.G64Case1
public import CFSG.Quasithin.Background.G64Case3
public import CFSG.Quasithin.Background.G64ProofCase45
public import CFSG.Quasithin.Background.G64G2

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemmaG64_of_b5 (h56 : AsB56) : LemmaG64 := by
  intro V _ _ hV2 G a h htr
  have hB53 := b53Hyp_classK h htr
  have hK1 : conjClosure (Subgroup.zpowers a) G ≠ ⊥ := by
    intro hb
    have ha : a ∈ conjClosure (Subgroup.zpowers a) G := mem_classK
    rw [hb, Subgroup.mem_bot] at ha
    exact h.ne_one ha
  rcases h56 V hV2 _ hK1 hB53 with h1 | h2 | h3 | h4 | h5
  · exact conclusion_of_case1 hV2 h htr g2NoTransvection h1
  · exact conclusion_of_case2 hV2 h h2
  · exact conclusion_of_case3 hV2 h htr h3
  · exact absurd (false_of_case4 h htr h4) not_false
  · exact absurd (false_of_case5 h h5) not_false

end CFSG.Quasithin.G64
