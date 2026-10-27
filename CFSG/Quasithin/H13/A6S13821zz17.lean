module

public import CFSG.Quasithin.H13.A6S13821zz16
public import CFSG.Quasithin.H13.A6S13821zz7
public import CFSG.Quasithin.H13.A6S13821zz3
public import CFSG.Quasithin.H13.A6S13821zz4

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem case13820a_of
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    (hF10 : Vol2.Ch10.SecA.Facts10_1) (h1337 : Stmt13_3_7) (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hB51 : AsB51) : Case13820a := by
  intro G _ _ T L V S H K n hC ha
  rcases hC.2.2.2.2.2.2 with h2 | h3 | hu | hsp | hg2
  · exact S.false_of_l2_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 h42 hF10 h1337
      h13314 h13315 h1356two hC ha h2
  · rcases Nat.even_or_odd n with he | ho
    · exact S.false_of_rank_two_13820a hC ha (Or.inr (Or.inr (Or.inl ⟨he, h3⟩)))
    · exact S.false_of_l3_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 h42 hB51 hC
        ha ho h3
  · exact S.false_of_u3_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 h42 hC ha hu
  · exact S.false_of_rank_two_13820a hC ha (Or.inl hsp)
  · exact S.false_of_rank_two_13820a hC ha (Or.inr (Or.inl hg2))

end CFSG.Quasithin.H13.A6
