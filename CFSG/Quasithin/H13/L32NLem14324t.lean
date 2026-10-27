module

public import CFSG.Quasithin.H13.L32NLem14324l
public import CFSG.Quasithin.H13.L32NLem14324s

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

theorem cases_six_or_thirteen
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12813 : Lemma12_8_13) (h14312 : Lemma14312One) (hFixS : G11.SzG11S.TheoremG112FixS)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h1434 : Lemma1434One)
    (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) (V₂ : Subgroup G) (g : G)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (D : HatModelU (fsuU T V)) (hd : 6 ≤ Module.finrank (ZMod 2) D.V) :
    G112Concl6 (D.img (l32nH T V)) ∨ G11.SzG11S.G112Concl13S (D.img (l32nH T V)) := by
  rcases cases_of_inputs'' h1332 h1334 h1222 h12213 h12813 h14312 hFixS G T L V h hlt V₂ g hV₂
    hgP hgN D hd with h6 | h5 | h13
  · exact Or.inl h6
  · exact (false_of_concl5 h1332 h1334 h1222 h12213 h12813 h14312 hFixS h36 h37 h38 h39 h1434 h
      hlt hV₂ hgP hgN D h5).elim
  · exact Or.inr h13

end L14324

end CFSG.Quasithin.H13
