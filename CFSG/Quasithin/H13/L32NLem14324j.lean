module

public import CFSG.Quasithin.H13.L32NLem14324f
public import CFSG.Quasithin.H13.L32NLem14324i

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

theorem cases_of_inputs'
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13)
    (h14312 : Lemma14312One) (hFixS : G11.SzG11S.TheoremG112FixS)
    (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) (V₂ : Subgroup G) (g : G)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (D : HatModelU (fsuU T V)) (hd : 6 ≤ Module.finrank (ZMod 2) D.V) :
    G112Concl6 (D.img (l32nH T V)) ∨ G112Concl5 D.B (D.img (l32nH T V)) ∨
      G11.G112Concl8S8 D.B (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g)) ∨
      G11.SzG11S.G112Concl13S (D.img (l32nH T V)) := by
  rcases cases_of_inputs h1332 h1334 h1222 h12213 h12813 h14312 hFixS G T L V h hlt V₂ g hV₂
    hgP hgN D hd with h6 | h5 | h7 | h8 | h13
  · exact Or.inl h6
  · exact Or.inr (Or.inl h5)
  · exfalso
    obtain ⟨a, H, -, hX, -⟩ :=
      data_of h1332 h1334 h1222 h12213 h12813 h14312 hFixS h hlt hV₂ hgP hgN D
    have h8 := card_le_eight_of_concl7S H.X_le H.toG101Hyp.X_isElemAbelian h7
    rw [h7.1.1] at hX
    have : (16 : ℕ) ≤ 8 := (show (16 : ℕ) = 2 ^ (8 / 2) by norm_num) ▸ hX.trans h8
    omega
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h13))

end L14324

end CFSG.Quasithin.H13
