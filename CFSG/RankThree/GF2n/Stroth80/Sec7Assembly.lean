module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth71_of_steps (h1 : Step71VanishStatement) (h2 : Step71TypeStatement)
    (h3 : Step71CloseStatement) : Stroth71Statement := by
  intro G _ _ M Q Z B hc n t hs
  by_contra hne
  have hno : ¬ Conc71abcd hc n t := fun h => hne (Or.inl h)
  have hnoe : ¬ Conc71e hc t := fun h => hne (Or.inr h)
  have hvan := h1 G M Q Z B hc n t hs hno
  by_cases hex : ∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
      ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t
  · exact hnoe ⟨h2 G M Q Z B hc n t hs hno hex, hex, hvan⟩
  · exact h3 G M Q Z B hc n t hs hno fun x hx hxt w hw =>
      by_contra fun hcon => hex ⟨x, hx, hxt, w, hw, hcon⟩

theorem step71close_of_parts (hTI : Close71TIStatement) (hSyl : Close71SylowStatement)
    (hE : Close71EStatement) (hFin : Close71FinalStatement) : Step71CloseStatement := by
  intro G _ _ M Q Z B hc n t hs hno hvan
  have hcl : Close71Hyp hc n t := ⟨hs, hno, hvan⟩
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre hs.toSec5.mem
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  exact hFin G M Q Z B hc n t hcl Z0 hZ0 (hTI G M Q Z B hc n t hcl Z0 hZ0)
    (hSyl G M Q Z B hc n t hcl Z0 hZ0) (hE G M Q Z B hc n t hcl Z0 hZ0)

theorem stroth73a_of_cases (h1 : Stroth73aNotOm4Statement) (h2 : Stroth73aOm4Statement) :
    Stroth73aStatement := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0 m hm hmV
  by_cases hom : OmegaMinusNat hc t 2
  · exact h2 G M Q Z B hc n t hs hno hom Z0 hZ0 m hm hmV
  · exact h1 G M Q Z B hc n t hs hno hom Z0 hZ0 m hm hmV

theorem stroth73c_of_cases (h1 : Stroth73cNotOm4Statement) (h2 : Stroth73cOm4Statement) :
    Stroth73cStatement := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0
  by_cases hom : OmegaMinusNat hc t 2
  · exact ⟨fun _ => (h2 G M Q Z B hc n t hs hno hom Z0 hZ0).2, fun _ =>
      h2 G M Q Z B hc n t hs hno hom Z0 hZ0⟩
  · exact ⟨h1 G M Q Z B hc n t hs hno hom Z0 hZ0, fun h => (hom h).elim⟩

end CFSG.RankThree.GF2n.Stroth80
