module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13604
public import Certificates.Certificate13657
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclLin
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclSymp
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclUnit
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclOrth
import CFSG.LocalAnalysis.StandardType.GGD5LabelExclExc
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem lup10d_label_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (hxL : x ∉ L) {y : G} {H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (e : Fin 5 ≃ M.ι) (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j)
    (he0 : M.a = e 0) (hbas : M.toLin.Basis) :
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) p Bs L := by
  subst hp
  have hq : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) ∨
      ((lab.tag = .A ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .triD4 ∨ lab.tag = .G2 ∨
        lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨
        lab.tag = .twF4der) ∧ lab.n = 1) ∨
      ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .F4) ∧ lab.n = 1) ∨
      ((lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ lab.n = 1) ∨
      (((lab.tag = .D ∧ lab.rank ≠ 4) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)) ∧ lab.n = 1) ∨
      ((lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6) ∧ lab.n = 1))
      3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hlab _ hn => ?_) hS.2.1
    have h1 : 1 ≤ lab.n := hlab.1
    have hn1 : lab.n = 1 := by
      have h2 : lab.n < 2 := hn
      omega
    obtain ⟨t, r, n⟩ := lab
    dsimp only at hn1 ⊢
    cases t
    case D =>
      by_cases hr : r = 4
      · exact Or.inl ⟨rfl, hr, hn1⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, hr⟩, hn1⟩))))
    case twD =>
      have hr2 : 2 ≤ r := hlab.2
      rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with h | h | h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inl ⟨rfl, h⟩), hn1⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, h⟩, hn1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, h⟩, hn1⟩))))
    all_goals simp [hn1]
  rcases GGInnerDiagOnLabel.elim_or hq with h | h
  · exact h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_lin hS hxL M e hecart he0 hbas h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_symp hS hxL M e hecart he0 hbas h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_unit hS hxL M e hecart he0 hbas h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (lup10e_not_orth hS hxL M e hecart he0 hbas h).elim
  · exact (lup10e_not_exc hS hxL M e hecart he0 hbas h).elim

end CFSG.StandardType

end
