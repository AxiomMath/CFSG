module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisCases
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGLabel
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixOpen
import CFSG.LocalAnalysis.StandardType.GGL45FixA2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangS1ExcXLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (((lab.tag = .F4 ∨ lab.tag = .twF4) ∧ p = 3) ∨ (lab.tag = .E8 ∧ (p = 3 ∨ p = 5))) ∧ p ∣ lab.n

theorem ggNbrLangAxisOuterOn_s1ExcX (hsub : GGNbrSubcomponentInput) (hT : GGStdSubNotTorsionInput) :
    GGNbrLangAxisOuterOn GGNbrLangS1ExcXLabel := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hfixOn : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (GGL45FieldFixKGRaw p lab) :=
    (ggL45FieldFixKnownForms_of_open ggL45FieldFixKnownFormsOpen_holds) p hp hp2
  have hconjAll : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGNbrLangS1ExcXLabel p lab → LargeEvenLabelAll lab (GGRawFieldConj p) := by
    intro lab hlab hS
    have htag : GGRecipeChevConjLabel lab ∨ lab.tag = .twF4 := by
      rcases hS.1 with ⟨ht, -⟩ | ⟨ht, -⟩
      · rcases ht with h | h
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ht))))
    rcases htag with h | h
    · exact ggRawFieldConjOn_chev p hp hp2 lab hlab h
    · exact ggRawFieldConjOn_twF4 p hp hp2 lab hlab h
  have hMfix := largeEvenMarking_and_labelAll_dep
    (P' := fun lab => GGL45FieldFixKGRaw p lab) hfixOn hP
  have hMsimp := largeEvenMarking_and_labelAll_simple_imp
    (S := fun lab => GGNbrLangS1ExcXLabel p lab)
    (P' := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      GGRawFieldConj p R I F)
    (fun lab hlab hS => ggL45_labelAll_mono (hconjAll lab hlab hS)
      (fun R _ I F hc hs hna => ⟨hs, hna, hc⟩)) hMfix
  refine largeEvenMarking_mono ?_ hMsimp
  rintro lab R _ I F θ ⟨⟨hPθ, hfix⟩, hfacts⟩
  refine ⟨hPθ, ?_⟩
  rintro hS hxout hall b₀ hb₀ hb₀I
  obtain ⟨hs, hna, hconj⟩ := hfacts hS
  have htor : GGL45TorsionTag lab := by
    rcases hS.1 with ⟨ht, -⟩ | ⟨ht, -⟩
    · rcases ht with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl ht
  have hI : GGThmIHyp p B x L := hcfg.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hSstar : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hSstar.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hxpow : x ^ p = 1 := hBstar.2.1.2 x hxBs
  have hKperf : commutator K = ⊤ := hP.1
  have hJK : J ≤ K := hsub G p B x L D J hI hDJ y K hK
  have hJc0 : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSstar hDJ hK hJK
  have hJc : IsComponentOf (J.subgroupOf K)
      (ggAutFixedSubgroup (K.normalizerMonoidHom ⟨x, hN hxBs⟩)) :=
    ggL45_isComponentOf_fixed_rhoK (hN hxBs) hJc0
  have hψp : (K.normalizerMonoidHom ⟨x, hN hxBs⟩ : MulAut ↥K) ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hN hxBs⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hxpow)
    rw [h1, map_one]
  obtain ⟨u, huI, f, hfF, hux⟩ := hall x hxBs
  have hufI : u * f ∉ I := by rw [← hux]; exact hxout hxBs
  have hσp : ggLAut K θ ⟨x, hN hxBs⟩ ^ p = 1 :=
    ggLAut_pow_eq_one_of_pow K θ (hN hxBs) hxpow
  have hufp : (u * f) ^ p = 1 := by rw [← hux]; exact hσp
  obtain ⟨f', hf'F, u', hu'I, hford, hufeq⟩ := hconj hs hna u huI f hfF hufI hufp
  have hψ : ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ LargeEvenInduces θ
      (fun k k' => k' = K.normalizerMonoidHom ⟨x, hN hxBs⟩ k) (u * f * u⁻¹) := by
    refine ⟨f', hf'F, u', hu'I, hford, ?_⟩
    intro k k' hkk
    rw [hkk, ← hufeq, ← hux, ggLAut_apply]
  have hJmark := (hfix.2 (↥K) θ hKperf (K.normalizerMonoidHom ⟨x, hN hxBs⟩) hψp hψ
    (J.subgroupOf K) hJc).1 htor
  have hJ := largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hJmark
  exact False.elim (hT G p B x L D J hI hDJ hJ)

end CFSG.StandardType
