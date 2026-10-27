module

public import CFSG.LocalAnalysis.StandardType.GGA6GlueDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType.RCKA6

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open CFSG.Blueprint.Chevalley (adjointGroup Tag)

private theorem rckLB_tag_b2der_of_row_a6 {lab : LargeEvenLabel}
    (h : ggSixRCKLabelRow lab = .A6) : lab.tag = .B2der := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [ggSixRCKLabelRow] at h
  all_goals try rfl
  all_goals (try split_ifs at h)
  all_goals simp_all

private theorem rckLB_centerQuot_a6_of_row {X : Type} [Group X] {J : Subgroup X}
    (hrow : GGSixRCKJRow .A6 J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨lab, _hlab, R, _instR, I, F, θ, _hs, _hna, hP, hM⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have htag : lab.tag = .B2der := rckLB_tag_b2der_of_row_a6 hP
  obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der htag hM
  exact ⟨θ.trans e⟩

theorem rckF4_f_eq_one_of_quot
    (hF : A6Red.GGA6QuotF4f)
    (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X) (p : ℕ)
    (G₀ D J : Subgroup X) (hG₀ : GGPresentsG0 G₀ (ggU .F4 n f).D .F4 n f ψ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU .F4 n f).D ψ d) (hD : IsElemAbelian p D)
    (hD2 : Nat.card D = p ^ 2) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hrow : GGSixRCKJRow .A6 J) : f = 1 := by
  obtain ⟨⟨_hadm, _hrk⟩, ⟨hrange, hker⟩, _hperf, hmodel⟩ := hG₀
  exact hF X n f ψ p G₀ D J hrange hker hmodel hp hp2 hDN hdiag hD hD2 hJ
    (rckLB_centerQuot_a6_of_row hrow)

theorem rck_A6_exc_noRow_of_quot
    (hE : ∀ t : StatedLieTag,
      (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → A6Red.GGA6QuotNoJAt t)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ D J : Subgroup X) (hG₀ : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) (hD : IsElemAbelian p D)
    (hD2 : Nat.card D = p ^ 2) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    ¬ GGSixRCKJRow .A6 J := by
  intro hrow
  obtain ⟨⟨_hadm, _hrk⟩, ⟨hrange, hker⟩, _hperf, hmodel⟩ := hG₀
  exact hE t ht X n f ψ p G₀ D J hrange hker hmodel hp hp2 hDN hdiag hD hD2 hJ
    (rckLB_centerQuot_a6_of_row hrow)

end CFSG.StandardType.RCKA6
