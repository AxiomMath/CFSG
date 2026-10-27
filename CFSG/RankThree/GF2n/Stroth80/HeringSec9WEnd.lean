module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9WCount
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9WPt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem Z_le_QB_of_isConjB (hc : Ctx M Q Z B) {F : Subgroup G} (hF : IsConjB M B F) :
    Z ≤ QB F := by
  obtain ⟨m, hm, rfl⟩ := hF
  have hFQ : conjSubgroup m B ≤ Q := (hc.conj_of_mem hm).le
  exact (IsZConjugate.le_QB_iff hc.hyp (isZConjugate_of_isConjB hc ⟨m, hm, rfl⟩)
    (IsZConjugate.self Z)).mpr (by rw [QB_Z_eq hc]; exact hFQ)

theorem goodAll_of_five_four (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hT : Sec97OneTypesNoSL) (hspread : StrothNoA2SpreadStatement) (h95 : Stroth95Statement)
    (hS4 : Sec4Statement) (hOne : Sec97OneStatement) (h57 : Sec57WStatement)
    (h96 : Sec96WStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    (hfour : FourConcl M Q B Y) (hfive : FiveConcl M Q Z B Y) : GoodAll M Q B Y := by
  intro m hm
  have hFB : IsConjB M B (conjSubgroup m B) := ⟨m, hm, rfl⟩
  obtain ⟨U₁, -, -, hUQ, ha, hb, -, hcard⟩ := hfive
  by_cases hcase : U₁ ⊓ QB (conjSubgroup m B) ≤ Z
  ·
    obtain ⟨g, hgB, hgZ, hgQ, hgQB⟩ := exists_swapFrame hc hFB
    obtain ⟨d, hdU, hdC, hdQF, hdLX⟩ :=
      exists_swap_point hc hsplit h4 hFB hUQ hcard hgZ hgQB hgQ hcase
    have hdZ : d ∉ Z := fun h => hdQF (Z_le_QB_of_isConjB hc hFB h)
    obtain ⟨P, hP, hdP, hgoodP⟩ := exists_good_point_of_mem_U₁ hc ha hb hdU hdZ
    have hxQ : g⁻¹ * d * g ∉ Q := fun h => hdQF ((swap_conj_mem_Q_iff hgQ d).mp h)
    have hdich := slNat_or_omegaPlus h310 hT hc hs hsplit h4 hdLX hxQ
    have hW := wpoint_of_dichotomy h95 hS4 hOne h57 h96 hc hs hdLX.1 hxQ hdich
    have hs5 := hs.toSec5
    have hRT : RootTrans M Q Z B :=
      rootTrans_of_all h34 hc hs5 (hspread G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen)
    obtain ⟨C', hC', hC'F, hC'P⟩ :=
      exists_swapped_point hc hRT hgB hgQ hgQB hP hdP hdLX.1 hxQ hW
    have hgoodC' : GoodPt M Q B Y C' := hfour P C' hP hC' hgoodP hC'P
    have hFC' : conjSubgroup m B ≤ QB C' :=
      (IsZConjugate.le_QB_iff hc.hyp (isZConjugate_of_isConjB hc hFB)
        (isZConjugate_of_isConjB hc hC')).mp hC'F
    exact hfour C' _ hC' hFB hgoodC' hFC'
  ·
    obtain ⟨u, hu, huZ⟩ := SetLike.not_le_iff_exists.mp hcase
    exact good_of_mem_U₁_inf_QB hc hfour ha hb hFB hu.1 huZ hu.2

end HS9

theorem sec97SixW_of (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hT : Sec97OneTypesNoSL) (hspread : StrothNoA2SpreadStatement) : Sec97SixWStatement := by
  intro h95 hS4 hOne h57 h96 G _ _ M Q Z B hc n t hs X Y hsplit h4 _ hfour hfive S F _ hF _ _
  obtain ⟨m, hm, rfl⟩ := hF
  exact HS9.goodAll_of_five_four h34 h310 hT hspread h95 hS4 hOne h57 h96 hc hs hsplit h4 hfour
    hfive m hm

end CFSG.RankThree.GF2n.Stroth80
