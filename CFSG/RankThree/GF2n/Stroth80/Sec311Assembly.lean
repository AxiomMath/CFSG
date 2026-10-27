module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Torus
public import CFSG.RankThree.GF2n.Stroth80.Sec311RootOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec57B
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth311a_of_inputs (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hGr : GriessCoverStatement) (hConj : Stroth311ConjStatement)
    (hTorus : Stroth311TorusStatement) (hOrd : Stroth311RootOrderStatement) :
    Stroth311aStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  refine le_antisymm ?_ (N0t_le_CN hc t)
  by_cases hV : Vt M (LB M Q B) B Z t ≤ QB B
  · exact stroth311a_of_SL h34 hGr hConj hc hs hR hV
  obtain ⟨τ, hτR, hτL, hτ⟩ := hTorus G M Q Z B hc n hw hn hno hgen t ht htQ hR hV
  have hAb' := stroth311ElAb G M Q Z B hc n hw hn hno hgen t ht htQ hR
  have hConj' := hConj G M Q Z B hc n hw hn hno hgen t ht htQ hR
  rcases h310 G M Q Z B hc n hw hn hno hgen t ht htQ with hRL | ⟨K, fK, finK, hK, hfam⟩
  · exact absurd hRL hR
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
  rcases hfam with ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, b, c, hm, hirr, hnat⟩
  · exact absurd (stroth310SL_of_34 h34 G M Q Z B hc n t hs ⟨K, fK, finK, hK, m, hm, hnat⟩) hV
  · have hm2 : 2 ≤ m := by
      by_contra hlt
      have h1 : m = 1 := by omega
      subst h1
      exact hV (stroth310SL_of_34 h34 G M Q Z B hc n t hs
        ⟨K, fK, finK, hK, 2, le_refl 2, NaturalRep.sp_one_to_sl_two hnat⟩)
    obtain ⟨φ, hrange, hker, -⟩ := id hnat
    refine Ctx.CN_le_N0t h34 hc hs hConj' hAb' hτR hτL hτ φ hker 0 ?_ (Nat.zero_le _)
    intro E _ _ Y π hrange' hkerπ hcen hperf A hAY hAel hAnorm hbA
    rcases (hGr K hq4 E Y hcen hperf).2.1 m hm π (hrange'.trans hrange) hkerπ with hY | hlt
    · exact hY
    · have h2 := hlt A hAY hAel hAnorm
      simp [show m ≠ 1 by omega] at h2
  · obtain ⟨φ, hrange, hker, -⟩ := id hnat
    refine Ctx.CN_le_N0t h34 hc hs hConj' hAb' hτR hτL hτ φ hker
      (if Nat.card K = 4 ∧ m = 2 then 16 else 0) ?_ ?_
    · intro E _ _ Y π hrange' hkerπ hcen hperf A hAY hAel hAnorm hbA
      rcases (hGr K hq4 E Y hcen hperf).2.2.1 m hm π (hrange'.trans hrange) hkerπ with hY | hlt
      · exact hY
      · exact absurd (hlt A hAY hAel hAnorm) (not_lt.mpr hbA)
    · split_ifs with h
      · obtain ⟨h4, rfl⟩ := h
        have := hOrd G M Q Z B hc n hw hn hno hgen t ht htQ hR hV ⟨K, fK, finK, hK, hnat⟩
        refine le_trans ?_ this
        rw [← hK, h4]
        norm_num
      · exact Nat.zero_le _
  · obtain ⟨φ, hrange, hker, -⟩ := id hnat
    refine Ctx.CN_le_N0t h34 hc hs hConj' hAb' hτR hτL hτ φ hker 0 ?_ (Nat.zero_le _)
    intro E _ _ Y π hrange' hkerπ hcen hperf A hAY hAel hAnorm hbA
    exact (hGr K hq4 E Y hcen hperf).2.2.2 m b c hm hirr π (hrange'.trans hrange) hkerπ

theorem strothNt_of_311a (h34 : Stroth34Statement) (ha : Stroth311aStatement) :
    StrothNtStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  refine le_antisymm (hc.Nt_le_CN h34 hs) (hc.CN_le_Nt ht ?_)
  by_cases hR : Rt M (LB M Q B) t = LB M Q B
  · have hL := Ctx.isPGroup_LB h34 hc hw hn hno hgen
    have hle : hc.CN t ≤ LB M Q B := fun x hx => hR ▸ (Ctx.mem_CN.mp hx).1
    exact hL.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  · exact hc.isPGroup_CN_of_311 h34 hs (ha G M Q Z B hc n hw hn hno hgen t ht htQ hR)

theorem stroth311a_of_theoremX (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hX : Classify.TheoremXStatement) (hGr : GriessCoverStatement)
    (hConj : Stroth311ConjStatement) : Stroth311aStatement :=
  stroth311a_of_inputs h34 h310 hGr hConj (stroth311Torus_of_theoremX h34 hX)
    (stroth311RootOrder_of_34 h34)

end CFSG.RankThree.GF2n.Stroth80
