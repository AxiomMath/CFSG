module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZR
public import CFSG.Quasithin.Vol2.Ch10SecB3Part2
public import CFSG.Quasithin.Vol2.Ch10SecQ3CE22D
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBk
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C11AmS

theorem obl10_2_3Case1_ofC
    (hB0K : Obl10_2_3B0K) (hKF9 : FactTwoL2BlocksSL3) (hBlocks : Obl10_2_3Blocks)
    (h118 : TheoremC118) (h126 : TheoremC126) (hBen : FactBenderOver)
    (hF1 : FactCommNatSL) (hF2 : FactCommAlt5) (hF3 : FactCommOrth) (hF4 : FactCommSz)
    (hF5 : FactCommL3Pair) (hF6 : FactCommGL4) (hDHB : Ch11.SecB.DerivedHallBorel)
    (h4413 : TmpL6_4_4_13) (h443 : Stmt4_4_3') (h3228 : TmpL6_3_2_2_eight)
    (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) : Obl10_2_3Case1 := by
  intro G _ _ T L I hyp H hH hn1 hZH n h1
  have hfaith : HallFaithful T L I H := stmt10_2_3_two hF1 hF2 hF3 hF4 hF5 hF6 hDHB h4413 h443
    h3228 h322 h154 h37 h38 h331 h1011 h1013 h1022 G T L I hyp H hH hn1
  obtain ⟨K, k, b, hel, I', K₀, c⟩ := exists_ctxC hBen h37 h38 h322 h331 h1013 hDHB hB0K hE22
    he23 hAS h1021 h1022 h3228 hyp h1 hH hn1 hZH hfaith
  obtain ⟨t, ht, htn⟩ := c.exists_t
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ :=
    eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (c.eq_one_of_mem_centralizer_L0 hz.1 hz.2)
  have hZH' : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (H : Set G) = ⊥ :=
    eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (c.eq_one_of_mem_centralizer_H hz.1 hz.2)
  have hbaumL : baum T ≤ Subgroup.normalizer (L : Set G) :=
    (c.baum_le_T1 h1012).trans inf_le_right
  obtain ⟨L₁, hL₁, hbL₁, hSL₁⟩ : ∃ L₁ : Subgroup G, (L₁ = L ∨ L₁ = CFSG.conjugate L t) ∧
      b ∈ L₁ ∧ baum T ≤ Subgroup.normalizer (L₁ : Set G) := by
    rcases c.s7.2 t ht htn with ⟨hb, -⟩ | ⟨hb, -⟩
    · exact ⟨L, Or.inl rfl, hb, hbaumL⟩
    · exact ⟨CFSG.conjugate L t, Or.inr rfl, hb, c.baum_le_normalizer_conjugate h1012 ht⟩
  have hLi : IsLi T L L₁ := hL₁.imp id fun h => ⟨t, ht, htn, h⟩
  obtain ⟨hS₁L₁, hS₁K, hL₁blk, hKblk⟩ := hBlocks G T L I hyp n h1 H hH hn1 hZH K c.hKc c.hHK
    c.hKF_n hZL hZH' c.fsuCVM_eq_bot c.isSylowTwoOf_baum_L0 c.isSylowTwoOf_baum_H
    (c.B0_le_normalizer_K hB0K) (c.isChi0Block h118 h126) L₁ b hLi hSL₁ c.baum_le_normalizer_K
    hbL₁ c.hbK c.hbB0 c.hbS c.orderOf_b c.hbD
  exact Ctx9.false (c := c) ⟨ht, htn, hL₁, hbL₁, hS₁L₁, hS₁K, hL₁blk, hKblk, h1012, h1021, h39,
    hKF9⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
