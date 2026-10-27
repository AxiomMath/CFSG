module

public import CFSG.Quasithin.Vol2.Ch11SecE42S2
public import CFSG.Quasithin.Vol2.Ch11SecE42Obl
public import CFSG.Quasithin.Vol2.Ch11SecE42Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_4_2_of
    (hF : Facts42) (hF43 : Facts43) (hP : SecB.PointFacts)
    (hN : SecA.NatFacts) (hPar : ParInFacts) (hSig : SL2pSignalizerFact)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (h312 : QuasithinUnique.Vol2Native.A312ForSQTKCat) (h3214 : TmpL6_3_2_14)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (hS1 : Obl11_4_2S1) (hS3 : Obl11_4_2S3) : Stmt11_4_2 := by
  intro G _ _ T L I n V₁ h hV₁ z hz hz1
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hV₁ hX).1.1
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF43 h1102 h hcV hV₁ hz.1 hz.2
  have hV₁1 : V₁ ≠ ⊥ := fun h0 => hz1 (Subgroup.mem_bot.mp (h0 ▸ hzV₁))
  obtain ⟨hK, hNK, hcase⟩ := kz_spec hF43 h1102 h1110 h1111 h hcV hV₁ hz hz1
  have hle := kOf_le_kz hP h1102 h1110 h1111 h hV₁ hzV₁ hz1 hz2
  show kz L V₁ z = KOf L V₁ V₁
  by_contra hne
  have hne' : KOf L V₁ V₁ ≠ kz L V₁ z := fun e => hne e.symm
  have hnC := not_le_centralizer_of_ne h1110 h1111 h hV₁ hV₁1 hK hle hne'
  have hTz := le_centralizer_of_mem hz.2
  have hloc : quasithinIsLocal T (kz L V₁ z) :=
    isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz)
      (pCoreOf_centralizer_ne_bot h hz hz1) hK
  have hTK : T ≤ Subgroup.normalizer (kz L V₁ z : Set G) := hTz.trans hNK
  have hLK : LOf L V₁ ≤ kz L V₁ z := le_conjClosure _ _
  have hKz : kz L V₁ z ≤ Subgroup.centralizer ({z} : Set G) := le_of_mem_cComp hK
  have hnA36 : ¬ A36Case4 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) := fun hA =>
    hnC (le_centralizer_of_a36 h3214 hP h1102 h1110 h hV₁ hloc hTK hLK hA)
  have hconf : (List11_1_1Two (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) n ∨
      (n = 2 ∧ List11_1_1Three (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)))) →
      ¬ IsSL2pE (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) → False := by
    intro hlist hnE
    have hc : Conf11_4_2 T L I n V₁ z :=
      ⟨h, hV₁, hz, hz1, lt_of_le_of_ne hle hne', hlist, hnA36, hnE⟩
    exact hS3 G T L I n V₁ z hc ⟨hloc, fun Kp hKp hle' => hS1 G T L I n V₁ z hc Kp hKp hle'⟩
  rcases hcase with heq | hlist2 | ⟨hn2, hlist3⟩
  · apply hne'
    refine le_antisymm hle ?_
    calc kz L V₁ z = LOf L V₁ := heq.symm
      _ ≤ KOf L V₁ V₁ := le_conjClosure _ _
  · exact hconf (Or.inl hlist2) fun hE =>
      not_isQuasisimple_of_sl2pE hE (hF.twoQS _ n h.one_lt hlist2)
  · by_cases hE : IsSL2pE (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z))
    · exact hnC (le_centralizer_of_sl2pE hF hSig hN hPar hP h37 h38 h39 h312 h3214 h1102 h1110
        h1141 h hcV hV₁ hn2 hloc hTK hLK hzV₁ hz1 hKz hE)
    · exact hconf (Or.inr ⟨hn2, hlist3⟩) hE

end CFSG.Quasithin.Vol2.Ch11.SecE
