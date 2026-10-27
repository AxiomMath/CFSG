module

public import CFSG.Quasithin.Background.RonanE68Conv
public import CFSG.Quasithin.Background.RonanE68Case2
public import CFSG.Quasithin.Background.RonanE68Cover
public import CFSG.Quasithin.Background.ONanE68Main

public section

namespace CFSG.Quasithin

namespace RonanE68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68 CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin.E6 CFSG.Quasithin.E6.E68Proof
  CFSG.QuasithinUnique.Vol2Native.L239

@[expose] def Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (h : E6.HypE61 T M V),
    U ∈ E6.gammaE64 V M → IsComponentIn L (Subgroup.centralizer (U : Set G)) →
      ¬ L ≤ M ∧
        (Case1P h.isElemAbelian T M U L ∨ Case2P T M V U L ∨ Case3P T M V U L ∨
          E6.E68Case4 M V U L ∨ Case5P M V U L)

section Main

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem outP_of_out (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ : Subgroup.center ↥L = ⊥)
    (hout : E68Out h.isElemAbelian T M U L) : OutP h.isElemAbelian T M U L := by
  rcases hout with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (case1P_of_case1 hZ h1)
  · exact Or.inr (Or.inl (case2P_of_case2 h hU hL h2))
  · exact Or.inr (Or.inr (Or.inl (case3P_of_case3 hU hL h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (case5P_of_case5 hU hL h5))))

theorem outP_of_caseA (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hInn : Ch1.EvenLieAutInner) (hcat : SmallCatL2p) (hA6 : E68A6Case)
    (hLie : E68LieRankTwo) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hA : Lemma115CaseA L z) : OutP h.isElemAbelian T M U L :=
  outP_of_out h hU hL
    (center_eq_bot_of_simple_quasisimple (BenderBranch.isQuasisimple_of_isComponentIn hL) hA.1)
    (out_of_caseA hC129 hpairs hnot h121 hInn hcat hA6 hLie h.isElemAbelian h hU hL hA)

theorem outP_of_caseB
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hF : E68LieFacts) (hInn : Ch1.EvenLieAutInner) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hB : Lemma115CaseB L z) : OutP h.isElemAbelian T M U L := by
  obtain ⟨hne, hZP, hmodel, -⟩ := hB
  rcases hmodel with hL34 | hG24
  · exact Or.inl (out_of_coverP hF hInn h121 h.isElemAbelian h hU hL ⟨hZP, hne, hL34⟩)
  · exact (false_of_pairs hC129 hpairs hnot h121 h hU hL (Or.inr (Or.inl hG24))).elim

theorem outP_of_caseC (hAlt : E68AltRank) (hA6 : E68A6Case) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hC : Lemma115CaseC L z) : OutP h.isElemAbelian T M U L := by
  obtain ⟨φ, -, hZ, -, -⟩ := id hC
  rcases hZ with h1 | h3
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact Or.inr (Or.inl (case2P_of_case2 h hU hL
      (hA6 G T M V U L h.isElemAbelian h hU hL ⟨(mulEquivQuotientCenter hbot).trans φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (case4_of_alt hAlt h hU hL (Or.inl hC)
      (Or.inr (Or.inl ⟨h3, ⟨φ⟩⟩))))))

theorem outP_of_caseD (hAlt : E68AltRank) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hD : Lemma115CaseD L z) : OutP h.isElemAbelian T M U L := by
  obtain ⟨φ, -, hZ, -, -⟩ := id hD
  refine Or.inr (Or.inr (Or.inr (Or.inl (case4_of_alt hAlt h hU hL (Or.inr hD) ?_))))
  rcases hZ with h1 | h3
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact Or.inl ⟨(mulEquivQuotientCenter hbot).trans φ⟩
  · exact Or.inr (Or.inr ⟨h3, ⟨φ⟩⟩)

theorem outP_of_caseE (hcat33 : SmallCatL33) (hcat : SmallCatL2p) (hLie : E68LieRankTwo)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hE : Lemma115CaseE L z) : OutP h.isElemAbelian T M U L := by
  obtain ⟨hmodel, -⟩ := hE
  rcases hmodel with hL3 | ⟨p, hFM, hL2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (case5P_of_case5 hU hL (case5_l33 hcat33 h hU hL hL3)))))
  · have hp : p.Prime := hFM.1
    have hadm := hL2.1
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    have hp2 : p ≠ 2 := fun hp2 => h22 (by subst hp2; rfl)
    have hp3 : p ≠ 3 := fun hp3 => h23 (by subst hp3; rfl)
    by_cases hp5 : p = 5
    · subst hp5
      refine outP_of_out h hU hL ?_ (hLie G T M V U L h.isElemAbelian h hU hL
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL2)))))))
      exact center_eq_bot_of_simple_quasisimple (BenderBranch.isQuasisimple_of_isComponentIn hL)
        (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 5 1 hL2).2
    · have h7 : 7 ≤ p := by
        have h2 := hp.two_le
        by_contra hlt
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by decide)
        · exact hp5 rfl
        · exact absurd hp (by decide)
      exact Or.inr (Or.inr (Or.inr (Or.inr (case5P_of_case5 hU hL
        (case5_l2p hcat h hU hL hFM h7 hL2)))))

theorem outP_of_caseF (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hSpor : Ch1.SporadicAutInner) (hcyc : SporadicSylowCenterCyclic) (hcov : L239Covers)
    (hM22 : E68M22Excl) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hF : Lemma115CaseF L z) : OutP h.isElemAbelian T M U L := by
  obtain ⟨⟨s, hs, ⟨e⟩⟩, -⟩ := hF
  have hbad : IsBadSporadicName s → OutP h.isElemAbelian T M U L := fun hb =>
    (false_of_pairs hC129 hpairs hnot h121 h hU hL
      (Or.inr (Or.inr (Or.inl ⟨s, hb, ⟨e⟩⟩)))).elim
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · subst hs
    exact Or.inr (Or.inr (Or.inr (Or.inr (case5P_of_case5 hU hL
      (case5_m11 hSpor hcyc hcov h hU hL e)))))
  · exact hbad (by simp [IsBadSporadicName, hs])
  · subst hs
    exact (hM22 G T M V U L h hU hL (Or.inl ⟨e⟩)).elim
  · subst hs
    exact (hM22 G T M V U L h hU hL (Or.inr ⟨e⟩)).elim
  all_goals exact hbad (by simp [IsBadSporadicName, hs])

end Main

theorem e68P_of_inputs
    (hlist : Lemma115_3_List)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hAlt : E68AltRank) (hInn : Ch1.EvenLieAutInner) (hSpor : Ch1.SporadicAutInner)
    (hcyc : SporadicSylowCenterCyclic) (hcov : L239Covers) (hcat33 : SmallCatL33)
    (hcat : SmallCatL2p) (hA6 : E68A6Case) (hM22 : E68M22Excl) (hLie : E68LieRankTwo)
    (hF : E68LieFacts) : Stmt := by
  intro G _ _ T M V U L h hU hL
  obtain ⟨hLM, -, -, z, -, -, -, hcases⟩ := setting hlist h hU hL
  refine ⟨hLM, ?_⟩
  rcases hcases with hA | hB | hC | hD | hE | hFF
  · exact outP_of_caseA hC129 hpairs hnot h121 hInn hcat hA6 hLie h hU hL hA
  · exact outP_of_caseB hC129 hpairs hnot h121 hF hInn h hU hL hB
  · exact outP_of_caseC hAlt hA6 h hU hL hC
  · exact outP_of_caseD hAlt h hU hL hD
  · exact outP_of_caseE hcat33 hcat hLie h hU hL hE
  · exact outP_of_caseF hC129 hpairs hnot h121 hSpor hcyc hcov hM22 h hU hL hFF

end RonanE68

end CFSG.Quasithin
