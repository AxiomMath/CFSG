module

public import CFSG.Quasithin.Background.ONanE68Cases
public import CFSG.Quasithin.Background.ONanE68Alt
public import CFSG.Quasithin.Background.ONanE68Elim
public import CFSG.Quasithin.Background.ONanE68L42

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68 CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

section Main

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem out_of_caseA (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hInn : Ch1.EvenLieAutInner) (hcat : SmallCatL2p) (hA6 : E68A6Case)
    (hLie : E68LieRankTwo) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hA : Lemma115CaseA L z) : E68Out hV T M U L := by
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  obtain ⟨-, hlie, -⟩ := hA
  have hF : IsParabolicPairType L (T ⊓ Subgroup.centralizer (V : Set G)) → E68Out hV T M U L :=
    fun ht => (false_of_pairs hC129 hpairs hnot h121 h hU hL ht).elim
  rcases hlie with ((⟨f, h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8⟩ | htits) | ⟨n, hn, hmodel⟩) |
      hA6' | hU33
  · exact hLie G T M V U L hV h hU hL (Or.inl ⟨f, h1⟩)
  · by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inr (Or.inr (Or.inr (case5_l2p hcat h hU hL isFermatOrMersennePrime_seven
        le_rfl (psl_two_seven_of_psl_three_two h2.2)))))
    · have hf2 : 2 ≤ f := by have := h2.1; omega
      exact hLie G T M V U L hV h hU hL (Or.inr (Or.inr (Or.inl ⟨f, hf2, h2.2⟩)))
  · exact hLie G T M V U L hV h hU hL (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h3⟩))))
  · exact hLie G T M V U L hV h hU hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h4⟩)))))
  · exact hF (Or.inl (Or.inl ⟨f, Or.inl h5⟩))
  · exact hF (Or.inl (Or.inl ⟨f, Or.inr (Or.inl h6)⟩))
  · exact hF (Or.inl (Or.inl ⟨f, Or.inr (Or.inr h7)⟩))
  · exact hLie G T M V U L hV h hU hL (Or.inr (Or.inl ⟨f, h8⟩))
  · exact hF (Or.inl (Or.inr (Or.inl htits)))
  · rcases hn with rfl | rfl
    · by_cases hout : ∃ s ∈ T ⊓ Subgroup.centralizer (V : Set G), InducesOuter s L
      · have hnorm : IsNormalListedType L := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmodel))))
        have hCN := le_normalizer_of_not_is121List h121 h hU hL fun hl =>
          hnot G L hq hnorm (Id2519.a38Types_of_is121List hl)
        exact Or.inr (Or.inr (Or.inl (case3_of_l42 hInn h hU hL ((e6_5_one h hU).1.trans hCN)
          hmodel hout)))
      · exact hF (Or.inr (Or.inr (Or.inr ⟨hmodel, hout⟩)))
    · exact hF (Or.inl (Or.inr (Or.inr (Or.inl hmodel))))
  · exact Or.inr (Or.inl (hA6 G T M V U L hV h hU hL hA6'))
  · exact hF (Or.inl (Or.inr (Or.inr (Or.inr hU33))))

theorem out_of_caseB (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hLie : E68LieRankTwo) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hB : Lemma115CaseB L z) : E68Out hV T M U L := by
  obtain ⟨hne, hZP, hmodel, -⟩ := hB
  rcases hmodel with hL34 | hG24
  · exact hLie G T M V U L hV h hU hL
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hZP, hne, hL34⟩))))))
  · exact (false_of_pairs hC129 hpairs hnot h121 h hU hL (Or.inr (Or.inl hG24))).elim

theorem out_of_caseC (hAlt : E68AltRank) (hA6 : E68A6Case) (hV : CFSG.Open.IsElemAbelian 2 V)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hC : Lemma115CaseC L z) : E68Out hV T M U L := by
  obtain ⟨φ, -, hZ, -, -⟩ := id hC
  rcases hZ with h1 | h3
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact Or.inr (Or.inl (hA6 G T M V U L hV h hU hL ⟨(mulEquivQuotientCenter hbot).trans φ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (case4_of_alt hAlt h hU hL (Or.inl hC)
      (Or.inr (Or.inl ⟨h3, ⟨φ⟩⟩))))))

theorem out_of_caseD (hAlt : E68AltRank) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hD : Lemma115CaseD L z) : E68Out hV T M U L := by
  obtain ⟨φ, -, hZ, -, -⟩ := id hD
  refine Or.inr (Or.inr (Or.inr (Or.inl (case4_of_alt hAlt h hU hL (Or.inr hD) ?_))))
  rcases hZ with h1 | h3
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact Or.inl ⟨(mulEquivQuotientCenter hbot).trans φ⟩
  · exact Or.inr (Or.inr ⟨h3, ⟨φ⟩⟩)

theorem out_of_caseE (hcat33 : SmallCatL33) (hcat : SmallCatL2p) (hLie : E68LieRankTwo)
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hE : Lemma115CaseE L z) : E68Out hV T M U L := by
  obtain ⟨hmodel, -⟩ := hE
  rcases hmodel with hL3 | ⟨p, hFM, hL2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (case5_l33 hcat33 h hU hL hL3))))
  · have hp : p.Prime := hFM.1
    have hadm := hL2.1
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    have hp2 : p ≠ 2 := fun hp2 => h22 (by subst hp2; rfl)
    have hp3 : p ≠ 3 := fun hp3 => h23 (by subst hp3; rfl)
    by_cases hp5 : p = 5
    · subst hp5
      exact hLie G T M V U L hV h hU hL
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL2))))))
    · have h7 : 7 ≤ p := by
        have h2 := hp.two_le
        by_contra hlt
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by decide)
        · exact hp5 rfl
        · exact absurd hp (by decide)
      exact Or.inr (Or.inr (Or.inr (Or.inr (case5_l2p hcat h hU hL hFM h7 hL2))))

theorem out_of_caseF (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hSpor : Ch1.SporadicAutInner) (hcyc : SporadicSylowCenterCyclic) (hcov : L239Covers)
    (hM22 : E68M22Excl) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hF : Lemma115CaseF L z) : E68Out hV T M U L := by
  obtain ⟨⟨s, hs, ⟨e⟩⟩, -⟩ := hF
  have hbad : IsBadSporadicName s → E68Out hV T M U L := fun hb =>
    (false_of_pairs hC129 hpairs hnot h121 h hU hL
      (Or.inr (Or.inr (Or.inl ⟨s, hb, ⟨e⟩⟩)))).elim
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · subst hs
    exact Or.inr (Or.inr (Or.inr (Or.inr (case5_m11 hSpor hcyc hcov h hU hL e))))
  · exact hbad (by simp [IsBadSporadicName, hs])
  · subst hs
    exact (hM22 G T M V U L h hU hL (Or.inl ⟨e⟩)).elim
  · subst hs
    exact (hM22 G T M V U L h hU hL (Or.inr ⟨e⟩)).elim
  all_goals exact hbad (by simp [IsBadSporadicName, hs])

theorem e68Stmt_of_inputs (hlist : Lemma115_3_List)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (hAlt : E68AltRank) (hInn : Ch1.EvenLieAutInner) (hSpor : Ch1.SporadicAutInner)
    (hcyc : SporadicSylowCenterCyclic) (hcov : L239Covers) (hcat33 : SmallCatL33)
    (hcat : SmallCatL2p) (hA6 : E68A6Case) (hM22 : E68M22Excl) (hLie : E68LieRankTwo) :
    E68Stmt := by
  intro G _ _ T M V U L hV h hU hL
  obtain ⟨hLM, -, -, z, -, -, -, hcases⟩ := setting hlist h hU hL
  refine ⟨hLM, ?_⟩
  rcases hcases with hA | hB | hC | hD | hE | hF
  · exact out_of_caseA hC129 hpairs hnot h121 hInn hcat hA6 hLie hV h hU hL hA
  · exact out_of_caseB hC129 hpairs hnot h121 hLie hV h hU hL hB
  · exact out_of_caseC hAlt hA6 hV h hU hL hC
  · exact out_of_caseD hAlt hV h hU hL hD
  · exact out_of_caseE hcat33 hcat hLie hV h hU hL hE
  · exact out_of_caseF hC129 hpairs hnot h121 hSpor hcyc hcov hM22 hV h hU hL hF

end Main

end E68Proof

end E6

end CFSG.Quasithin
