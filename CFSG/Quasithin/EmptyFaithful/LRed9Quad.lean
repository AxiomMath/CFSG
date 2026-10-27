module

public import CFSG.Quasithin.Vol2.Ch3y319
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.Vol2.Ch3xCons1519

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace LRed9

@[expose] def Lemma319StatementCE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc → IsMf T Mc M →
    IsCE1513 T M → ∀ H M₀ : Subgroup G, IsHStar T M H →
      ∀ h : Hyp315Base T M M₀ H (V154 T Mc M), Hyp315.CaseII M H (V154 T Mc M) →
      qInt M₀ (V154 T Mc M) h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V154 T Mc M ≤ pCoreOf 2 H →
      ¬ IsDualFFOn M₀ (V154 T Mc M) →
      Concl319 T M (V154 T Mc M) H (oTwoUpper (M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G)) ≤ Subgroup.centralizer (V154 T Mc M : Set G))

theorem lemma319StatementCE_of_inputs (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK)
    (hShape : Lemma319Shape) : Lemma319StatementCE := by
  intro G _ _ T Mc M hQ' hM _ H M₀ _ hbase hII hq hMu hVH hdual
  have h : Hyp319 T M M₀ H (V154 T Mc M) := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hmain := Hyp319.concl_core hC58 hD15 hS316 hD125 hQ'.simple hQ'.nonabelian hQ'.qtke hQ'.sylow
    hM.1.1 h
  exact { hmain with
    shape := fun hyp5 => hShape G T hQ'.simple hQ'.nonabelian hQ'.qtke hQ'.sylow M M₀ H _ hM.1.1
      hbase hII hq hMu hVH hdual hmain hyp5 }

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_12_concl319 (h319 : Lemma319StatementCE) {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (h158 : Lemma1518Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (h16 : oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G))
    (hdual : ¬ IsDualFFOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M))
    {H : Subgroup G} (hH : IsHStar T M H) (hVH : V154 T Mc M ≤ pCoreOf 2 H) :
    Concl319 T M (V154 T Mc M) H True := by
  obtain ⟨hbase, hII⟩ := h159.six_hyp H hH
  have hV' := hbase.reduced.2.2.1
  have hq2 : qOn M (V154 T Mc M) = 2 := by
    rcases h158 with h' | h'
    · exact h'.2
    · exact h'.2.2
  have hq : qInt (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M)
      hV' = 2 := by
    rw [qInt_congr hV' h159.six_autOn, ← qOn_eq hV']
    exact hq2
  exact concl319_of_hyp5
    (h319 G T Mc M h hM hCE H _ hH hbase hII hq h159.five hVH hdual) h16

theorem stageLemma15112_of_ce (h319 : Lemma319StatementCE) (h1416 : StageLemma1416)
    (h1515 : StageLemma1515CE) (h158 : StageLemma1518) (h159 : StageLemma1519)
    (h16 : StageLemma1516CE) (h1511 : StageLemma15111) (h4 : StageLemma15112Four) :
    StageLemma15112 := by
  intro G _ _ T Mc M h hM hCE H hH
  exact ⟨lemma_15_1_12_concl319 h319 h hM hCE (h158 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE)
    (h16 G T Mc M h hM hCE) (notDualFF1512_of_ce h1416 h1515 h158 h159 G T Mc M h hM hCE) hH
    (h1511 G T Mc M h hM hCE H hH).1, h4 G T Mc M h hM hCE H hH⟩

theorem stage151_of_inputs_ce_FE (h316 : Theorem316StatementPerf) (h317 : Theorem317StatementFE)
    (h1413 : StageLemma1413) (h319 : Lemma319StatementCE) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hD : Description1512CE)
    (hN : Nilpotency1512CE) (hStep : Step1514Gen) (h157 : StageLemma1517) (h158 : StageLemma1518)
    (h1511one : StageLemma15111One) (h1512four : StageLemma15112Four) :
    StageLemma1511 ∧ StageLemma1515CE ∧ StageLemma1516CE ∧ StageLemma1519 ∧ StageLemma15112 ∧
      StageLemma15113 ∧ StageLemma15114 := by
  have h15 : StageLemma1515CE := stageLemma1515CE_of_description hD
  have h16 : StageLemma1516CE := stageLemma1516CE_of hN
  have h159 : StageLemma1519 := stageLemma1519_of_ce_FE h1414 h1417 h317 h1413 h15 h16
  have h15110 : StageLemma15110 := stageLemma15110_of_ce h1416 h15
  have h15111 : StageLemma15111 := stageLemma15111_of_one h158 h159 h1511one
  have h1512 : StageLemma15112 :=
    CFSG.Quasithin.LRed9.stageLemma15112_of_ce h319 h1416 h15 h158 h159 h16 h15111 h1512four
  have h3 : StageLemma15113Three := stageLemma15113Three_of_ce h157 h158 h159 h15 h15110
  have h4 : StageLemma15113Four := stageLemma15113Four_of_ce h157 h158 h159 h15 h15110 h1512four
  exact ⟨stageLemma1511_of_theorem316Perf h316 h1416, h15, h16, h159, h1512,
    stageLemma15113_of h157 h159 h1512 h3 h4, stageLemma15114_of_ce hStep h157 h15 h159 h16 h1512⟩

theorem theorem1515_of_inputs_ce3_FE
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h23 : Lemma15123Standalone)
    (h316 : Theorem316StatementPerf) (h317 : Theorem317StatementFE) (h1413 : StageLemma1413)
    (h319 : Lemma319StatementCE)
    (h1414 : StageLemma1414) (h1416 : StageLemma1416) (h1417 : StageLemma1417)
    (hD : Description1512CE) (hN : Nilpotency1512CE) (hStep : Step1514Gen)
    (h17 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four)
    (hI20 : Lemma15120InputU) (hI21 : Lemma15121InputU) (hI22 : Lemma15122InputU)
    (hI24 : Lemma15124InputU) (hI25 : Lemma15125InputRestU) (hI27 : Lemma15127InputU)
    (hI28 : Lemma15128InputU) (hI29 : Lemma15129InputU) : StageTheorem1515 := by
  obtain ⟨-, h15, -, h19, -, h113, h14⟩ :=
    CFSG.Quasithin.LRed9.stage151_of_inputs_ce_FE h316 h317 h1413 h319 h1414 h1416 h1417 hD hN hStep h17 h158 h1511one
      h1512four
  have h110 : StageLemma15110 := stageLemma15110_of_ce h1416 h15
  exact theorem1515_of_inputs3_ce3 h37 h38 h39 h15 h17 h19 h110 h113 h14
    (m11TypesDisjoint1522_of_orders psuThreeThreeOrder1522 threeD4TwoOrder1522) h23 hI20 hI21 hI22
    hI24 hI25 hI27 hI28 hI29

end LRed9

end CFSG.Quasithin
