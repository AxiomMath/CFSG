module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentLLocal
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section LSide

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {x y : G} {L D J : Subgroup G}

theorem le_of_stdSub_left (hDJ : LargeEvenStdSub 3 B x L D J) : J ≤ L :=
  (hDJ.1.2.2.2.2.2.1.1).trans inf_le_left

theorem ggD4OddCent_jInduce_of_classical (hLT : GGLieInnerDiagInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hNL : B ≤ Subgroup.normalizer (L : Set G))
    (hLcl : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      GGLabelTwClassical lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I) :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGConjInducesOn B J θ' I' := by
  have hloc := ggD4OddCent_lLocal hI hDJ hD hyB hNL
  exact ggD4OddCent_jInduce_of_lInduce (le_of_stdSub_left hDJ) hNL
    (hLT ↥L hLcl.1 _ _ _ hloc hLcl)

theorem ggD4OddCent_not_fixed_of_classical (hLTs : GGLieSU3FixedInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hNL : B ≤ Subgroup.normalizer (L : Set G))
    (hLcl : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      GGLabelTwClassical lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I)
    (hJA2 : LargeEvenMarking ↥J fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA)
    (hZ : Subgroup.center ↥J ≠ ⊥) : ¬ GGConjFixedInCenter B J := by
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hloc := ggD4OddCent_lLocal hI hDJ hD hyB hNL
  set e := Subgroup.subgroupOfEquivOfLe hJL with he
  have hZ' : Subgroup.center ↥(J.subgroupOf L) ≠ ⊥ := fun h => hZ (center_eq_bot_of_mulEquiv e.symm h)
  have hJA2' : LargeEvenMarking ↥(J.subgroupOf L) fun lab _ _ _ _ _ =>
      GGLabelA2 lab ∧ lab.tag = .twA :=
    largeEvenMarking_congr e (fun _ _ _ _ _ _ h => h) hJA2
  have h := hLTs ↥L hLcl.1 _ _ _ hloc hZ' hLcl hJA2'
  exact fun hfix => h ((ggAutsFixedInCenter_iff hNL hJL).2 hfix)

theorem ggD4OddCent_jInduce_of_twE6 (hKG7 : GGTwE6InnerDiagInput) (hTR : GGTwE6ThreeRankInput)
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hNL : B ≤ Subgroup.normalizer (L : Set G)) (hm : LargeEvenTwoLocalRank 3 G = 5)
    (hLE : LargeEvenMarking ↥L fun lab _ _ I _ θ => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab ∧
      GGInducedInn (ggAutsOf L B hNL) θ I) :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGConjInducesOn B J θ' I' := by
  have hloc := ggD4OddCent_lLocal hI hDJ hD hyB hNL
  have hcard : Nat.card ↥(ggAutsOf L B hNL) = 3 ^ 4 := by
    rw [ggD4OddCent_card_lAuts hI hNL, hm]
  have hU := ggD4OddCent_twoGroup hI hm.le hTR hNL
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hLE)
  have hmark : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ GGInducedInn (ggAutsOf L B hNL) θ I :=
    largeEvenMarking_mono
      (fun lab _ _ I _ θ h => ⟨h.1, three_dvd_of_split_twE6 h.1 h.2.1, h.2.2⟩) hLE
  exact ggD4OddCent_jInduce_of_lInduce (le_of_stdSub_left hDJ) hNL
    (hKG7 ↥L hLE.1 _ _ _ hloc hcard hU hmark)

end LSide

end CFSG.StandardType
