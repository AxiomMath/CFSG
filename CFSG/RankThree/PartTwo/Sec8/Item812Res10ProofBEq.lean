module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofFinal
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGen
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLink

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (InducesOuterTheta)

@[expose] def Fin812BMemY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n → b ∈ Y

namespace Item812Res10

variable {G : Type} [Group G] [Finite G]

theorem sec8B_le_of_memY (h84 : Pair84A) {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) (hbY : b ∈ Y) :
    sec8B A X ≤ A ⊓ Y := by
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  obtain ⟨x, hxA, hxk⟩ := h.mem_pairOmega.2.2.2.1
  have hxout : InducesOuterTheta x X := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  obtain ⟨S₀, hS₀A, -, -, -, -, hBS⟩ := Item812Res2.sec8B_structure_of_projSp
    h.toTheoremFourHyp.localRank_three.le h.mem_partTwoF h.card_eq hbA hb1 hXb h.item89_X hxA
    hxout
  have haout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) one_ne_zero ha3 haout
    h.item89_X
  have hRF := Item8KFacts2Proof.ResidualFacts.of_mulEquiv ι
    (Item8KFacts2Proof.residualFacts_projSp (m := 1) le_rfl)
  have haN : a ∈ Subgroup.normalizer (X : Set G) := haout.1
  have hS₀J : S₀.map X.subtype ≤ sec8J X a := by
    rintro _ ⟨s, hs, rfl⟩
    have hsA : (s : G) ∈ A := hS₀A ⟨s, hs, rfl⟩
    have hsa : (s : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAab.1.is_comm.comm ⟨_, hsA⟩ ⟨a, haA⟩))
    exact Item8KFacts2Proof.mem_inSubgroup_perfectResidual_of_pow_three haN ha3 hRF.1 s.2 hsa
      (hAab.2 _ hsA)
  have hJY : sec8J X a ≤ Y := le_sup_right.trans h.le_Y
  rw [hBS]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact ⟨hbA, hbY⟩
  · exact le_inf hS₀A (hS₀J.trans hJY)

end Item812Res10

open Item812Res10

theorem fin812BEq_of_memY (h84 : Pair84A) (hY : Fin812BMemY) : Fin812BEq := by
  intro G _ _ A c L a b X Y n h
  exact Subgroup.eq_of_le_of_card_ge (sec8B_le_of_memY h84 h (hY G A c L a b X Y n h))
    (by rw [Item812Res8.card_inf_Y h, Item812Res8.card_sec8B h])

end CFSG.RankThree.PartTwo.Sec8
