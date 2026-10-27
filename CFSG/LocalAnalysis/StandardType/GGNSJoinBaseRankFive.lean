module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCardinality
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoCenter
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseE7TwoFrame
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseE8TwoFrame
import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoBstar
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoAEightE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGConfig.not_orthMinus_of_eq_bstar_card_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hRig : GGLabelRigidInput)
    (hEq : B = Bs) (hCard : Nat.card Bs = 3 ^ 5)
    (hmark : GGInnerDiagOnLabel ggRowP_EOmM 3 Bs L) : False := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Group.IsPerfect ↥L := Group.IsPerfect.mk hcfg.data_L.2.2.2
  have hsplit : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_EOmM p lab ∧ lab.n = 1) ∨
      (ggRowP_EOmM p lab ∧ 2 ≤ lab.n)) 3 Bs L :=
    hmark.mono_label fun lab hl => by
      by_cases h1 : lab.n = 1
      · exact Or.inl ⟨hl, h1⟩
      · have h0 : lab.n ≠ 0 := by
          intro h0
          have hd := hl.2.2.2
          rw [h0] at hd
          norm_num at hd
        exact Or.inr ⟨hl, by omega⟩
  rcases GGInnerDiagOnLabel.elim_or hsplit with htwo | hord
  · exact (ne_of_lt (GGConfig.lt_bstar_of_orthTwo hRig hcfg
      (htwo.mono_label fun _ hl => ⟨Or.inr hl.1, hl.2⟩))) hEq
  have hZ : ∀ lab, (ggRowP_EOmM 3 lab ∧ 2 ≤ lab.n) →
      GGHasLabel lab (L ⧸ Subgroup.center L) → Subgroup.center L = ⊥ :=
    fun lab hl hhas => OrthTorus.center_eq_bot_of_hasLabel_orth
      (Or.inr hl.1.1) (by have := hl.1.2.1; omega) hl.2 hhas
  obtain ⟨lab, hl, hhas, Φ, hr, -, -, -, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig (by decide : 3 ≠ 2) hcfg.2.1.2.1
      hcfg.2.1.2.2.2 (fun _ hl => Or.inr hl.1) hord hZ
      (fun hN => ggGamma_L_exists_ne_one hcfg hN)
  have hr5 : 5 ≤ Φ.r := by rw [hr]; exact hl.1.2.1
  have h6 : 3 ^ 6 ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 6 ≤ Φ.r + 1)).trans
      (Φ.pow_rank_succ_le_card_bstar hcfg (hZ lab hl hhas))
  rw [hCard] at h6
  norm_num at h6

theorem GGSecFiveRouteCfg.unitary_baseLabel_of_eq_bstar_card_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hRig : GGLabelRigidInput) (hEq : B = Bs) (hCard : Nat.card Bs = 3 ^ 5)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie 3 L) :
    GGInnerDiagOnLabel ggRowP_ESU 3 Bs L := by
  have hbase := ggL_baseLabel_of_nonSplit hcfg hpres h3 hns
  rcases GGInnerDiagOnLabel.elim_or hbase with hu | hbase
  · exact hu
  rcases GGInnerDiagOnLabel.elim_or hbase with ho | hbase
  · exact (hcfg.1.1.not_orthMinus_of_eq_bstar_card_five hRig hEq hCard ho).elim
  rcases GGInnerDiagOnLabel.elim_or hbase with he | hbase
  · have hm : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
      largeEvenMarking_mono (fun lab _ _ I _ θ hl =>
        ⟨⟨hl.1.1, rfl, hl.1.2⟩,
          Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, hl.1.1],
            by rw [hl.1.1]; decide, hl.1.2⟩), hl.2.1, hl.2.2⟩) he
    have h6 := ggL48TwE6_pow_six_le_card ggTwE6ThreeBstarRankInput_holds hcfg.1.1 hm
    rw [hCard] at h6
    norm_num at h6
  have hs : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_EOmP p lab ∧ lab.n = 1) ∨
      (ggRowP_EE7 p lab ∧ lab.n = 1) ∨
      (ggRowP_EE8 p lab ∧ lab.n = 1) ∨
      (ggRowP_NF4 p lab ∧ lab.n = 1)) 3 Bs L :=
    hbase.mono_label fun lab hl => by
      rcases hl with ⟨hn, -, ho | h7 | h8 | h4⟩
      · exact Or.inl ⟨ho, hn⟩
      · exact Or.inr (Or.inl ⟨h7, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h8, hn⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h4, hn⟩))
  rcases GGInnerDiagOnLabel.elim_or hs with ho | hs
  · exact ((ne_of_lt (GGConfig.lt_bstar_of_orthTwo hRig hcfg.1.1
      (ho.mono_label fun _ hl => ⟨Or.inl hl.1, hl.2⟩))) hEq).elim
  rcases GGInnerDiagOnLabel.elim_or hs with h7 | hs
  · exact ((ne_of_lt (GGConfig.lt_bstar_of_E7two hcfg.1.1 h7)) hEq).elim
  rcases GGInnerDiagOnLabel.elim_or hs with h8 | h4
  · exact ((ne_of_lt (GGConfig.lt_bstar_of_E8two hcfg.1.1 h8)) hEq).elim
  · exact (NSJoin.not_f4Three_of_cfg hcfg hpres h3
      (h4.mono_label fun _ hl => ⟨hl.1.1, rfl, by rw [hl.2]; norm_num⟩)).elim

theorem GGSecFiveRouteCfg.unitary_baseLabel_of_D4two_nbr_of_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hRig : GGLabelRigidInput) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L) :
    GGInnerDiagOnLabel ggRowP_ESU p Bs L := by
  have hmX : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hN := GGInnerDiagOn.le_normalizer hmX
  obtain ⟨rfl, hCard, -⟩ :=
    hcfg.1.1.card_bstar_twoLocalRank_of_D4two_nbr_of_eq hnb hRig hmark hN hEq
  exact hcfg.unitary_baseLabel_of_eq_bstar_card_five hRig hEq hCard hpres h3 hns

theorem GGSecFiveRouteCfg.unitary_baseLabel_singular_two_of_D4two_nbr_of_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hRig : GGLabelRigidInput) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧
      (lab.n = 1 → 3 ∣ lab.rank + 1)) p Bs L := by
  classical
  have hu := hcfg.unitary_baseLabel_of_D4two_nbr_of_eq hRig hnb hmark hEq hpres h3 hns
  have hs : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ (lab.n = 1 → 3 ∣ lab.rank + 1)) ∨
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1)) p Bs L :=
    hu.mono_label fun lab hl => by
      by_cases hn : lab.n = 1
      · by_cases hd : 3 ∣ lab.rank + 1
        · exact Or.inl ⟨hl, fun _ => hd⟩
        · exact Or.inr ⟨hl, hn, hd⟩
      · exact Or.inl ⟨hl, fun h => (hn h).elim⟩
  rcases GGInnerDiagOnLabel.elim_or hs with hs | hs
  · exact hs
  · exact ((ne_of_lt (GGConfig.lt_bstar_of_unitaryTwo hcfg.1.1 hs)) hEq).elim

theorem GGConfig.innerDiagOnLabel_unitary_rank_five_of_singular_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (h : GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) 3 Bs L)
    (hMu : LargeEvenTwoLocalRank 3 G ≤ 6) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L := by
  have hr := hcfg.innerDiagOnLabel_torusRank (P := fun p lab =>
    ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) (fun lab hl => by
    rcases hl.1.1 with ⟨ht, -⟩ | ⟨-, hr3⟩
    · exact ⟨ht, hl.2.1⟩
    · have hd := hl.2.2
      rw [hr3] at hd
      norm_num at hd) h
  exact hr.mono_label fun lab hl => by
    have hr3 : 3 ≤ lab.rank := by
      rcases hl.1.1.1 with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · omega
    have hd := hl.1.2.2
    have hb := hl.2.trans hMu
    simp only [ggUnitaryTorusRank, hd, ite_true] at hb
    obtain ⟨k, hk⟩ := hd
    exact ⟨hl.1.1, hl.1.2.1, by omega⟩

end CFSG.StandardType

end
