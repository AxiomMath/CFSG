module

public import CFSG.Quasithin.Recognition.St84.Hyp
public import CFSG.Quasithin.Recognition.St84.Basic
public import CFSG.Quasithin.Recognition.St84.Gold26
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.F1Borel
public import CFSG.Quasithin.Background.F1Rank
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Recognition.GoldschmidtCompletion
public import CFSG.Quasithin.Recognition.GoldschmidtTreeAcyclic
public import CFSG.Quasithin.Recognition.GoldschmidtStatement
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAct
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivLoc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivTransl
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSt84HypA
public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakBalance
public import Certificates.Certificate113
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Recognition.F112WSetup
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

universe u

variable {H : Type} [Group H] [Finite H]

abbrev f112P1 (L1 L2 S : Subgroup H) : Subgroup H := L1 ⊔ bigB L1 L2 S

abbrev f112P2 (L1 L2 S : Subgroup H) : Subgroup H := L2 ⊔ bigB L1 L2 S

abbrev f112Gold (L1 L2 S : Subgroup H) :
    GoldAmalgam ↥(f112P1 L1 L2 S) ↥(f112P1 L1 L2 S ⊓ f112P2 L1 L2 S)
      ↥(f112P2 L1 L2 S) :=
  GoldAmalgam.ofSubgroupPair (f112P1 L1 L2 S) (f112P2 L1 L2 S)

@[expose] noncomputable def f112E5 (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  Subgroup.closure {u | (u ∈ (f112Gold L1 L2 S).ofA.range ∨
      u ∈ (f112Gold L1 L2 S).ofB.range) ∧ orderOf u = 5}

@[expose] noncomputable def f112M1 (L1 L2 S : Subgroup H) : Subgroup H :=
  Subgroup.closure {x | x ∈ f112P1 L1 L2 S ∧ orderOf x = 5}

@[expose] noncomputable def f112M2 (L1 L2 S : Subgroup H) : Subgroup H :=
  Subgroup.closure {x | x ∈ f112P2 L1 L2 S ∧ orderOf x = 5}

theorem f112_inf_eq_bigB_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S) :
    f112P1 L1 L2 S ⊓ f112P2 L1 L2 S = bigB L1 L2 S :=
  (prop_F19 hR).1

theorem f112_inf_eq_bigB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    f112P1 L1 L2 S ⊓ f112P2 L1 L2 S = bigB L1 L2 S :=
  f112_inf_eq_bigB_of_hyp111R (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem st84HypA_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S) {n1 n2 : ℕ}
    (h1 : IsL2Quot n1 (oTwoQuot ↥L1)) (h2 : IsL2Quot n2 (oTwoQuot ↥L2)) (hn1 : 1 ≤ n1)
    (hn2 : 1 ≤ n2) (hmax : 1 < max n1 n2) :
    St84HypA (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) n1 n2 := by
  obtain ⟨hB, hW, -, -⟩ := prop_F19 hR
  have hN := F1.bigB_le_normalizer_left hR
  have hLB1 : L1 ⊓ bigB L1 L2 S = borelOf L1 S := F1.inf_bigB_eq_borelOf hR
  have hLB2 : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
    have := F1.inf_bigB_eq_borelOf hR.symm
    rwa [bigB_comm] at this
  have hP1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer hN.1
  have hP2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
    sup_le Subgroup.le_normalizer hN.2
  refine ⟨hW.core, ?_, ?_, hn1, hn2, hmax, ?_, ?_⟩
  · rw [hB, CFSG.Quasithin.F112W.relIndex_sup_eq_relIndex_inf hN.1, hLB1]
    exact index_borelOf_of_psl2 (by omega) hR.hyp.h1.sylow h1
  · rw [hB, CFSG.Quasithin.F112W.relIndex_sup_eq_relIndex_inf hN.2, hLB2]
    exact index_borelOf_of_psl2 (by omega) hR.hyp.h2.sylow h2
  · rw [hB]
    exact st84Levi_of_vertex (by omega) hR.hyp.h1.sylow h1 le_sup_left hP1 hLB1
  · rw [hB]
    exact st84Levi_of_vertex (by omega) hR.hyp.h2.sylow h2 le_sup_left hP2 hLB2

theorem f112_relIndex_left_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hR : Hyp111R L1 L2 S) (hm : 1 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).relIndex (f112P1 L1 L2 S) = 2 ^ m + 1 := by
  rw [f112_inf_eq_bigB_of_hyp111R hR,
    CFSG.Quasithin.F112W.relIndex_sup_eq_relIndex_inf (F1.bigB_le_normalizer_left hR).1,
    F1.inf_bigB_eq_borelOf hR]
  exact index_borelOf_of_psl2 (by omega) hR.hyp.h1.sylow h1

theorem f112_relIndex_left {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).relIndex (f112P1 L1 L2 S) = 5 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  have h := (st84HypA_of_hyp111R hR h1 h2 (by norm_num) (by norm_num)
    (by norm_num)).index_left
  simpa using h

theorem f112_relIndex_right_of_isL2Quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hR : Hyp111R L1 L2 S) (hn : 1 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).relIndex (f112P2 L1 L2 S) = 2 ^ n + 1 := by
  have hLB2 : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
    have h := F1.inf_bigB_eq_borelOf hR.symm
    rwa [bigB_comm] at h
  rw [f112_inf_eq_bigB_of_hyp111R hR,
    CFSG.Quasithin.F112W.relIndex_sup_eq_relIndex_inf (F1.bigB_le_normalizer_left hR).2, hLB2]
  exact index_borelOf_of_psl2 (by omega) hR.hyp.h2.sylow h2

theorem f112_relIndex_right {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).relIndex (f112P2 L1 L2 S) = 5 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  have h := (st84HypA_of_hyp111R hR h1 h2 (by norm_num) (by norm_num)
    (by norm_num)).index_right
  simpa using h

theorem f112_edgeA_index_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hR : Hyp111R L1 L2 S) (hm : 1 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    (f112Gold L1 L2 S).edgeA.index = 2 ^ m + 1 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeA_index]
  exact f112_relIndex_left_of_isL2Quot hR hm h1

theorem f112_edgeA_index {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    (f112Gold L1 L2 S).edgeA.index = 5 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeA_index]
  exact f112_relIndex_left hF h1 h2

theorem f112_edgeB_index_of_isL2Quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hR : Hyp111R L1 L2 S) (hn : 1 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112Gold L1 L2 S).edgeB.index = 2 ^ n + 1 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeB_index]
  exact f112_relIndex_right_of_isL2Quot hR hn h2

theorem f112_edgeB_index {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    (f112Gold L1 L2 S).edgeB.index = 5 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeB_index]
  exact f112_relIndex_right hF h1 h2

theorem f112_ncard_neighborSet_alpha_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hR : Hyp111R L1 L2 S) (hm : 1 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (g : (f112Gold L1 L2 S).Universal) :
    ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseA (f112Gold L1 L2 S))).ncard = 2 ^ m + 1 := by
  rw [smul_baseA (f112Gold L1 L2 S) g]
  change ((f112Gold L1 L2 S).treeGraph.neighborSet
    (Sum.inl ((g : (f112Gold L1 L2 S).Universal) :
      (f112Gold L1 L2 S).Universal ⧸ (f112Gold L1 L2 S).ofA.range))).ncard = 2 ^ m + 1
  rw [ncard_neighborSet_inl, f112_edgeA_index_of_isL2Quot hR hm h1]

theorem f112_ncard_neighborSet_beta_of_isL2Quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hR : Hyp111R L1 L2 S) (hn : 1 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (g : (f112Gold L1 L2 S).Universal) :
    ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseB (f112Gold L1 L2 S))).ncard = 2 ^ n + 1 := by
  rw [smul_baseB (f112Gold L1 L2 S) g]
  change ((f112Gold L1 L2 S).treeGraph.neighborSet
    (Sum.inr ((g : (f112Gold L1 L2 S).Universal) :
      (f112Gold L1 L2 S).Universal ⧸ (f112Gold L1 L2 S).ofB.range))).ncard = 2 ^ n + 1
  rw [ncard_neighborSet_inr, f112_edgeB_index_of_isL2Quot hR hn h2]

theorem f112_ncard_neighborSet {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (v : Vtx (f112Gold L1 L2 S)) :
    ((f112Gold L1 L2 S).treeGraph.neighborSet v).ncard = 5 := by
  obtain ⟨g, rfl⟩ | ⟨g, rfl⟩ := exists_smul_base (f112Gold L1 L2 S) v
  · rw [smul_baseA]
    change ((f112Gold L1 L2 S).treeGraph.neighborSet
      (Sum.inl ((g : (f112Gold L1 L2 S).Universal ⧸ (f112Gold L1 L2 S).ofA.range)))).ncard = 5
    rw [ncard_neighborSet_inl, f112_edgeA_index hF h1 h2]
  · rw [smul_baseB]
    change ((f112Gold L1 L2 S).treeGraph.neighborSet
      (Sum.inr ((g : (f112Gold L1 L2 S).Universal ⧸ (f112Gold L1 L2 S).ofB.range)))).ncard = 5
    rw [ncard_neighborSet_inr, f112_edgeB_index hF h1 h2]

theorem f112_nOf_alpha_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hR : Hyp111R L1 L2 S) (hm : 1 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (g : (f112Gold L1 L2 S).Universal) :
    nOf (f112Gold L1 L2 S).treeGraph (g • baseA (f112Gold L1 L2 S)) = m := by
  unfold nOf
  have hcard : Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseA (f112Gold L1 L2 S))) = 2 ^ m + 1 := by
    rw [Nat.card_coe_set_eq]
    exact f112_ncard_neighborSet_alpha_of_isL2Quot hR hm h1 g
  rw [hcard]
  have hsub : 2 ^ m + 1 - 1 = 2 ^ m := Nat.add_sub_cancel _ _
  rw [hsub, Nat.log_pow]
  norm_num

theorem f112_nOf_beta_of_isL2Quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hR : Hyp111R L1 L2 S) (hn : 1 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (g : (f112Gold L1 L2 S).Universal) :
    nOf (f112Gold L1 L2 S).treeGraph (g • baseB (f112Gold L1 L2 S)) = n := by
  unfold nOf
  have hcard : Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseB (f112Gold L1 L2 S))) = 2 ^ n + 1 := by
    rw [Nat.card_coe_set_eq]
    exact f112_ncard_neighborSet_beta_of_isL2Quot hR hn h2 g
  rw [hcard]
  have hsub : 2 ^ n + 1 - 1 = 2 ^ n := Nat.add_sub_cancel _ _
  rw [hsub, Nat.log_pow]
  norm_num

theorem f112_nOf_eq_two {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (v : Vtx (f112Gold L1 L2 S)) :
    nOf (f112Gold L1 L2 S).treeGraph v = 2 := by
  unfold nOf
  have hcard : Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet v) = 5 := by
    rw [Nat.card_coe_set_eq]
    exact f112_ncard_neighborSet hF h1 h2 v
  rw [hcard]
  norm_num

theorem f112_valency_of_isL2Quot {L1 L2 S : Subgroup H} {m n : ℕ} (hR : Hyp111R L1 L2 S)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (v : Vtx (f112Gold L1 L2 S)) :
    1 ≤ nOf (f112Gold L1 L2 S).treeGraph v ∧
      Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet v) =
        2 ^ nOf (f112Gold L1 L2 S).treeGraph v + 1 := by
  obtain ⟨g, rfl⟩ | ⟨g, rfl⟩ := exists_smul_base (f112Gold L1 L2 S) v
  · rw [f112_nOf_alpha_of_isL2Quot hR hm h1 g, Nat.card_coe_set_eq,
      f112_ncard_neighborSet_alpha_of_isL2Quot hR hm h1 g]
    omega
  · rw [f112_nOf_beta_of_isL2Quot hR hn h2 g, Nat.card_coe_set_eq,
      f112_ncard_neighborSet_beta_of_isL2Quot hR hn h2 g]
    omega

theorem f112_valency {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (v : Vtx (f112Gold L1 L2 S)) :
    1 ≤ nOf (f112Gold L1 L2 S).treeGraph v ∧
      Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet v) =
        2 ^ nOf (f112Gold L1 L2 S).treeGraph v + 1 := by
  rw [f112_nOf_eq_two hF h1 h2 v, Nat.card_coe_set_eq,
    f112_ncard_neighborSet hF h1 h2 v]
  norm_num

theorem f112_sup_P1_P2 (L1 L2 S : Subgroup H) :
    f112P1 L1 L2 S ⊔ f112P2 L1 L2 S = L1 ⊔ L2 ⊔ S := by
  have hB1 : borelOf L1 S ≤ L1 := F1.borelOf_le L1 S
  have hB2 : borelOf L2 S ≤ L2 := F1.borelOf_le L2 S
  have hB : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hB1.trans (le_sup_left.trans le_sup_left)
    · exact hB2.trans (le_sup_right.trans le_sup_left)
    · show S ≤ (L1 ⊔ L2) ⊔ S
      exact le_sup_right
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) hB)
      (sup_le (le_sup_right.trans le_sup_left) hB)
  · refine sup_le (sup_le ?_ ?_) ?_
    · show L1 ≤ f112P1 L1 L2 S ⊔ f112P2 L1 L2 S
      exact le_sup_left.trans le_sup_left
    · show L2 ≤ f112P1 L1 L2 S ⊔ f112P2 L1 L2 S
      exact le_sup_left.trans le_sup_right
    · show S ≤ f112P1 L1 L2 S ⊔ f112P2 L1 L2 S
      have hSB : S ≤ bigB L1 L2 S := le_sup_right
      exact hSB.trans ((le_sup_right (a := L1) (b := bigB L1 L2 S)).trans le_sup_left)

theorem isFaithful_ofSubgroupPair_of_coreIn_eq_bot {D : Type*} [Group D]
    {A B : Subgroup D}
    (hcore : coreIn (A ⊓ B) (A ⊔ B) = ⊥) :
    (GoldAmalgam.ofSubgroupPair A B).IsFaithful := by
  intro K hKA hKB
  let K' : Subgroup D := K.map (A ⊓ B).subtype
  have hK' : K' ≤ A ⊓ B := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hsubA : K'.subgroupOf A =
      K.map (Subgroup.inclusion (inf_le_left : A ⊓ B ≤ A)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    exact ⟨fun ⟨c, hc, hcx⟩ => ⟨c, hc, Subtype.ext hcx⟩,
      fun ⟨c, hc, hcx⟩ => ⟨c, hc, congrArg Subtype.val hcx⟩⟩
  have hsubB : K'.subgroupOf B =
      K.map (Subgroup.inclusion (inf_le_right : A ⊓ B ≤ B)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    exact ⟨fun ⟨c, hc, hcx⟩ => ⟨c, hc, Subtype.ext hcx⟩,
      fun ⟨c, hc, hcx⟩ => ⟨c, hc, congrArg Subtype.val hcx⟩⟩
  have hAN : A ≤ Subgroup.normalizer (K' : Set D) := by
    haveI : (K'.subgroupOf A).Normal := by rw [hsubA]; exact hKA
    exact Subgroup.le_normalizer_of_normal_subgroupOf (H := K') (K := A)
      (hK'.trans inf_le_left)
  have hBN : B ≤ Subgroup.normalizer (K' : Set D) := by
    haveI : (K'.subgroupOf B).Normal := by rw [hsubB]; exact hKB
    exact Subgroup.le_normalizer_of_normal_subgroupOf (H := K') (K := B)
      (hK'.trans inf_le_right)
  have hKsup : K' ≤ A ⊔ B := fun x hx =>
    Subgroup.mem_sup_left (Subgroup.mem_inf.mp (hK' hx)).1
  have hN : A ⊔ B ≤ Subgroup.normalizer (K' : Set D) := by
    rw [sup_le_iff]
    exact ⟨hAN, hBN⟩
  have hle : K' ≤ coreIn (A ⊓ B) (A ⊔ B) :=
    le_coreIn (N := K') (K := A ⊓ B) (H := A ⊔ B) hKsup hN hK'
  rw [hcore, le_bot_iff] at hle
  exact Subgroup.map_injective (Subgroup.subtype_injective (A ⊓ B))
    (by simpa [K'] using hle)

theorem f112_isFaithful_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S) :
    (f112Gold L1 L2 S).IsFaithful := by
  apply isFaithful_ofSubgroupPair_of_coreIn_eq_bot
  rw [f112_inf_eq_bigB_of_hyp111R hR, f112_sup_P1_P2]
  exact (prop_F19 hR).2.2.1

@[expose] def f112PartsSubgroup {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) : Subgroup G where
  carrier := {g | ∀ v : V, Even (Γ.dist v (g • v))}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    have h1 := IsTree.even_dist_add_dist_add_dist hT v (g • v) ((g * h) • v)
    have hdist : Γ.dist (g • v) ((g * h) • v) = Γ.dist v (h • v) := by
      simpa [mul_smul] using IsTree.dist_smul hT hadj g v (h • v)
    rw [hdist] at h1
    have h2 : Even (Γ.dist v (g • v) + Γ.dist v (h • v)) := by
      rcases hg v with ⟨a, ha⟩
      rcases hh v with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
    exact (even_add_iff_left h2).mp (by simpa [Nat.add_assoc] using h1)
  inv_mem' := by
    intro g hg v
    have h := IsTree.dist_smul hT hadj g (g⁻¹ • v) v
    rw [smul_inv_smul] at h
    have h' : Γ.dist v (g⁻¹ • v) = Γ.dist v (g • v) := by
      rw [SimpleGraph.dist_comm (G := Γ) (u := v) (v := g⁻¹ • v), ← h]
    rw [h']
    exact hg v

@[simp] theorem mem_f112PartsSubgroup {V G : Type*} [Group G] [MulAction G V]
    {Γ : SimpleGraph V} (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) {g : G} :
    g ∈ f112PartsSubgroup hT hadj ↔ ∀ v : V, Even (Γ.dist v (g • v)) := Iff.rfl

theorem f112_stabilizer_le_parts {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (w : V) : MulAction.stabilizer G w ≤ f112PartsSubgroup hT hadj := by
  intro g hg
  rw [mem_f112PartsSubgroup]
  intro v
  have hgw : g • w = w := MulAction.mem_stabilizer_iff.mp hg
  have h1 := IsTree.even_dist_add_dist_add_dist hT v w (g • v)
  have h2 : Γ.dist w (g • v) = Γ.dist w v := by
    have h := IsTree.dist_smul hT hadj g w v
    rwa [hgw] at h
  rw [h2] at h1
  have h3 : Even (Γ.dist v w + Γ.dist w v) := by
    have hcomm : Γ.dist w v = Γ.dist v w := SimpleGraph.dist_comm
    rw [hcomm]
    exact ⟨Γ.dist v w, by omega⟩
  exact (even_add_iff_left h3).mp (by simpa [Nat.add_assoc] using h1)

theorem f112_preservesParts {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    PreservesParts (f112Gold L1 L2 S).treeGraph (f112Gold L1 L2 S).Universal := by
  let P := f112PartsSubgroup (f112Gold L1 L2 S).treeGraph_isTree
    (adj_smul (f112Gold L1 L2 S))
  have hA : (f112Gold L1 L2 S).ofA.range ≤ P := by
    intro u hu
    exact f112_stabilizer_le_parts _ _ (baseA (f112Gold L1 L2 S))
      (by simpa [stabilizer_baseA] using hu)
  have hB : (f112Gold L1 L2 S).ofB.range ≤ P := by
    intro u hu
    exact f112_stabilizer_le_parts _ _ (baseB (f112Gold L1 L2 S))
      (by simpa [stabilizer_baseB] using hu)
  have htop : P = ⊤ := by
    rw [eq_top_iff, ← (f112Gold L1 L2 S).ofA_range_sup_ofB_range]
    exact sup_le hA hB
  intro g v
  have hg : g ∈ P := by rw [htop]; trivial
  rw [mem_f112PartsSubgroup] at hg
  exact hg v

theorem f112_preservesParts_E5 {L1 L2 S : Subgroup H} :
    PreservesParts (f112Gold L1 L2 S).treeGraph (f112E5 L1 L2 S) := by
  let P := f112PartsSubgroup (f112Gold L1 L2 S).treeGraph_isTree
    (adj_smul (f112Gold L1 L2 S))
  have hgen : f112E5 L1 L2 S ≤ P := by
    change Subgroup.closure {u | (u ∈ (f112Gold L1 L2 S).ofA.range ∨
      u ∈ (f112Gold L1 L2 S).ofB.range) ∧ orderOf u = 5} ≤ P
    refine (Subgroup.closure_le P).mpr ?_
    rintro u ⟨hu | hu, -⟩
    · exact (f112_stabilizer_le_parts _ _ (baseA (f112Gold L1 L2 S)))
        (by simpa [stabilizer_baseA] using hu)
    · exact (f112_stabilizer_le_parts _ _ (baseB (f112Gold L1 L2 S)))
        (by simpa [stabilizer_baseB] using hu)
  intro g v
  have hg : ((g : (f112Gold L1 L2 S).Universal)) ∈ P := hgen g.2
  rw [mem_f112PartsSubgroup] at hg
  exact hg v

theorem f112_faithful_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S) :
    ∀ g : (f112Gold L1 L2 S).Universal,
      (∀ v : Vtx (f112Gold L1 L2 S), g • v = v) → g = 1 := by
  let X := f112Gold L1 L2 S
  have hX : X.IsFaithful := f112_isFaithful_of_hyp111R hR
  have hker := (X.universalCompletion.isFaithful_iff_ker_inf_ker_eq_bot).mp hX
  intro g hg
  have hmem : g ∈ (MulAction.toPermHom X.Universal
        (X.Universal ⧸ X.ofA.range)).ker ⊓
      (MulAction.toPermHom X.Universal (X.Universal ⧸ X.ofB.range)).ker := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      have h := hg (Sum.inl ((x : X.Universal) : X.Universal ⧸ X.ofA.range))
      simpa using h
    · rw [MonoidHom.mem_ker]
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      have h := hg (Sum.inr ((x : X.Universal) : X.Universal ⧸ X.ofB.range))
      simpa using h
  have hker' : (MulAction.toPermHom X.Universal
        (X.Universal ⧸ X.ofA.range)).ker ⊓
      (MulAction.toPermHom X.Universal (X.Universal ⧸ X.ofB.range)).ker = ⊥ := hker
  rw [hker'] at hmem
  simpa using hmem

theorem f112_faithful {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∀ g : (f112Gold L1 L2 S).Universal,
      (∀ v : Vtx (f112Gold L1 L2 S), g • v = v) → g = 1 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  exact f112_faithful_of_hyp111R hR

theorem f112_S_le_normalizer_borelOf {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    S ≤ Subgroup.normalizer (borelOf L1 S : Set H) ∧
      S ≤ Subgroup.normalizer (borelOf L2 S : Set H) := by
  constructor
  · intro s hs
    have hSL : conjSub s L1 = L1 := by
      simpa [conjSub] using
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hF.1.h1.normalizes hs)
    have hSS : conjSub s (S ⊓ L1) = S ⊓ L1 := by
      rw [conjSub_inf, conjSub_eq_of_mem hs, hSL]
    have hB : conjSub s (borelOf L1 S) = borelOf L1 S := by
      rw [borelOf, conjSub_inf, hSL, ← conjSub_normalizer s (S ⊓ L1), hSS]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hB
  · intro s hs
    have hSL : conjSub s L2 = L2 := by
      simpa [conjSub] using
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hF.1.h2.normalizes hs)
    have hSS : conjSub s (S ⊓ L2) = S ⊓ L2 := by
      rw [conjSub_inf, conjSub_eq_of_mem hs, hSL]
    have hB : conjSub s (borelOf L2 S) = borelOf L2 S := by
      rw [borelOf, conjSub_inf, hSL, ← conjSub_normalizer s (S ⊓ L2), hSS]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hB

theorem f112_card_oTwoQuot {L : Subgroup H}
    (h : VA5 L) : Nat.card (oTwoQuot ↥L) = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have := CFSG.Walter.psl2_even_card (f := 2) (by norm_num)
  norm_num at this ⊢
  exact this

theorem f112_not_25_dvd_card {L : Subgroup H}
    (h : VA5 L) : ¬ 25 ∣ Nat.card ↥L := by
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).exists_card_eq
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  rw [hcard, f112_card_oTwoQuot h, ha]
  have h2 : ¬ 5 ∣ 2 ^ a := by
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    norm_num at this
  intro h25
  have hdvd : 5 ∣ 12 * 2 ^ a := by
    have h := h25
    rw [show (25 : ℕ) = 5 * 5 by norm_num,
      show (60 : ℕ) * 2 ^ a = 5 * (12 * 2 ^ a) by ring] at h
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).mp h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
  · norm_num at h'
  · exact h2 h'

theorem f112_not_five_dvd_borelOf {L S : Subgroup H}
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L) (h : VA5 L) :
    ¬ 5 ∣ Nat.card ↥(borelOf L S) := by
  have hrel : (borelOf L S).relIndex L = 5 := by
    have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hsyl h
    simpa [Subgroup.relIndex] using h'
  have hcard : 5 * Nat.card ↥(borelOf L S) = Nat.card ↥L := by
    have h' := Subgroup.relIndex_mul_card (borelOf L S) L
    rw [inf_eq_left.mpr (F1.borelOf_le L S), hrel] at h'
    exact h'
  intro h5
  apply f112_not_25_dvd_card h
  obtain ⟨c, hc⟩ := h5
  exact ⟨c, by rw [← hcard, hc]; ring⟩

theorem f112_not_five_dvd_card_bigB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ¬ 5 ∣ Nat.card (bigB L1 L2 S) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  have hB1 : ¬ 5 ∣ Nat.card ↥(borelOf L1 S) :=
    f112_not_five_dvd_borelOf hF.1.h1.sylow h1
  have hB2 : ¬ 5 ∣ Nat.card ↥(borelOf L2 S) :=
    f112_not_five_dvd_borelOf hF.1.h2.sylow h2
  have hS : ¬ 5 ∣ Nat.card ↥S := by
    obtain ⟨a, ha⟩ := hF.1.h1.pgroup.exists_card_eq
    rw [ha]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    norm_num at this
  have hSN : S ≤ Subgroup.normalizer ((borelOf L1 S ⊔ borelOf L2 S : Subgroup H) : Set H) :=
    le_normalizer_sup (f112_S_le_normalizer_borelOf hF).1
      (f112_S_le_normalizer_borelOf hF).2
  have hK : ¬ 5 ∣ Nat.card ↥(borelOf L1 S ⊔ borelOf L2 S) := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.not_dvd_card_sup_of_le_normalizer
      Nat.prime_five (F1.borelOf_le_normalizer_borelOf hR) hB2 hB1
    simpa [sup_comm] using h
  have h := CFSG.HardMathSupport.Solomon.Coordinator.not_dvd_card_sup_of_le_normalizer
    Nat.prime_five hSN hS hK
  simpa [bigB, sup_comm, sup_left_comm, sup_assoc] using h

theorem f112_card_P1 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    5 * Nat.card ↥(bigB L1 L2 S) = Nat.card ↥(f112P1 L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  have h := Subgroup.relIndex_mul_card (bigB L1 L2 S) (f112P1 L1 L2 S)
  rw [inf_eq_left.mpr le_sup_right,
    show (bigB L1 L2 S).relIndex (f112P1 L1 L2 S) = 5 from by
      rw [← f112_inf_eq_bigB_of_hyp111R hR]; exact f112_relIndex_left hF h1 h2] at h
  exact h

theorem f112_card_P2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    5 * Nat.card ↥(bigB L1 L2 S) = Nat.card ↥(f112P2 L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  have h := Subgroup.relIndex_mul_card (bigB L1 L2 S) (f112P2 L1 L2 S)
  rw [inf_eq_left.mpr le_sup_right,
    show (bigB L1 L2 S).relIndex (f112P2 L1 L2 S) = 5 from by
      rw [← f112_inf_eq_bigB_of_hyp111R hR]; exact f112_relIndex_right hF h1 h2] at h
  exact h

theorem f112_edgeA_card (L1 L2 S : Subgroup H) :
    Nat.card ↥((f112Gold L1 L2 S).edgeA) =
      Nat.card ↥(f112P1 L1 L2 S ⊓ f112P2 L1 L2 S) := by
  have hedge : (f112Gold L1 L2 S).edgeA =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P1 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_left).range = _
    exact Subgroup.inclusion_range inf_le_left
  rw [hedge]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem f112_edgeB_card (L1 L2 S : Subgroup H) :
    Nat.card ↥((f112Gold L1 L2 S).edgeB) =
      Nat.card ↥(f112P1 L1 L2 S ⊓ f112P2 L1 L2 S) := by
  have hedge : (f112Gold L1 L2 S).edgeB =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_right).range = _
    exact Subgroup.inclusion_range inf_le_right
  rw [hedge]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem f112_orderFive_not_fixed_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S)
    (hB : ¬ 5 ∣ Nat.card (bigB L1 L2 S))
    {x : (f112Gold L1 L2 S).Universal} (hxA : x ∈ (f112Gold L1 L2 S).ofA.range)
    (hx5 : orderOf x = 5) {w : Vtx (f112Gold L1 L2 S)}
    (hw : (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) w) :
    x • w ≠ w := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let X := f112Gold L1 L2 S
  obtain ⟨a, rfl⟩ := (adj_baseA_iff X w).1 hw
  intro hfix
  obtain ⟨y, rfl⟩ := hxA
  have hy5 : orderOf y = 5 := by
    rw [← hx5]
    exact (orderOf_injective X.ofA X.ofA_injective y).symm
  have hmem : a⁻¹ * y * a ∈ X.edgeA := (ofA_smul_inr_eq_self_iff X y a).1 hfix
  have hmem5 : orderOf (a⁻¹ * y * a) = 5 := by
    apply orderOf_eq_prime
    · have hy_pow : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
      have h : a⁻¹ * y * a = a⁻¹ * y * (a⁻¹)⁻¹ := by simp
      rw [h, conj_pow, hy_pow]
      simp
    · intro h1
      have hy1 : y = 1 := by
        have := congrArg (fun z => a * z * a⁻¹) h1
        simpa [mul_assoc] using this
      rw [hy1] at hy5
      simp at hy5
  have hdvd : 5 ∣ Nat.card ↥X.edgeA := by
    have := orderOf_dvd_natCard (⟨a⁻¹ * y * a, hmem⟩ : ↥X.edgeA)
    rw [← Subgroup.orderOf_coe (⟨a⁻¹ * y * a, hmem⟩ : ↥X.edgeA), hmem5] at this
    exact this
  rw [f112_edgeA_card, f112_inf_eq_bigB_of_hyp111R hR] at hdvd
  exact hB hdvd

theorem f112_orderFive_not_fixed {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hB : ¬ 5 ∣ Nat.card (bigB L1 L2 S))
    {x : (f112Gold L1 L2 S).Universal} (hxA : x ∈ (f112Gold L1 L2 S).ofA.range)
    (hx5 : orderOf x = 5) {w : Vtx (f112Gold L1 L2 S)}
    (hw : (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) w) :
    x • w ≠ w :=
  f112_orderFive_not_fixed_of_hyp111R (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hB hxA hx5 hw

theorem f112_orderFive_not_fixed_beta_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S)
    (hB : ¬ 5 ∣ Nat.card (bigB L1 L2 S))
    {x : (f112Gold L1 L2 S).Universal} (hxB : x ∈ (f112Gold L1 L2 S).ofB.range)
    (hx5 : orderOf x = 5) {w : Vtx (f112Gold L1 L2 S)}
    (hw : (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) w) :
    x • w ≠ w := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let X := f112Gold L1 L2 S
  obtain ⟨a, rfl⟩ := (adj_baseB_iff X w).1 hw
  intro hfix
  obtain ⟨y, rfl⟩ := hxB
  have hy5 : orderOf y = 5 := by
    rw [← hx5]
    exact (orderOf_injective X.ofB X.ofB_injective y).symm
  have hmem : a⁻¹ * y * a ∈ X.edgeB := (ofB_smul_inl_eq_self_iff X y a).1 hfix
  have hmem5 : orderOf (a⁻¹ * y * a) = 5 := by
    apply orderOf_eq_prime
    · have hy_pow : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
      have h : a⁻¹ * y * a = a⁻¹ * y * (a⁻¹)⁻¹ := by simp
      rw [h, conj_pow, hy_pow]
      simp
    · intro h1
      have hy1 : y = 1 := by
        have := congrArg (fun z => a * z * a⁻¹) h1
        simpa [mul_assoc] using this
      rw [hy1] at hy5
      simp at hy5
  have hdvd : 5 ∣ Nat.card ↥X.edgeB := by
    have := orderOf_dvd_natCard (⟨a⁻¹ * y * a, hmem⟩ : ↥X.edgeB)
    rw [← Subgroup.orderOf_coe (⟨a⁻¹ * y * a, hmem⟩ : ↥X.edgeB), hmem5] at this
    exact this
  rw [f112_edgeB_card, f112_inf_eq_bigB_of_hyp111R hR] at hdvd
  exact hB hdvd

theorem f112_orderFive_not_fixed_beta {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hB : ¬ 5 ∣ Nat.card (bigB L1 L2 S))
    {x : (f112Gold L1 L2 S).Universal} (hxB : x ∈ (f112Gold L1 L2 S).ofB.range)
    (hx5 : orderOf x = 5) {w : Vtx (f112Gold L1 L2 S)}
    (hw : (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) w) :
    x • w ≠ w :=
  f112_orderFive_not_fixed_beta_of_hyp111R (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hB hxB
    hx5 hw

theorem f112_preservesParts_E5' {L1 L2 S : Subgroup H} :
    PreservesParts (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S) := by
  intro g v
  exact f112_preservesParts_E5 (g := g) v

theorem f112_transitive_of_orderFive_alpha {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {x : (f112Gold L1 L2 S).Universal} (hxA : x ∈ (f112Gold L1 L2 S).ofA.range)
    (hx5 : orderOf x = 5) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112E5 L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseA (f112Gold L1 L2 S)),
        g • a = b := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let X := f112Gold L1 L2 S
  have hxfix : x • baseA X = baseA X := by
    rw [← stabilizer_baseA X] at hxA
    exact MulAction.mem_stabilizer_iff.mp hxA
  have hfin : (X.treeGraph.neighborSet (baseA X)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [f112_ncard_neighborSet hF h1 h2]; norm_num)
  haveI : Finite (X.treeGraph.neighborSet (baseA X)) := hfin.to_subtype
  haveI : Fintype (X.treeGraph.neighborSet (baseA X)) := Fintype.ofFinite _
  let e : Equiv.Perm (X.treeGraph.neighborSet (baseA X)) :=
  { toFun := fun w => ⟨x • w.1, by
        have h := (adj_smul X x (baseA X) w.1).2 w.2
        simpa [hxfix] using h⟩
    invFun := fun w => ⟨x⁻¹ • w.1, by
        have hxinv : x⁻¹ • baseA X = baseA X := by
          calc x⁻¹ • baseA X = x⁻¹ • (x • baseA X) := by rw [hxfix]
            _ = baseA X := by simp
        have h := (adj_smul X x⁻¹ (baseA X) w.1).2 w.2
        simpa [hxinv] using h⟩
    left_inv := fun w => by ext; simp
    right_inv := fun w => by ext; simp }
  have hpow_all : ∀ (n : ℕ) (w : X.treeGraph.neighborSet (baseA X)),
      ((e ^ n) w).1 = x ^ n • w.1 := by
    intro n w
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change (x • ((e ^ n) w).1) = x ^ (n + 1) • w.1
      rw [ih, ← mul_smul, ← pow_succ']
  have he5 : e ^ 5 = 1 := by
    ext w
    have hxpow : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
    rw [hpow_all 5 w, hxpow]
    simp
  have he1 : e ≠ 1 := by
    intro he
    have hw : e ⟨baseB X, adj_baseA_baseB X⟩ = ⟨baseB X, adj_baseA_baseB X⟩ := by
      rw [he]; rfl
    exact f112_orderFive_not_fixed_of_hyp111R hR (f112_not_five_dvd_card_bigB hF h1 h2) hxA hx5
      (adj_baseA_baseB X) (congrArg Subtype.val hw)
  have hord : orderOf e = 5 := by
    exact orderOf_eq_prime he5 he1
  have hcardN : Fintype.card (X.treeGraph.neighborSet (baseA X)) = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, f112_ncard_neighborSet hF h1 h2]
  have hcycle : e.IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order' ?_ ?_
    · rw [hord]; norm_num
    · rw [hcardN, hord]; norm_num
  intro a b ha hb
  let A : X.treeGraph.neighborSet (baseA X) := ⟨a, ha⟩
  let B : X.treeGraph.neighborSet (baseA X) := ⟨b, hb⟩
  have hAfix : e A ≠ A := by
    intro h
    exact f112_orderFive_not_fixed_of_hyp111R hR (f112_not_five_dvd_card_bigB hF h1 h2) hxA hx5 ha
      (congrArg Subtype.val h)
  have hBfix : e B ≠ B := by
    intro h
    exact f112_orderFive_not_fixed_of_hyp111R hR (f112_not_five_dvd_card_bigB hF h1 h2) hxA hx5 hb
      (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := hcycle.exists_pow_eq hAfix hBfix
  refine ⟨x ^ k, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr
      ⟨Subgroup.zpow_mem (K := f112E5 L1 L2 S) (Subgroup.subset_closure ?_) k, ?_⟩
    · exact ⟨Or.inl hxA, hx5⟩
    · exact Subgroup.zpow_mem (K := MulAction.stabilizer X.Universal (baseA X))
        (MulAction.mem_stabilizer_iff.mpr hxfix) k
  · have hkb : x ^ k • a = b := by
      have := congrArg Subtype.val hk
      rwa [hpow_all k A] at this
    exact hkb

theorem f112_transitive_of_orderFive_beta {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {x : (f112Gold L1 L2 S).Universal} (hxB : x ∈ (f112Gold L1 L2 S).ofB.range)
    (hx5 : orderOf x = 5) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112E5 L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseB (f112Gold L1 L2 S)),
        g • a = b := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let X := f112Gold L1 L2 S
  have hxfix : x • baseB X = baseB X := by
    rw [← stabilizer_baseB X] at hxB
    exact MulAction.mem_stabilizer_iff.mp hxB
  have hfin : (X.treeGraph.neighborSet (baseB X)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [f112_ncard_neighborSet hF h1 h2]; norm_num)
  haveI : Finite (X.treeGraph.neighborSet (baseB X)) := hfin.to_subtype
  haveI : Fintype (X.treeGraph.neighborSet (baseB X)) := Fintype.ofFinite _
  let e : Equiv.Perm (X.treeGraph.neighborSet (baseB X)) :=
  { toFun := fun w => ⟨x • w.1, by
        have h := (adj_smul X x (baseB X) w.1).2 w.2
        simpa [hxfix] using h⟩
    invFun := fun w => ⟨x⁻¹ • w.1, by
        have hxinv : x⁻¹ • baseB X = baseB X := by
          calc x⁻¹ • baseB X = x⁻¹ • (x • baseB X) := by rw [hxfix]
            _ = baseB X := by simp
        have h := (adj_smul X x⁻¹ (baseB X) w.1).2 w.2
        simpa [hxinv] using h⟩
    left_inv := fun w => by ext; simp
    right_inv := fun w => by ext; simp }
  have hpow_all : ∀ (n : ℕ) (w : X.treeGraph.neighborSet (baseB X)),
      ((e ^ n) w).1 = x ^ n • w.1 := by
    intro n w
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change (x • ((e ^ n) w).1) = x ^ (n + 1) • w.1
      rw [ih, ← mul_smul, ← pow_succ']
  have he5 : e ^ 5 = 1 := by
    ext w
    have hxpow : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
    rw [hpow_all 5 w, hxpow]
    simp
  have he1 : e ≠ 1 := by
    intro he
    have hw : e ⟨baseA X, (adj_baseA_baseB X).symm⟩ = ⟨baseA X, (adj_baseA_baseB X).symm⟩ := by
      rw [he]; rfl
    exact f112_orderFive_not_fixed_beta_of_hyp111R hR (f112_not_five_dvd_card_bigB hF h1 h2) hxB hx5
      (adj_baseA_baseB X).symm (congrArg Subtype.val hw)
  have hord : orderOf e = 5 := by
    exact orderOf_eq_prime he5 he1
  have hcardN : Fintype.card (X.treeGraph.neighborSet (baseB X)) = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, f112_ncard_neighborSet hF h1 h2]
  have hcycle : e.IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order' ?_ ?_
    · rw [hord]; norm_num
    · rw [hcardN, hord]; norm_num
  intro a b ha hb
  let A : X.treeGraph.neighborSet (baseB X) := ⟨a, ha⟩
  let B : X.treeGraph.neighborSet (baseB X) := ⟨b, hb⟩
  have hAfix : e A ≠ A := by
    intro h
    exact f112_orderFive_not_fixed_beta_of_hyp111R hR
      (f112_not_five_dvd_card_bigB hF h1 h2) hxB hx5 ha
      (congrArg Subtype.val h)
  have hBfix : e B ≠ B := by
    intro h
    exact f112_orderFive_not_fixed_beta_of_hyp111R hR
      (f112_not_five_dvd_card_bigB hF h1 h2) hxB hx5 hb
      (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := hcycle.exists_pow_eq hAfix hBfix
  refine ⟨x ^ k, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr
      ⟨Subgroup.zpow_mem (K := f112E5 L1 L2 S) (Subgroup.subset_closure ?_) k, ?_⟩
    · exact ⟨Or.inr hxB, hx5⟩
    · exact Subgroup.zpow_mem (K := MulAction.stabilizer X.Universal (baseB X))
        (MulAction.mem_stabilizer_iff.mpr hxfix) k
  · have hkb : x ^ k • a = b := by
      have := congrArg Subtype.val hk
      rwa [hpow_all k A] at this
    exact hkb

theorem f112_exists_orderFive_ofA {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∃ x ∈ (f112Gold L1 L2 S).ofA.range, orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5dvd : 5 ∣ Nat.card ↥(f112P1 L1 L2 S) :=
    ⟨Nat.card ↥(bigB L1 L2 S), (f112_card_P1 hF h1 h2).symm⟩
  obtain ⟨y, hy5⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  refine ⟨(f112Gold L1 L2 S).ofA y, ⟨y, rfl⟩, ?_⟩
  rw [← hy5]
  exact orderOf_injective (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective y

theorem f112_exists_orderFive_ofB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∃ x ∈ (f112Gold L1 L2 S).ofB.range, orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5dvd : 5 ∣ Nat.card ↥(f112P2 L1 L2 S) :=
    ⟨Nat.card ↥(bigB L1 L2 S), (f112_card_P2 hF h1 h2).symm⟩
  obtain ⟨y, hy5⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  refine ⟨(f112Gold L1 L2 S).ofB y, ⟨y, rfl⟩, ?_⟩
  rw [← hy5]
  exact orderOf_injective (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective y

theorem f112_locTransBase {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    (∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112E5 L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseA (f112Gold L1 L2 S)),
        g • a = b) ∧
    (∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112E5 L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseB (f112Gold L1 L2 S)),
        g • a = b) := by
  obtain ⟨x, hxA, hx5⟩ := f112_exists_orderFive_ofA hF h1 h2
  obtain ⟨y, hyB, hy5⟩ := f112_exists_orderFive_ofB hF h1 h2
  exact ⟨f112_transitive_of_orderFive_alpha hF h1 h2 hxA hx5,
    f112_transitive_of_orderFive_beta hF h1 h2 hyB hy5⟩

theorem f112_mem_of_orderFive {G : Type*} [Group G] {M K : Subgroup G} (hMnorm : M.Normal)
    (h5Mα : 5 ∣ Nat.card ↥(M ⊓ K)) (hnot5 : ¬ 5 ∣ (M ⊓ K).relIndex K)
    {x : G} (hxK : x ∈ K) (hx5 : orderOf x = 5) : x ∈ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let Mα : Subgroup G := M ⊓ K
  have hMαn : (Mα.subgroupOf K).Normal := by
    have h : (M.subgroupOf K).Normal := hMnorm.subgroupOf K
    convert h using 1
    ext y
    simp [Mα, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  let q : K →* K ⧸ Mα.subgroupOf K := QuotientGroup.mk' (Mα.subgroupOf K)
  have hxpow : (⟨x, hxK⟩ : K) ^ 5 = 1 := by
    apply Subtype.ext
    have hxpow' : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
    simpa using hxpow'
  have hq5 : (q ⟨x, hxK⟩) ^ 5 = 1 := by
    rw [← map_pow, hxpow, map_one]
  have hord : orderOf (q ⟨x, hxK⟩) ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
  have hcarddvd : orderOf (q ⟨x, hxK⟩) ∣ Nat.card (K ⧸ Mα.subgroupOf K) :=
    orderOf_dvd_natCard _
  have hqcard : Nat.card (K ⧸ Mα.subgroupOf K) = Mα.relIndex K := by
    rw [← Subgroup.index_eq_card (H := Mα.subgroupOf K)]
    rfl
  have hnot5q : ¬ 5 ∣ Nat.card (K ⧸ Mα.subgroupOf K) := by
    rwa [hqcard]
  have hcop : Nat.Coprime 5 (Nat.card (K ⧸ Mα.subgroupOf K)) :=
    Nat.prime_five.coprime_iff_not_dvd.mpr hnot5q
  have hdvd1 : orderOf (q ⟨x, hxK⟩) ∣ 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one.mp hcop]
    exact Nat.dvd_gcd hord hcarddvd
  have hq1 : q ⟨x, hxK⟩ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hmem : (⟨x, hxK⟩ : K) ∈ Mα.subgroupOf K := (QuotientGroup.eq_one_iff _).mp hq1
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1

theorem f112_minimality {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∀ M : Subgroup ↥(f112E5 L1 L2 S), M.Normal →
      EdgeTransitive (f112Gold L1 L2 S).treeGraph M → M = ⊤ := by
  intro M hMnorm hMtrans
  let X := f112Gold L1 L2 S
  let H' := ↥(f112E5 L1 L2 S)
  let K : Subgroup ↥(f112E5 L1 L2 S) :=
    MulAction.stabilizer ↥(f112E5 L1 L2 S) (baseA X)
  let Mα : Subgroup ↥(f112E5 L1 L2 S) := M ⊓ K
  have hKdef : K = (MulAction.stabilizer X.Universal (baseA X)).subgroupOf
      (f112E5 L1 L2 S) := by
    change MulAction.stabilizer ↥(f112E5 L1 L2 S) (baseA X) = _
    rw [← MulAction.stabilizer_subgroupOf (f112E5 L1 L2 S) (baseA X)]
  haveI hKfin : Finite K := by
    rw [hKdef]
    haveI : Finite (MulAction.stabilizer X.Universal (baseA X)) :=
      finite_stabilizer X (baseA X)
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer X.Universal (baseA X)).subgroupOf (f112E5 L1 L2 S)) =>
        (⟨(x.1 : X.Universal), x.2⟩ : ↥(MulAction.stabilizer X.Universal (baseA X))))
      (by intro a b h
          exact Subtype.ext (Subtype.ext
            (congrArg (fun y : ↥(MulAction.stabilizer X.Universal (baseA X)) =>
              (y : X.Universal)) h)))
  have hMα_transA : ∀ a b : Vtx X, X.treeGraph.Adj (baseA X) a →
      X.treeGraph.Adj (baseA X) b → ∃ g ∈ Mα, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgM, hcase⟩ := hMtrans (baseA X) a (baseA X) b ha hb
    rcases hcase with ⟨hgα, hgab⟩ | ⟨hgα, hga⟩
    · refine ⟨g, ⟨hgM, ?_⟩, hgab⟩
      exact MulAction.mem_stabilizer_iff.mpr hgα
    · exfalso
      have hdist : X.treeGraph.dist (baseA X) (g • baseA X) = 1 := by
        rw [hgα]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hb
      have heven := f112_preservesParts_E5' (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseA X)
      rw [hdist] at heven
      norm_num at heven
  have h5Mα : 5 ∣ Nat.card ↥Mα := by
    have hbaseB : X.treeGraph.Adj (baseA X) (baseB X) := adj_baseA_baseB X
    have horbit : MulAction.orbit Mα (baseB X) = X.treeGraph.neighborSet (baseA X) := by
      ext b
      constructor
      · rintro ⟨g, rfl⟩
        have hgK : (g : ↥(f112E5 L1 L2 S)) ∈ K := (Subgroup.mem_inf.mp g.2).2
        have hgfix : (g : ↥(f112E5 L1 L2 S)) • baseA X = baseA X :=
          MulAction.mem_stabilizer_iff.mp hgK
        have hgfixU : (g : X.Universal) • baseA X = baseA X := hgfix
        have h := (adj_smul X (g : X.Universal) (baseA X) (baseB X)).2 hbaseB
        rwa [hgfixU] at h
      · intro hb
        obtain ⟨g, hg, hgab⟩ := hMα_transA (baseB X) b hbaseB hb
        exact ⟨⟨g, hg⟩, hgab⟩
    have hidx : (MulAction.stabilizer Mα (baseB X)).index = 5 := by
      rw [MulAction.index_stabilizer Mα (baseB X), horbit,
        f112_ncard_neighborSet hF h1 h2]
    have hcard := Subgroup.card_mul_index (MulAction.stabilizer Mα (baseB X))
    rw [hidx] at hcard
    exact ⟨Nat.card ↥(MulAction.stabilizer Mα (baseB X)),
      by rw [← hcard, mul_comm]⟩
  have hKcard_eq : Nat.card ↥K =
      Nat.card ↥(f112E5 L1 L2 S ⊓ MulAction.stabilizer X.Universal (baseA X)) := by
    rw [hKdef]
    have hEq : (MulAction.stabilizer X.Universal (baseA X)).subgroupOf (f112E5 L1 L2 S) =
        (f112E5 L1 L2 S ⊓ MulAction.stabilizer X.Universal (baseA X)).subgroupOf
          (f112E5 L1 L2 S) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hKdvd : Nat.card ↥K ∣ Nat.card ↥(MulAction.stabilizer X.Universal (baseA X)) := by
    rw [hKcard_eq]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hUα_card : Nat.card ↥(MulAction.stabilizer X.Universal (baseA X)) =
      5 * Nat.card ↥(bigB L1 L2 S) := by
    rw [stabilizer_baseA X]
    have hrange : Nat.card ↥X.ofA.range = Nat.card ↥(f112P1 L1 L2 S) :=
      (Nat.card_congr (MonoidHom.ofInjective X.ofA_injective).toEquiv).symm
    rw [hrange, ← f112_card_P1 hF h1 h2]
  have hP1_25 : ¬ 25 ∣ 5 * Nat.card ↥(bigB L1 L2 S) := by
    intro h
    have h' : (5 * 5) ∣ 5 * Nat.card ↥(bigB L1 L2 S) := by
      simpa [show (25 : ℕ) = 5 * 5 by norm_num] using h
    exact (f112_not_five_dvd_card_bigB hF h1 h2)
      ((Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).mp h')
  have hUα25 : ¬ 25 ∣ Nat.card ↥(MulAction.stabilizer X.Universal (baseA X)) := by
    rw [hUα_card]; exact hP1_25
  have hK25 : ¬ 25 ∣ Nat.card ↥K := fun h => hUα25 (h.trans hKdvd)
  have hrel : Mα.relIndex K * Nat.card ↥Mα = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card Mα K
    rwa [inf_eq_left.mpr inf_le_right] at h
  have hnot5A : ¬ 5 ∣ Mα.relIndex K := by
    intro h5
    have h25 : 25 ∣ Nat.card ↥K := by
      rw [← hrel]
      have := mul_dvd_mul h5 h5Mα
      simpa [show (25 : ℕ) = 5 * 5 by norm_num] using this
    exact hK25 h25
  let Kβ : Subgroup ↥(f112E5 L1 L2 S) :=
    MulAction.stabilizer ↥(f112E5 L1 L2 S) (baseB X)
  let Mβ : Subgroup ↥(f112E5 L1 L2 S) := M ⊓ Kβ
  have hKβdef : Kβ = (MulAction.stabilizer X.Universal (baseB X)).subgroupOf
      (f112E5 L1 L2 S) := by
    change MulAction.stabilizer ↥(f112E5 L1 L2 S) (baseB X) = _
    rw [← MulAction.stabilizer_subgroupOf (f112E5 L1 L2 S) (baseB X)]
  haveI hKβfin : Finite Kβ := by
    rw [hKβdef]
    haveI : Finite (MulAction.stabilizer X.Universal (baseB X)) :=
      finite_stabilizer X (baseB X)
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer X.Universal (baseB X)).subgroupOf (f112E5 L1 L2 S)) =>
        (⟨(x.1 : X.Universal), x.2⟩ : ↥(MulAction.stabilizer X.Universal (baseB X))))
      (by intro a b h
          exact Subtype.ext (Subtype.ext
            (congrArg (fun y : ↥(MulAction.stabilizer X.Universal (baseB X)) =>
              (y : X.Universal)) h)))
  have hMβ_transB : ∀ a b : Vtx X, X.treeGraph.Adj (baseB X) a →
      X.treeGraph.Adj (baseB X) b → ∃ g ∈ Mβ, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgM, hcase⟩ := hMtrans (baseB X) a (baseB X) b ha hb
    rcases hcase with ⟨hgβ, hgab⟩ | ⟨hgβ, hga⟩
    · refine ⟨g, ⟨hgM, ?_⟩, hgab⟩
      exact MulAction.mem_stabilizer_iff.mpr hgβ
    · exfalso
      have hdist : X.treeGraph.dist (baseB X) (g • baseB X) = 1 := by
        rw [hgβ]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hb
      have heven := f112_preservesParts_E5' (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseB X)
      rw [hdist] at heven
      norm_num at heven
  have h5Mβ : 5 ∣ Nat.card ↥Mβ := by
    have hbaseA : X.treeGraph.Adj (baseB X) (baseA X) := (adj_baseA_baseB X).symm
    have horbit : MulAction.orbit Mβ (baseA X) = X.treeGraph.neighborSet (baseB X) := by
      ext b
      constructor
      · rintro ⟨g, rfl⟩
        have hgK : (g : ↥(f112E5 L1 L2 S)) ∈ Kβ := (Subgroup.mem_inf.mp g.2).2
        have hgfix : (g : ↥(f112E5 L1 L2 S)) • baseB X = baseB X :=
          MulAction.mem_stabilizer_iff.mp hgK
        have hgfixU : (g : X.Universal) • baseB X = baseB X := hgfix
        have h := (adj_smul X (g : X.Universal) (baseB X) (baseA X)).2 hbaseA
        rwa [hgfixU] at h
      · intro hb
        obtain ⟨g, hg, hgab⟩ := hMβ_transB (baseA X) b hbaseA hb
        exact ⟨⟨g, hg⟩, hgab⟩
    have hidx : (MulAction.stabilizer Mβ (baseA X)).index = 5 := by
      rw [MulAction.index_stabilizer Mβ (baseA X), horbit,
        f112_ncard_neighborSet hF h1 h2]
    have hcard := Subgroup.card_mul_index (MulAction.stabilizer Mβ (baseA X))
    rw [hidx] at hcard
    exact ⟨Nat.card ↥(MulAction.stabilizer Mβ (baseA X)),
      by rw [← hcard, mul_comm]⟩
  have hKβcard_eq : Nat.card ↥Kβ =
      Nat.card ↥(f112E5 L1 L2 S ⊓ MulAction.stabilizer X.Universal (baseB X)) := by
    rw [hKβdef]
    have hEq : (MulAction.stabilizer X.Universal (baseB X)).subgroupOf (f112E5 L1 L2 S) =
        (f112E5 L1 L2 S ⊓ MulAction.stabilizer X.Universal (baseB X)).subgroupOf
          (f112E5 L1 L2 S) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hKβdvd : Nat.card ↥Kβ ∣ Nat.card ↥(MulAction.stabilizer X.Universal (baseB X)) := by
    rw [hKβcard_eq]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hUβ_card : Nat.card ↥(MulAction.stabilizer X.Universal (baseB X)) =
      5 * Nat.card ↥(bigB L1 L2 S) := by
    rw [stabilizer_baseB X]
    have hrange : Nat.card ↥X.ofB.range = Nat.card ↥(f112P2 L1 L2 S) :=
      (Nat.card_congr (MonoidHom.ofInjective X.ofB_injective).toEquiv).symm
    rw [hrange, ← f112_card_P2 hF h1 h2]
  have hUβ25 : ¬ 25 ∣ Nat.card ↥(MulAction.stabilizer X.Universal (baseB X)) := by
    rw [hUβ_card]; exact hP1_25
  have hKβ25 : ¬ 25 ∣ Nat.card ↥Kβ := fun h => hUβ25 (h.trans hKβdvd)
  have hrelβ : Mβ.relIndex Kβ * Nat.card ↥Mβ = Nat.card ↥Kβ := by
    have h := Subgroup.relIndex_mul_card Mβ Kβ
    rwa [inf_eq_left.mpr inf_le_right] at h
  have hnot5B : ¬ 5 ∣ Mβ.relIndex Kβ := by
    intro h5
    have h25 : 25 ∣ Nat.card ↥Kβ := by
      rw [← hrelβ]
      have := mul_dvd_mul h5 h5Mβ
      simpa [show (25 : ℕ) = 5 * 5 by norm_num] using this
    exact hKβ25 h25
  have hgen : ∀ x : X.Universal, x ∈ f112E5 L1 L2 S →
      (x ∈ X.ofA.range ∨ x ∈ X.ofB.range) → orderOf x = 5 →
        x ∈ M.map (f112E5 L1 L2 S).subtype := by
    intro x hxE5 hxAorB hx5
    have hxH : (⟨x, hxE5⟩ : H') ∈ M := by
      rcases hxAorB with hxA | hxB
      · have hxK : (⟨x, hxE5⟩ : H') ∈ K := by
          show (⟨x, hxE5⟩ : H') ∈ MulAction.stabilizer H' (baseA X)
          rw [MulAction.mem_stabilizer_iff]
          change x • baseA X = baseA X
          have hxstab : x ∈ MulAction.stabilizer X.Universal (baseA X) := by
            rw [stabilizer_baseA X]; exact hxA
          exact MulAction.mem_stabilizer_iff.mp hxstab
        refine f112_mem_of_orderFive hMnorm h5Mα hnot5A hxK ?_
        simpa using hx5
      · have hxK : (⟨x, hxE5⟩ : H') ∈ Kβ := by
          show (⟨x, hxE5⟩ : H') ∈ MulAction.stabilizer H' (baseB X)
          rw [MulAction.mem_stabilizer_iff]
          change x • baseB X = baseB X
          have hxstab : x ∈ MulAction.stabilizer X.Universal (baseB X) := by
            rw [stabilizer_baseB X]; exact hxB
          exact MulAction.mem_stabilizer_iff.mp hxstab
        refine f112_mem_of_orderFive hMnorm h5Mβ hnot5B hxK ?_
        simpa using hx5
    exact ⟨⟨x, hxE5⟩, hxH, rfl⟩
  have hsub : {u | (u ∈ X.ofA.range ∨ u ∈ X.ofB.range) ∧ orderOf u = 5} ⊆
      M.map (f112E5 L1 L2 S).subtype := by
    rintro x ⟨hor, hx5⟩
    exact hgen x (Subgroup.subset_closure ⟨hor, hx5⟩) hor hx5
  have hclos : f112E5 L1 L2 S ≤ M.map (f112E5 L1 L2 S).subtype := by
    change Subgroup.closure {u | (u ∈ X.ofA.range ∨ u ∈ X.ofB.range) ∧ orderOf u = 5} ≤
      M.map (f112E5 L1 L2 S).subtype
    exact (Subgroup.closure_le _).mpr hsub
  rw [eq_top_iff]
  intro m _
  have hmval : (m : X.Universal) ∈ M.map (f112E5 L1 L2 S).subtype := hclos m.2
  obtain ⟨m', hm', hmm'⟩ := Subgroup.mem_map.mp hmval
  have : m' = m := Subtype.ext hmm'
  simpa [this] using hm'

@[expose] def F112LocalL2 (L1 L2 S : Subgroup H) : Prop :=
  ∀ v : Vtx (f112Gold L1 L2 S),
    ∃ N : Subgroup ↥(f112E5 L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S) v 2 N

theorem f112_edgeTransitive {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    EdgeTransitive (f112Gold L1 L2 S).treeGraph (f112E5 L1 L2 S) := by
  obtain ⟨hα, hβ⟩ := f112_locTransBase hF h1 h2
  exact edgeTransitive_of_locTrans (f112Gold L1 L2 S).treeGraph_isTree.connected
    (adj_smul (f112Gold L1 L2 S)) (f112E5 L1 L2 S)
    (adj_baseA_baseB (f112Gold L1 L2 S)) hα hβ

theorem f112_edgeTransitive_top {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    EdgeTransitive (f112Gold L1 L2 S).treeGraph (⊤ : Subgroup ↥(f112E5 L1 L2 S)) := by
  intro u v u' v' huv hu'v'
  obtain ⟨g, hg, hmap⟩ := f112_edgeTransitive hF h1 h2 u v u' v' huv hu'v'
  exact ⟨⟨g, hg⟩, Subgroup.mem_top _, hmap⟩

theorem f112_sup_edgeStab {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    f112E5 L1 L2 S ⊔
        (MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseA (f112Gold L1 L2 S)) ⊓
          MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseB (f112Gold L1 L2 S))) = ⊤ :=
  sup_eq_top_of_edgeTransitive (adj_smul (f112Gold L1 L2 S))
    (f112_preservesParts hF h1 h2) (adj_baseA_baseB (f112Gold L1 L2 S))
    (f112_edgeTransitive hF h1 h2)

theorem f112_edgeStab_le_normalizer_E5 {L1 L2 S : Subgroup H} :
    (MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseA (f112Gold L1 L2 S)) ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal (baseB (f112Gold L1 L2 S))) ≤
      Subgroup.normalizer (f112E5 L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let X := f112Gold L1 L2 S
  let S0 : Set X.Universal := {u | (u ∈ X.ofA.range ∨ u ∈ X.ofB.range) ∧ orderOf u = 5}
  have hconj : ∀ (e : X.Universal), e ∈
      (MulAction.stabilizer X.Universal (baseA X) ⊓
        MulAction.stabilizer X.Universal (baseB X)) →
      ∀ u ∈ S0, e * u * e⁻¹ ∈ S0 := by
    intro e he u hu
    obtain ⟨huA | huB, hu5⟩ := hu
    · have heA : e ∈ X.ofA.range := by
        rw [← stabilizer_baseA X]
        exact (Subgroup.mem_inf.mp he).1
      refine ⟨Or.inl ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := huA
        obtain ⟨b, rfl⟩ := heA
        exact ⟨b * a * b⁻¹, by simp⟩
      · apply orderOf_eq_prime
        · have hu_pow : u ^ 5 = 1 := by rw [← hu5]; exact pow_orderOf_eq_one u
          rw [conj_pow, hu_pow]
          simp
        · intro h1
          have hu1 : u = 1 := by
            have := congrArg (fun x => e⁻¹ * x * e) h1
            simpa [mul_assoc] using this
          rw [hu1] at hu5
          simp at hu5
    · have heB : e ∈ X.ofB.range := by
        rw [← stabilizer_baseB X]
        exact (Subgroup.mem_inf.mp he).2
      refine ⟨Or.inr ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := huB
        obtain ⟨b, rfl⟩ := heB
        exact ⟨b * a * b⁻¹, by simp⟩
      · apply orderOf_eq_prime
        · have hu_pow : u ^ 5 = 1 := by rw [← hu5]; exact pow_orderOf_eq_one u
          rw [conj_pow, hu_pow]
          simp
        · intro h1
          have hu1 : u = 1 := by
            have := congrArg (fun x => e⁻¹ * x * e) h1
            simpa [mul_assoc] using this
          rw [hu1] at hu5
          simp at hu5
  have hmap : ∀ e ∈ (MulAction.stabilizer X.Universal (baseA X) ⊓
        MulAction.stabilizer X.Universal (baseB X)),
      (f112E5 L1 L2 S).map (MulAut.conj e).toMonoidHom ≤ f112E5 L1 L2 S := by
    intro e he
    rw [f112E5, MonoidHom.map_closure]
    exact (Subgroup.closure_le _).mpr (by
      rintro x ⟨u, hu, rfl⟩
      exact Subgroup.subset_closure (hconj e he u hu))
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hmap e he (Subgroup.mem_map_of_mem _ hx)
  · intro hx
    have hx' : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈ f112E5 L1 L2 S :=
      hmap e⁻¹ (Subgroup.inv_mem _ he) (Subgroup.mem_map_of_mem _ hx)
    simpa [mul_assoc] using hx'

theorem f112E5_normal {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    (f112E5 L1 L2 S).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  rw [← f112_sup_edgeStab hF h1 h2]
  refine sup_le Subgroup.le_normalizer ?_
  exact f112_edgeStab_le_normalizer_E5

theorem f112_charTwo_P1_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S) :
    CharTwo (f112P1 L1 L2 S) :=
  F112W.charTwo_beta hR

theorem f112_charTwo_P2_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S) :
    CharTwo (f112P2 L1 L2 S) := by
  have h := F112W.charTwo_beta hR.symm
  simpa [f112P2, bigB_comm] using h

theorem f112_charTwo_top {G : Type*} [Group G] {P : Subgroup G} (h : CharTwo P) :
    CharTwo (⊤ : Subgroup ↥P) :=
  CFSG.Quasithin.F6.charTwo_of_mulEquiv (Subgroup.topEquiv (G := ↥P)).symm h

theorem f112_charTwo_stabilizer_of_hyp111R {L1 L2 S : Subgroup H} (hR : Hyp111R L1 L2 S)
    (v : Vtx (f112Gold L1 L2 S)) :
    CharTwo (MulAction.stabilizer (f112Gold L1 L2 S).Universal v) := by
  have hP2 : CharTwo (f112P2 L1 L2 S) := by
    have h := F112W.charTwo_beta hR.symm
    simpa [f112P2, bigB_comm] using h
  exact charTwo_stabilizer (f112Gold L1 L2 S)
    (f112_charTwo_top (F112W.charTwo_beta hR)) (f112_charTwo_top hP2) v

theorem f112_charTwoStab {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    CharTwoStab (V := Vtx (f112Gold L1 L2 S)) (G := ↥(f112E5 L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  intro v
  let X := f112Gold L1 L2 S
  let Uv : Subgroup X.Universal := MulAction.stabilizer X.Universal v
  let E := f112E5 L1 L2 S
  haveI hUvfin : Finite Uv := finite_stabilizer X v
  have hEn : (E.subgroupOf Uv).Normal := (f112E5_normal hF h1 h2).subgroupOf Uv
  have hEq : E.subgroupOf Uv = (E ⊓ Uv).subgroupOf Uv := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hcharU : CharTwo Uv := f112_charTwo_stabilizer_of_hyp111R hR v
  have hcharSub : CharTwo ((E ⊓ Uv).subgroupOf Uv) := by
    have hHn : ((E ⊓ Uv).subgroupOf Uv).Normal := by rw [← hEq]; exact hEn
    exact CFSG.Quasithin.A4.charTwo_of_normal (H := (E ⊓ Uv).subgroupOf Uv)
      (N := ⊤) le_top (Subgroup.le_normalizer_of_normal) (f112_charTwo_top hcharU)
  have hcharI : CharTwo (E ⊓ Uv) :=
    CFSG.Quasithin.F6.charTwo_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ Uv ≤ Uv)) hcharSub
  have hstab : MulAction.stabilizer ↥E v = (Uv).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E v]
  rw [hstab]
  let e : ↥(E ⊓ Uv) ≃* ↥((Uv).subgroupOf E) :=
  { toFun := fun x => ⟨⟨(x : X.Universal), x.2.1⟩, x.2.2⟩
    invFun := fun x => ⟨(x.1 : X.Universal), ⟨x.1.2, x.2⟩⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun x => by ext; rfl
    map_mul' := fun x y => by ext; rfl }
  exact CFSG.Quasithin.F6.charTwo_of_mulEquiv e hcharI

theorem f112_hyp30_of_localL2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hl2 : F112LocalL2 L1 L2 S) :
    Hyp30 (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S) where
  isTree := (f112Gold L1 L2 S).treeGraph_isTree
  adj_smul := by
    intro g u v
    exact adj_smul (f112Gold L1 L2 S) (g : (f112Gold L1 L2 S).Universal) u v
  faithful := by
    intro g hg
    apply Subtype.ext
    exact f112_faithful hF h1 h2 (g : (f112Gold L1 L2 S).Universal) (fun v => hg v)
  edgeTrans := f112_edgeTransitive_top hF h1 h2
  minimal := f112_minimality hF h1 h2
  finite_stab := by
    intro v
    haveI : Finite ↥(f112P1 L1 L2 S) := Subtype.finite
    haveI : Finite ↥(f112P2 L1 L2 S) := Subtype.finite
    haveI hfin : Finite (MulAction.stabilizer (f112Gold L1 L2 S).Universal v) :=
      finite_stabilizer (f112Gold L1 L2 S) v
    rw [← MulAction.stabilizer_subgroupOf (f112E5 L1 L2 S) v]
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer (f112Gold L1 L2 S).Universal v).subgroupOf
          (f112E5 L1 L2 S)) =>
        (⟨(x.1 : (f112Gold L1 L2 S).Universal), x.2⟩ :
          ↥(MulAction.stabilizer (f112Gold L1 L2 S).Universal v)))
      (by
        intro a b h
        have hU : (a.1.1 : (f112Gold L1 L2 S).Universal) = b.1.1 :=
          congrArg (fun x : ↥(MulAction.stabilizer (f112Gold L1 L2 S).Universal v) =>
            (x : (f112Gold L1 L2 S).Universal)) h
        exact Subtype.ext (Subtype.ext hU))
  valency := fun v => f112_valency hF h1 h2 v
  locL2 := fun v => by
    obtain ⟨N, hN⟩ := hl2 v
    exact ⟨N, by simpa [f112_nOf_eq_two hF h1 h2 v] using hN⟩

end CFSG.Quasithin.F112R.St84
