module

public import CFSG.Quasithin.Recognition.St84.AppTree
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements

import CFSG.Quasithin.Recognition.St84.Gen.OTwoResMul
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Background.F1VertexCore

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise commutatorElement

universe u

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def f112EOdd (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  Subgroup.closure {u | (u ∈ (f112Gold L1 L2 S).ofA.range ∨
      u ∈ (f112Gold L1 L2 S).ofB.range) ∧ Odd (orderOf u)}

@[expose] noncomputable def f112saFive (L : Subgroup H) : Subgroup H :=
  Subgroup.closure {x | x ∈ L ∧ orderOf x = 5}

theorem f112sa_card_oTwoQuot_vs3 {L : Subgroup H} (h : VS3 L) :
    Nat.card (oTwoQuot ↥L) = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F112W.perm3_card]

theorem f112sa_three_dvd_card {L : Subgroup H} (h : VS3 L) : 3 ∣ Nat.card ↥L := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L)
  rw [f112sa_card_oTwoQuot_vs3 h] at hcard
  refine ⟨2 * Nat.card (CFSG.Open.pCore 2 ↥L), ?_⟩
  rw [hcard]
  ring

theorem f112sa_relIndex_left {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).relIndex (f112P1 L1 L2 S) = 3 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have h := (st84HypA_of_hyp111R hR (isL2Quot_of_VS3 h1) h2 (by norm_num) (by omega)
    (by omega)).index_left
  simpa using h

theorem f112sa_relIndex_right {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).relIndex (f112P2 L1 L2 S) = 2 ^ n + 1 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have h := (st84HypA_of_hyp111R hR (isL2Quot_of_VS3 h1) h2 (by norm_num) (by omega)
    (by omega)).index_right
  simpa using h

theorem f112sa_edgeA_index {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112Gold L1 L2 S).edgeA.index = 3 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeA_index]
  exact f112sa_relIndex_left hF h1 hn h2

theorem f112sa_edgeB_index {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112Gold L1 L2 S).edgeB.index = 2 ^ n + 1 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeB_index]
  exact f112sa_relIndex_right hF h1 hn h2

theorem f112sa_ncard_neighborSet_alpha {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (g : (f112Gold L1 L2 S).Universal) :
    ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseA (f112Gold L1 L2 S))).ncard = 3 := by
  rw [smul_baseA (f112Gold L1 L2 S) g]
  change ((f112Gold L1 L2 S).treeGraph.neighborSet
    (Sum.inl ((g : (f112Gold L1 L2 S).Universal) :
      (f112Gold L1 L2 S).Universal ⧸ (f112Gold L1 L2 S).ofA.range))).ncard = 3
  rw [ncard_neighborSet_inl, f112sa_edgeA_index hF h1 hn h2]

theorem f112sa_ncard_neighborSet_beta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (g : (f112Gold L1 L2 S).Universal) :
    ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseB (f112Gold L1 L2 S))).ncard = 2 ^ n + 1 := by
  rw [smul_baseB (f112Gold L1 L2 S) g]
  change ((f112Gold L1 L2 S).treeGraph.neighborSet
    (Sum.inr ((g : (f112Gold L1 L2 S).Universal) :
      (f112Gold L1 L2 S).Universal ⧸ (f112Gold L1 L2 S).ofB.range))).ncard = 2 ^ n + 1
  rw [ncard_neighborSet_inr, f112sa_edgeB_index hF h1 hn h2]

theorem f112sa_nOf_alpha {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (g : (f112Gold L1 L2 S).Universal) :
    nOf (f112Gold L1 L2 S).treeGraph (g • baseA (f112Gold L1 L2 S)) = 1 := by
  unfold nOf
  have hcard : Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseA (f112Gold L1 L2 S))) = 3 := by
    rw [Nat.card_coe_set_eq]
    exact f112sa_ncard_neighborSet_alpha hF h1 hn h2 g
  rw [hcard]
  norm_num

theorem f112sa_nOf_beta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (g : (f112Gold L1 L2 S).Universal) :
    nOf (f112Gold L1 L2 S).treeGraph (g • baseB (f112Gold L1 L2 S)) = n := by
  unfold nOf
  have hcard : Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet
      (g • baseB (f112Gold L1 L2 S))) = 2 ^ n + 1 := by
    rw [Nat.card_coe_set_eq]
    exact f112sa_ncard_neighborSet_beta hF h1 hn h2 g
  rw [hcard]
  have hsub : 2 ^ n + 1 - 1 = 2 ^ n := Nat.add_sub_cancel _ _
  rw [hsub, Nat.log_pow]
  norm_num

theorem f112sa_valency {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (v : Vtx (f112Gold L1 L2 S)) :
    1 ≤ nOf (f112Gold L1 L2 S).treeGraph v ∧
      Nat.card ((f112Gold L1 L2 S).treeGraph.neighborSet v) =
        2 ^ nOf (f112Gold L1 L2 S).treeGraph v + 1 := by
  obtain ⟨g, rfl⟩ | ⟨g, rfl⟩ := exists_smul_base (f112Gold L1 L2 S) v
  · rw [f112sa_nOf_alpha hF h1 hn h2 g, Nat.card_coe_set_eq,
      f112sa_ncard_neighborSet_alpha hF h1 hn h2 g]
    norm_num
  · rw [f112sa_nOf_beta hF h1 hn h2 g, Nat.card_coe_set_eq,
      f112sa_ncard_neighborSet_beta hF h1 hn h2 g]
    omega

theorem f112sa_borelOf_left_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    borelOf L1 S = S ⊓ L1 :=
  CFSG.Quasithin.F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1

theorem f112sa_borelOf_left_isPGroup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    IsPGroup 2 (borelOf L1 S) :=
  (f112sa_borelOf_left_eq hF h1) ▸ hF.1.h1.sylow.2.1

theorem f112sa_bigB_eq_sup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    bigB L1 L2 S = S ⊔ borelOf L2 S := by
  have hB1 : borelOf L1 S = S ⊓ L1 := f112sa_borelOf_left_eq hF h1
  have h : S ⊔ (S ⊓ L1) = S := sup_eq_left.mpr inf_le_left
  unfold bigB
  rw [hB1, sup_comm ((S ⊓ L1) ⊔ borelOf L2 S) S, ← sup_assoc, h]

theorem f112sa_P2_eq_sup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    f112P2 L1 L2 S = L2 ⊔ S := by
  have hB : bigB L1 L2 S = S ⊔ borelOf L2 S := f112sa_bigB_eq_sup hF h1
  show L2 ⊔ bigB L1 L2 S = L2 ⊔ S
  rw [hB, sup_comm S (borelOf L2 S), ← sup_assoc,
    sup_eq_left.mpr (F1.borelOf_le L2 S)]

theorem f112sa_L2_normal_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    (L2.subgroupOf (f112P2 L1 L2 S)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : L2 ≤ _)).mpr ?_
  have hN : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) := by
    have h := bigB_le_normalizer_of_hyp111 hF.1.symm
    rwa [bigB_comm] at h
  exact sup_le Subgroup.le_normalizer hN

theorem f112sa_quot_P2_two {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1)
    [hN : (L2.subgroupOf (f112P2 L1 L2 S)).Normal] :
    IsPGroup 2 (↥(f112P2 L1 L2 S) ⧸ L2.subgroupOf (f112P2 L1 L2 S)) := by
  have hS_le : S ≤ f112P2 L1 L2 S := by
    rw [f112sa_P2_eq_sup hF h1]
    exact le_sup_right
  have hL2_le : L2 ≤ f112P2 L1 L2 S := le_sup_left
  have hsup : (L2.subgroupOf (f112P2 L1 L2 S)) ⊔
      S.subgroupOf (f112P2 L1 L2 S) = ⊤ := by
    have h := Subgroup.subgroupOf_sup hL2_le hS_le
    rw [show L2 ⊔ S = f112P2 L1 L2 S from (f112sa_P2_eq_sup hF h1).symm] at h
    simpa [Subgroup.subgroupOf_self] using h.symm
  have hS2 : IsPGroup 2 (S.subgroupOf (f112P2 L1 L2 S)) :=
    hF.1.h1.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS_le).symm
  let f : ↥(S.subgroupOf (f112P2 L1 L2 S)) →*
      ↥(f112P2 L1 L2 S) ⧸ L2.subgroupOf (f112P2 L1 L2 S) :=
    (QuotientGroup.mk' (L2.subgroupOf (f112P2 L1 L2 S))).comp
      (S.subgroupOf (f112P2 L1 L2 S)).subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (L2.subgroupOf (f112P2 L1 L2 S)) q
    have hb : b ∈ (L2.subgroupOf (f112P2 L1 L2 S)) ⊔
        S.subgroupOf (f112P2 L1 L2 S) := by
      rw [hsup]
      exact Subgroup.mem_top b
    have hb' : b ∈ (((L2.subgroupOf (f112P2 L1 L2 S) : Set ↥(f112P2 L1 L2 S))) *
        ((S.subgroupOf (f112P2 L1 L2 S) : Set ↥(f112P2 L1 L2 S)))) := by
      rw [← Subgroup.normal_mul (L2.subgroupOf (f112P2 L1 L2 S))
        (S.subgroupOf (f112P2 L1 L2 S))]
      exact hb
    obtain ⟨n, hn, s, hs, hns⟩ := hb'
    have hns' : n * s = b := hns
    refine ⟨⟨s, hs⟩, ?_⟩
    have hsval : ((S.subgroupOf (f112P2 L1 L2 S)).subtype ⟨s, hs⟩ :
        ↥(f112P2 L1 L2 S)) = s := rfl
    have hfval : f ⟨s, hs⟩ =
        (QuotientGroup.mk' (L2.subgroupOf (f112P2 L1 L2 S))) s := by
      change (QuotientGroup.mk' (L2.subgroupOf (f112P2 L1 L2 S)))
        ((S.subgroupOf (f112P2 L1 L2 S)).subtype ⟨s, hs⟩) =
          (QuotientGroup.mk' (L2.subgroupOf (f112P2 L1 L2 S))) s
      rw [hsval]
    rw [hfval, ← hns', map_mul]
    have hn1 : (QuotientGroup.mk' (L2.subgroupOf (f112P2 L1 L2 S))) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hn
    rw [hn1, one_mul]
  exact hS2.of_surjective f hf

theorem f112sa_mem_L2_of_odd {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) {x : H}
    (hx : x ∈ f112P2 L1 L2 S) (hodd : Odd (orderOf x)) : x ∈ L2 := by
  haveI : (L2.subgroupOf (f112P2 L1 L2 S)).Normal := f112sa_L2_normal_P2 hF
  have hmem : (⟨x, hx⟩ : ↥(f112P2 L1 L2 S)) ∈ L2.subgroupOf (f112P2 L1 L2 S) :=
    CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_isPGroup_quotient _
      (f112sa_quot_P2_two hF h1) (by rwa [Subgroup.orderOf_mk])
  exact Subgroup.mem_subgroupOf.mp hmem

theorem f112sa_mem_oTwoRes_of_odd {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) {x : H}
    (hx : x ∈ f112P2 L1 L2 S) (hodd : Odd (orderOf x)) : x ∈ oTwoRes L2 := by
  have hxL : x ∈ L2 := f112sa_mem_L2_of_odd hF h1 hx hodd
  exact Subgroup.subset_closure ⟨hxL, orderOf x, hodd, pow_orderOf_eq_one x⟩

theorem f112sa_ncard_neighborSet_baseA {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ((f112Gold L1 L2 S).treeGraph.neighborSet (baseA (f112Gold L1 L2 S))).ncard = 3 := by
  simpa using f112sa_ncard_neighborSet_alpha hF h1 hn h2 (1 : (f112Gold L1 L2 S).Universal)

theorem f112sa_exists_orderThree_L1 {L1 L2 S : Subgroup H} (h1 : VS3 L1) :
    ∃ y ∈ L1, orderOf y = 3 := by
  obtain ⟨y, hy3⟩ := exists_prime_orderOf_dvd_card' 3 (f112sa_three_dvd_card h1)
  refine ⟨(y : H), y.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hy3

theorem f112sa_orderThree_not_fixed_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) (h1 : VS3 L1)
    {y : ↥(f112P1 L1 L2 S)}
    (hyL : (y : H) ∈ L1) (hy3 : orderOf y = 3) {w : Vtx (f112Gold L1 L2 S)}
    (hw : (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) w) :
    (f112Gold L1 L2 S).ofA y • w ≠ w := by
  let X := f112Gold L1 L2 S
  obtain ⟨a, rfl⟩ := (adj_baseA_iff X w).1 hw
  intro hfix
  have hmem : a⁻¹ * y * a ∈ X.edgeA := (ofA_smul_inr_eq_self_iff X y a).1 hfix
  have hedge : X.edgeA =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P1 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_left).range = _
    exact Subgroup.inclusion_range inf_le_left
  have hmemB : ((a⁻¹ * y * a : ↥(f112P1 L1 L2 S)) : H) ∈ bigB L1 L2 S := by
    have h := hmem
    rw [hedge, Subgroup.mem_subgroupOf, f112_inf_eq_bigB_of_hyp111R hR] at h
    exact h
  have hL1norm : (L1.subgroupOf (f112P1 L1 L2 S)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : L1 ≤ _)).mpr ?_
    exact sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).1
  have hconjL1 : ((a⁻¹ * y * a : ↥(f112P1 L1 L2 S)) : H) ∈ L1 := by
    have hy' : (⟨(y : H), Subgroup.mem_sup_left hyL⟩ : ↥(f112P1 L1 L2 S)) ∈
        L1.subgroupOf (f112P1 L1 L2 S) := Subgroup.mem_subgroupOf.mpr hyL
    have h := hL1norm.conj_mem ⟨(y : H), Subgroup.mem_sup_left hyL⟩ hy' a⁻¹
    have heq : a⁻¹ * (⟨(y : H), Subgroup.mem_sup_left hyL⟩ : ↥(f112P1 L1 L2 S)) * (a⁻¹)⁻¹ =
        a⁻¹ * y * a := by simp
    rw [heq] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hmemB1 : ((a⁻¹ * y * a : ↥(f112P1 L1 L2 S)) : H) ∈ borelOf L1 S := by
    rw [← F1.inf_bigB_eq_borelOf hR]
    exact ⟨hconjL1, hmemB⟩
  have hord : orderOf ((a⁻¹ * y * a : ↥(f112P1 L1 L2 S)) : H) = 3 := by
    have hconj : orderOf (a⁻¹ * y * a) = orderOf y := by
      have h := orderOf_injective (MulAut.conj a⁻¹).toMonoidHom
        (MulAut.conj a⁻¹).injective y
      simpa [MulAut.conj_apply] using h
    rw [Subgroup.orderOf_coe, hconj, hy3]
  have h3dvd : 3 ∣ Nat.card ↥(borelOf L1 S) := by
    have h := orderOf_dvd_natCard
      (⟨((a⁻¹ * y * a : ↥(f112P1 L1 L2 S)) : H), hmemB1⟩ : ↥(borelOf L1 S))
    rw [Subgroup.orderOf_mk, hord] at h
    exact h
  obtain ⟨n, hn⟩ := (f112sa_borelOf_left_isPGroup hF h1).exists_card_eq
  rw [hn] at h3dvd
  have h23 : 3 ∣ 2 ^ n := h3dvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h23
  norm_num at this

theorem f112sa_transitive_of_prime_order {p : ℕ} [hp : Fact p.Prime]
    {L1 L2 S : Subgroup H} {E : Subgroup (f112Gold L1 L2 S).Universal}
    {v : Vtx (f112Gold L1 L2 S)} {x : (f112Gold L1 L2 S).Universal}
    (hxE : x ∈ E) (hxfix : x • v = v) (hx : orderOf x = p)
    (hnotfix : ∀ w, (f112Gold L1 L2 S).treeGraph.Adj v w → x • w ≠ w)
    (hcard : ((f112Gold L1 L2 S).treeGraph.neighborSet v).ncard = p) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj v a →
      (f112Gold L1 L2 S).treeGraph.Adj v b →
      ∃ g ∈ E ⊓ MulAction.stabilizer (f112Gold L1 L2 S).Universal v, g • a = b := by
  let X := f112Gold L1 L2 S
  have hfin : (X.treeGraph.neighborSet v).Finite := by
    refine Set.finite_of_ncard_ne_zero ?_
    rw [hcard]
    exact hp.out.pos.ne'
  haveI : Finite (X.treeGraph.neighborSet v) := hfin.to_subtype
  haveI : Fintype (X.treeGraph.neighborSet v) := Fintype.ofFinite _
  let e : Equiv.Perm (X.treeGraph.neighborSet v) :=
  { toFun := fun w => ⟨x • w.1, by
        have h := (adj_smul X x v w.1).2 w.2
        simpa [hxfix] using h⟩
    invFun := fun w => ⟨x⁻¹ • w.1, by
        have hxinv : x⁻¹ • v = v := by
          calc x⁻¹ • v = x⁻¹ • (x • v) := by rw [hxfix]
            _ = v := by simp
        have h := (adj_smul X x⁻¹ v w.1).2 w.2
        simpa [hxinv] using h⟩
    left_inv := fun w => by ext; simp
    right_inv := fun w => by ext; simp }
  have hpow_all : ∀ (n : ℕ) (w : X.treeGraph.neighborSet v),
      ((e ^ n) w).1 = x ^ n • w.1 := by
    intro n w
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change (x • ((e ^ n) w).1) = x ^ (n + 1) • w.1
      rw [ih, ← mul_smul, ← pow_succ']
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have he_p : e ^ p = 1 := by
    ext w
    rw [hpow_all p w, hxp]
    simp
  have hpos : 0 < (X.treeGraph.neighborSet v).ncard := by
    rw [hcard]
    exact hp.out.pos
  obtain ⟨w0, hw0⟩ := (Set.ncard_pos (s := X.treeGraph.neighborSet v) hfin).mp hpos
  have he1 : e ≠ 1 := by
    intro he
    have hfixw : e ⟨w0, hw0⟩ = ⟨w0, hw0⟩ := by rw [he]; rfl
    exact hnotfix w0 hw0 (congrArg Subtype.val hfixw)
  have hord : orderOf e = p := orderOf_eq_prime he_p he1
  have hcardN : Fintype.card (X.treeGraph.neighborSet v) = p := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcard]
  have hcycle : e.IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order' (by rw [hord]; exact hp.out) ?_
    rw [hcardN, hord]
    have := hp.out.two_le
    omega
  intro a b ha hb
  let A : X.treeGraph.neighborSet v := ⟨a, ha⟩
  let B : X.treeGraph.neighborSet v := ⟨b, hb⟩
  have hAfix : e A ≠ A := by
    intro h
    exact hnotfix a ha (congrArg Subtype.val h)
  have hBfix : e B ≠ B := by
    intro h
    exact hnotfix b hb (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := hcycle.exists_pow_eq hAfix hBfix
  refine ⟨x ^ k, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨E.pow_mem hxE k, ?_⟩
    exact Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr hxfix) k
  · have hkb : x ^ k • a = b := by
      have := congrArg Subtype.val hk
      rwa [hpow_all k A] at this
    exact hkb

theorem f112sa_transitive_alpha {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112EOdd L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseA (f112Gold L1 L2 S)), g • a = b := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  obtain ⟨y, hyL, hy3⟩ := f112sa_exists_orderThree_L1 (L2 := L2) (S := S) h1
  let y' : ↥(f112P1 L1 L2 S) := ⟨y, Subgroup.mem_sup_left hyL⟩
  have hy'3 : orderOf y' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hy3
  have hxE : (f112Gold L1 L2 S).ofA y' ∈ f112EOdd L1 L2 S := by
    refine Subgroup.subset_closure ⟨Or.inl ⟨y', rfl⟩, ?_⟩
    rw [orderOf_injective (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective y', hy'3]
    norm_num
  have hxfix : (f112Gold L1 L2 S).ofA y' • baseA (f112Gold L1 L2 S) =
      baseA (f112Gold L1 L2 S) :=
    MulAction.mem_stabilizer_iff.mp (by
      rw [stabilizer_baseA (f112Gold L1 L2 S)]
      exact ⟨y', rfl⟩)
  exact f112sa_transitive_of_prime_order (p := 3) hxE hxfix
    (by rw [orderOf_injective (f112Gold L1 L2 S).ofA
      (f112Gold L1 L2 S).ofA_injective y', hy'3])
    (fun w hw => f112sa_orderThree_not_fixed_of_hyp111R hF hR h1 hyL hy'3 hw)
    (f112sa_ncard_neighborSet_baseA hF h1 hn h2)

private theorem f112sa_ofB_mem_EOdd {L1 L2 S : Subgroup H} {z : H}
    (hz : z ∈ oTwoRes L2) (hzP : z ∈ f112P2 L1 L2 S) :
    (f112Gold L1 L2 S).ofB ⟨z, hzP⟩ ∈ f112EOdd L1 L2 S := by
  revert hzP
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
      intro hwP
      have hwodd : Odd (orderOf w) :=
        hw.2.choose_spec.1.of_dvd_nat (orderOf_dvd_of_pow_eq_one hw.2.choose_spec.2)
      refine Subgroup.subset_closure ⟨Or.inr ⟨⟨w, hwP⟩, rfl⟩, ?_⟩
      rw [orderOf_injective (f112Gold L1 L2 S).ofB
        (f112Gold L1 L2 S).ofB_injective, Subgroup.orderOf_mk]
      exact hwodd
  | one =>
      intro hzP
      have h1 : (⟨1, hzP⟩ : ↥(f112P2 L1 L2 S)) = 1 := Subtype.ext rfl
      rw [h1, map_one]
      exact Subgroup.one_mem (f112EOdd L1 L2 S)
  | mul a b ha hb iha ihb =>
      intro habP
      have haP : a ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left (oTwoRes_le L2 ha)
      have hbP : b ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left (oTwoRes_le L2 hb)
      have heq : (⟨a * b, habP⟩ : ↥(f112P2 L1 L2 S)) =
          ⟨a, haP⟩ * ⟨b, hbP⟩ := Subtype.ext rfl
      rw [heq, map_mul]
      exact Subgroup.mul_mem (f112EOdd L1 L2 S) (iha haP) (ihb hbP)
  | inv a ha iha =>
      intro haP
      have haP' : a ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left (oTwoRes_le L2 ha)
      have heq : (⟨a⁻¹, haP⟩ : ↥(f112P2 L1 L2 S)) =
          (⟨a, haP'⟩ : ↥(f112P2 L1 L2 S))⁻¹ := Subtype.ext rfl
      rw [heq, map_inv]
      exact Subgroup.inv_mem (f112EOdd L1 L2 S) (iha haP')

theorem f112sa_transitive_beta {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112EOdd L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseB (f112Gold L1 L2 S)), g • a = b := by
  intro a b ha hb
  let X := f112Gold L1 L2 S
  obtain ⟨p, rfl⟩ := (adj_baseB_iff X a).1 ha
  obtain ⟨p', rfl⟩ := (adj_baseB_iff X b).1 hb
  have hB1 : borelOf L1 S = S ⊓ L1 :=
    CFSG.Quasithin.F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1
  have hS_normO2 : S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub s (oTwoRes L2) = oTwoRes L2
    rw [conjSub_oTwoRes]
    have hsL : conjSub s L2 = L2 := by
      simpa [conjSub] using
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hF.1.h2.normalizes hs)
    rw [hsL]
  have hB_normO2 : bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    sup_le (sup_le ((hB1.le.trans inf_le_left).trans hS_normO2)
      ((F1.borelOf_le L2 S).trans (le_normalizer_oTwoRes L2))) hS_normO2
  have hP2_normO2 : f112P2 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    sup_le (le_normalizer_oTwoRes L2) hB_normO2
  have hQleB : pCoreOf 2 L2 ≤ bigB L1 L2 S := by
    have h1 : pCoreOf 2 L2 ≤ borelOf L2 S :=
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow).trans
        (F1.sylow_le_borelOf L2 S)
    have h2 : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S := le_sup_right
    have h3 : borelOf L1 S ⊔ borelOf L2 S ≤ bigB L1 L2 S := by
      change borelOf L1 S ⊔ borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S
      exact le_sup_left
    exact h1.trans (h2.trans h3)
  have hL2_le : L2 ≤ oTwoRes L2 ⊔ bigB L1 L2 S := by
    calc L2 = oTwoRes L2 ⊔ pCoreOf 2 L2 := (f112sl_oTwoRes_sup_pCoreOf hn h2).symm
      _ ≤ oTwoRes L2 ⊔ bigB L1 L2 S := sup_le le_sup_left (hQleB.trans le_sup_right)
  have hP2_le : f112P2 L1 L2 S ≤ oTwoRes L2 ⊔ bigB L1 L2 S := by
    change L2 ⊔ bigB L1 L2 S ≤ oTwoRes L2 ⊔ bigB L1 L2 S
    exact sup_le hL2_le le_sup_right
  have hpP2 : (p : H) ∈ f112P2 L1 L2 S := p.2
  have hp'P2 : (p' : H) ∈ f112P2 L1 L2 S := p'.2
  have hmemP2 : (p : H)⁻¹ * (p' : H) ∈ f112P2 L1 L2 S :=
    (f112P2 L1 L2 S).mul_mem ((f112P2 L1 L2 S).inv_mem hpP2) hp'P2
  have hmemO2B : (p : H)⁻¹ * (p' : H) ∈ oTwoRes L2 ⊔ bigB L1 L2 S := hP2_le hmemP2
  have hcoe : (↑(oTwoRes L2 ⊔ bigB L1 L2 S) : Set H) =
      (oTwoRes L2 : Set H) * (bigB L1 L2 S : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (N := oTwoRes L2)
      (H := bigB L1 L2 S) hB_normO2
  have hmemProd : (p : H)⁻¹ * (p' : H) ∈
      (oTwoRes L2 : Set H) * (bigB L1 L2 S : Set H) := by
    rw [← hcoe]; exact hmemO2B
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hmemProd
  have hmb' : m' * b₀ = (p : H)⁻¹ * (p' : H) := hmb
  let mH : H := (p : H) * m' * (p : H)⁻¹
  have hmO2 : mH ∈ oTwoRes L2 := by
    dsimp [mH]
    exact (Subgroup.mem_normalizer_iff.mp (hP2_normO2 hpP2) m').mp hm'
  have hmP2 : mH ∈ f112P2 L1 L2 S := by
    dsimp [mH]
    exact (f112P2 L1 L2 S).mul_mem
      ((f112P2 L1 L2 S).mul_mem hpP2 (Subgroup.mem_sup_left ((oTwoRes_le L2) hm')))
      ((f112P2 L1 L2 S).inv_mem hpP2)
  have hp'_eq : (p' : H) = mH * (p : H) * b₀ := by
    dsimp [mH]
    calc (p' : H) = (p : H) * ((p : H)⁻¹ * (p' : H)) := by group
      _ = (p : H) * (m' * b₀) := by rw [hmb']
      _ = ((p : H) * m' * (p : H)⁻¹) * (p : H) * b₀ := by group
  have hb₀P1 : b₀ ∈ f112P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hb₀
  have hb₀P2 : b₀ ∈ f112P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) hb₀
  have hXedgeB : X.edgeB =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_right).range = _
    exact Subgroup.inclusion_range inf_le_right
  have hb₀edge : (⟨b₀, hb₀P2⟩ : ↥(f112P2 L1 L2 S)) ∈ X.edgeB := by
    rw [hXedgeB]
    exact Subgroup.mem_subgroupOf.mpr ⟨hb₀P1, hb₀P2⟩
  have hb₀A : X.ofB ⟨b₀, hb₀P2⟩ ∈ X.ofA.range :=
    (ofB_mem_ofA_range_iff X ⟨b₀, hb₀P2⟩).2 hb₀edge
  have hmp_eq : p' = ⟨mH, hmP2⟩ * p * ⟨b₀, hb₀P2⟩ := by
    apply Subtype.ext
    show (p' : H) = mH * (p : H) * b₀
    exact hp'_eq
  have hcoset : (Sum.inl ((X.ofB (⟨mH, hmP2⟩ * p) : X.Universal) :
        X.Universal ⧸ X.ofA.range) : Vtx X) =
      Sum.inl ((X.ofB p' : X.Universal) : X.Universal ⧸ X.ofA.range) := by
    rw [Sum.inl.injEq, QuotientGroup.eq]
    have h : (X.ofB (⟨mH, hmP2⟩ * p))⁻¹ * X.ofB p' = X.ofB ⟨b₀, hb₀P2⟩ := by
      rw [hmp_eq, map_mul, map_mul, map_mul]
      group
    rw [h]
    exact hb₀A
  refine ⟨X.ofB ⟨mH, hmP2⟩, ⟨?_, ?_⟩, ?_⟩
  · exact f112sa_ofB_mem_EOdd hmO2 hmP2
  · rw [stabilizer_baseB X]
    exact ⟨⟨mH, hmP2⟩, rfl⟩
  · rw [ofB_smul_inl X ⟨mH, hmP2⟩ p]
    exact hcoset

theorem f112sa_locTransBase {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112EOdd L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseA (f112Gold L1 L2 S)), g • a = b) ∧
    (∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112EOdd L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseB (f112Gold L1 L2 S)), g • a = b) :=
  ⟨f112sa_transitive_alpha hF h1 hn h2, f112sa_transitive_beta hF h1 hn h2⟩

theorem f112sa_preservesParts (L1 L2 S : Subgroup H) :
    PreservesParts (f112Gold L1 L2 S).treeGraph (f112Gold L1 L2 S).Universal := by
  let X := f112Gold L1 L2 S
  let P := f112PartsSubgroup X.treeGraph_isTree (adj_smul X)
  have hA : X.ofA.range ≤ P := by
    intro u hu
    exact f112_stabilizer_le_parts _ _ (baseA X) (by simpa [stabilizer_baseA] using hu)
  have hB : X.ofB.range ≤ P := by
    intro u hu
    exact f112_stabilizer_le_parts _ _ (baseB X) (by simpa [stabilizer_baseB] using hu)
  have htop : P = ⊤ := by
    rw [eq_top_iff, ← X.ofA_range_sup_ofB_range]
    exact sup_le hA hB
  intro g v
  have hg : g ∈ P := by rw [htop]; trivial
  rw [mem_f112PartsSubgroup] at hg
  exact hg v

theorem f112sa_preservesParts_E (L1 L2 S : Subgroup H) :
    PreservesParts (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) := by
  let X := f112Gold L1 L2 S
  let P := f112PartsSubgroup X.treeGraph_isTree (adj_smul X)
  have hgen : f112EOdd L1 L2 S ≤ P := by
    refine (Subgroup.closure_le P).mpr ?_
    rintro u ⟨hu | hu, -⟩
    · exact f112_stabilizer_le_parts _ _ (baseA X) (by simpa [stabilizer_baseA] using hu)
    · exact f112_stabilizer_le_parts _ _ (baseB X) (by simpa [stabilizer_baseB] using hu)
  intro g v
  have hg : ((g : (f112Gold L1 L2 S).Universal)) ∈ P := hgen g.2
  rw [mem_f112PartsSubgroup] at hg
  exact hg v

theorem f112sa_edgeTransitive {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    EdgeTransitive (f112Gold L1 L2 S).treeGraph (f112EOdd L1 L2 S) := by
  obtain ⟨hα, hβ⟩ := f112sa_locTransBase hF h1 hn h2
  exact edgeTransitive_of_locTrans (f112Gold L1 L2 S).treeGraph_isTree.connected
    (adj_smul (f112Gold L1 L2 S)) (f112EOdd L1 L2 S)
    (adj_baseA_baseB (f112Gold L1 L2 S)) hα hβ

theorem f112sa_edgeTransitive_top {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    EdgeTransitive (f112Gold L1 L2 S).treeGraph (⊤ : Subgroup ↥(f112EOdd L1 L2 S)) := by
  intro u v u' v' huv hu'v'
  obtain ⟨g, hg, hmap⟩ := f112sa_edgeTransitive hF h1 hn h2 u v u' v' huv hu'v'
  exact ⟨⟨g, hg⟩, Subgroup.mem_top _, hmap⟩

theorem f112sa_sup_edgeStab {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112EOdd L1 L2 S ⊔
        (MulAction.stabilizer (f112Gold L1 L2 S).Universal
            (baseA (f112Gold L1 L2 S)) ⊓
          MulAction.stabilizer (f112Gold L1 L2 S).Universal
            (baseB (f112Gold L1 L2 S))) = ⊤ :=
  sup_eq_top_of_edgeTransitive (adj_smul (f112Gold L1 L2 S))
    (f112sa_preservesParts L1 L2 S) (adj_baseA_baseB (f112Gold L1 L2 S))
    (f112sa_edgeTransitive hF h1 hn h2)

theorem f112sa_edgeStab_le_normalizer (L1 L2 S : Subgroup H) :
    (MulAction.stabilizer (f112Gold L1 L2 S).Universal
        (baseA (f112Gold L1 L2 S)) ⊓
      MulAction.stabilizer (f112Gold L1 L2 S).Universal
        (baseB (f112Gold L1 L2 S))) ≤
    Subgroup.normalizer (f112EOdd L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  let X := f112Gold L1 L2 S
  let S0 : Set X.Universal :=
    {u | (u ∈ X.ofA.range ∨ u ∈ X.ofB.range) ∧ Odd (orderOf u)}
  have hconj : ∀ (e : X.Universal), e ∈
      (MulAction.stabilizer X.Universal (baseA X) ⊓
        MulAction.stabilizer X.Universal (baseB X)) →
      ∀ u ∈ S0, e * u * e⁻¹ ∈ S0 := by
    intro e he u hu
    obtain ⟨huA | huB, huodd⟩ := hu
    · have heA : e ∈ X.ofA.range := by
        rw [← stabilizer_baseA X]
        exact (Subgroup.mem_inf.mp he).1
      obtain ⟨a, rfl⟩ := huA
      obtain ⟨b, rfl⟩ := heA
      refine ⟨Or.inl ⟨b * a * b⁻¹, by simp⟩, ?_⟩
      have h := orderOf_injective (MulAut.conj (X.ofA b)).toMonoidHom
        (MulAut.conj (X.ofA b)).injective (X.ofA a)
      simpa [MulAut.conj_apply] using h ▸ huodd
    · have heB : e ∈ X.ofB.range := by
        rw [← stabilizer_baseB X]
        exact (Subgroup.mem_inf.mp he).2
      obtain ⟨a, rfl⟩ := huB
      obtain ⟨b, rfl⟩ := heB
      refine ⟨Or.inr ⟨b * a * b⁻¹, by simp⟩, ?_⟩
      have h := orderOf_injective (MulAut.conj (X.ofB b)).toMonoidHom
        (MulAut.conj (X.ofB b)).injective (X.ofB a)
      simpa [MulAut.conj_apply] using h ▸ huodd
  have hmap : ∀ e ∈ (MulAction.stabilizer X.Universal (baseA X) ⊓
        MulAction.stabilizer X.Universal (baseB X)),
      (f112EOdd L1 L2 S).map (MulAut.conj e).toMonoidHom ≤ f112EOdd L1 L2 S := by
    intro e he
    rw [f112EOdd, MonoidHom.map_closure]
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
    have hx' : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈ f112EOdd L1 L2 S :=
      hmap e⁻¹ (Subgroup.inv_mem _ he) (Subgroup.mem_map_of_mem _ hx)
    simpa [mul_assoc] using hx'

theorem f112sa_EOdd_normal {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112EOdd L1 L2 S).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  rw [← f112sa_sup_edgeStab hF h1 hn h2]
  exact sup_le Subgroup.le_normalizer (f112sa_edgeStab_le_normalizer L1 L2 S)

theorem f112saFive_le (L : Subgroup H) : f112saFive L ≤ L :=
  (Subgroup.closure_le L).mpr fun _ hx => hx.1

theorem f112saFive_subgroupOf_normal (L : Subgroup H) :
    ((f112saFive L).subgroupOf L).Normal := by
  have hconj : ∀ g ∈ L, ∀ y ∈ f112saFive L, g * y * g⁻¹ ∈ f112saFive L := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        refine Subgroup.subset_closure ⟨L.mul_mem (L.mul_mem hg hz.1) (L.inv_mem hg), ?_⟩
        have h : orderOf (g * z * g⁻¹) = orderOf z := by
          have hh := orderOf_injective (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective z
          simpa [MulAut.conj_apply] using hh
        rw [h, hz.2]
    | one => simpa using Subgroup.one_mem (f112saFive L)
    | mul a b _ _ iha ihb => simpa [mul_assoc] using Subgroup.mul_mem _ iha ihb
    | inv a _ iha => simpa [mul_assoc] using Subgroup.inv_mem _ iha
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact hconj (g : H) g.2 (x : H) hx

theorem f112saFive_sup_pCore {L : Subgroup H} (h : VA5 L) :
    f112saFive L ⊔ pCoreOf 2 L = L := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine le_antisymm (sup_le (f112saFive_le L) (pCoreOf_le 2 L)) ?_
  have hQsimple : IsSimpleGroup (oTwoQuot ↥L) := by
    obtain ⟨e⟩ := h
    have hcard : 4 ≤ Nat.card (GaloisField 2 2) := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    haveI : IsSimpleGroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
    exact e.isSimpleGroup
  have h5L : 5 ∣ Nat.card ↥L := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L)
    rw [f112_card_oTwoQuot h] at hcard
    refine ⟨12 * Nat.card (CFSG.Open.pCore 2 ↥L), ?_⟩
    rw [hcard]
    ring
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 h5L
  have hx_notin : (x : H) ∉ pCoreOf 2 L := by
    intro hxP
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
    have hxord : orderOf (⟨(x : H), hxP⟩ : ↥(pCoreOf 2 L)) = 5 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      exact hx5
    have hdvd : 5 ∣ Nat.card ↥(pCoreOf 2 L) := by
      have h := orderOf_dvd_natCard (⟨(x : H), hxP⟩ : ↥(pCoreOf 2 L))
      rw [hxord] at h
      exact h
    rw [hn] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    norm_num at this
  let A : Subgroup ↥L := (f112saFive L).subgroupOf L
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)
  have hAn : A.Normal := f112saFive_subgroupOf_normal L
  have hnorm : (A.map π).Normal := hAn.map π (QuotientGroup.mk'_surjective _)
  have hxK5 : (x : H) ∈ f112saFive L :=
    Subgroup.subset_closure ⟨x.2, by rw [Subgroup.orderOf_coe]; exact hx5⟩
  have hxA : x ∈ A := Subgroup.mem_subgroupOf.mpr hxK5
  have hπx_ne : π x ≠ 1 := by
    intro hh
    exact hx_notin ((F1.mem_pCore_iff_coe x).mp ((QuotientGroup.eq_one_iff x).mp hh))
  have himg_top : A.map π = ⊤ := by
    haveI : (A.map π).Normal := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map π) with hbot | htop
    · exfalso
      have hmem : π x ∈ A.map π := Subgroup.mem_map_of_mem π hxA
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hπx_ne hmem
    · exact htop
  intro l hl
  let l' : ↥L := ⟨l, hl⟩
  have hlq : π l' ∈ A.map π := by rw [himg_top]; exact Subgroup.mem_top _
  obtain ⟨a, haA, haeq⟩ := Subgroup.mem_map.mp hlq
  have hafive : (a : H) ∈ f112saFive L := Subgroup.mem_subgroupOf.mp haA
  have hker : ((a⁻¹ * l' : ↥L) : H) ∈ pCoreOf 2 L := by
    have h1 : π (a⁻¹ * l') = 1 := by
      rw [map_mul, map_inv, haeq, inv_mul_cancel]
    exact (F1.mem_pCore_iff_coe (a⁻¹ * l')).mp
      ((QuotientGroup.eq_one_iff (a⁻¹ * l')).mp h1)
  have hl_eq : l' = a * (a⁻¹ * l') := by group
  have hval : (l' : H) = (a : H) * ((a⁻¹ * l' : ↥L) : H) := by
    have h := congrArg (fun z : ↥L => (z : H)) hl_eq
    simpa using h
  change (l' : H) ∈ f112saFive L ⊔ pCoreOf 2 L
  rw [hval]
  exact Subgroup.mul_mem_sup hafive hker

theorem f112sa_mem_five_of_odd {L : Subgroup H} (h : VA5 L)
    {x : H} (hxL : x ∈ L) (hodd : Odd (orderOf x)) : x ∈ f112saFive L := by
  let A : Subgroup ↥L := (f112saFive L).subgroupOf L
  let B : Subgroup ↥L := (pCoreOf 2 L).subgroupOf L
  have hAn : A.Normal := f112saFive_subgroupOf_normal L
  haveI : A.Normal := hAn
  have hB2 : IsPGroup 2 B :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 L)).symm
  have hsup : A ⊔ B = ⊤ := by
    rw [show A ⊔ B = (f112saFive L ⊔ pCoreOf 2 L).subgroupOf L from
      (Subgroup.subgroupOf_sup (f112saFive_le L) (pCoreOf_le 2 L)).symm]
    rw [f112saFive_sup_pCore h, Subgroup.subgroupOf_self]
  let f : ↥B →* ↥L ⧸ A := (QuotientGroup.mk' A).comp B.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective A q
    have hl : l ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top l
    have hl' : l ∈ ((A : Set ↥L) * (B : Set ↥L)) := by
      rw [← Subgroup.normal_mul A B]
      exact hl
    obtain ⟨a, ha, b, hb, hab⟩ := hl'
    have hab' : a * b = l := hab
    refine ⟨⟨b, hb⟩, ?_⟩
    have hfval : f ⟨b, hb⟩ = (QuotientGroup.mk' A) b := rfl
    rw [hfval, ← hab', map_mul]
    have ha1 : (QuotientGroup.mk' A) a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [ha1, one_mul]
  have hquot : IsPGroup 2 (↥L ⧸ A) := hB2.of_surjective f hf
  have hmem : (⟨x, hxL⟩ : ↥L) ∈ A :=
    CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_isPGroup_quotient A hquot
      (by rwa [Subgroup.orderOf_mk])
  exact Subgroup.mem_subgroupOf.mp hmem

theorem f112sa_oTwoRes_le_five {L : Subgroup H} (h : VA5 L) :
    oTwoRes L ≤ f112saFive L := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxL, m, hm, hxm⟩
  refine f112sa_mem_five_of_odd h hxL ?_
  exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxm)

theorem f112sa_card_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    5 * Nat.card ↥(bigB L1 L2 S) = Nat.card ↥(f112P2 L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := 2) (by norm_num) (by norm_num) hF.1
      (isL2Quot_of_VS3 h1) h2
  have h := Subgroup.relIndex_mul_card (bigB L1 L2 S) (f112P2 L1 L2 S)
  rw [inf_eq_left.mpr le_sup_right,
    show (bigB L1 L2 S).relIndex (f112P2 L1 L2 S) = 5 from by
      rw [← f112_inf_eq_bigB_of_hyp111R hR]
      exact f112sa_relIndex_right hF h1 le_rfl h2] at h
  exact h

theorem f112sa_oTwoRes_le_of_le_mul {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {M₀ : Subgroup H} (hM : M₀ ≤ f112P2 L1 L2 S)
    (hnorm : oTwoRes L2 ≤ Subgroup.normalizer (M₀ : Set H))
    (hmul : ∀ x ∈ oTwoRes L2, ∃ m ∈ M₀, ∃ b ∈ bigB L1 L2 S, x = m * b) :
    oTwoRes L2 ≤ M₀ :=
  f112_oTwoRes_le_of_le_mul
    (hyp111R_of_isL2Quot le_rfl (by omega) hF.1 (isL2Quot_of_VS3 h1) h2)
    hn h2 hM hnorm hmul

private theorem f112sa_minimality_beta_of_hyp111R
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S)
    (h1 : VS3 L1) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {M : Subgroup ↥(f112EOdd L1 L2 S)} (hMnorm : M.Normal)
    (hMtrans : EdgeTransitive (f112Gold L1 L2 S).treeGraph M)
    {x : ↥(f112EOdd L1 L2 S)}
    (hxK : x ∈ MulAction.stabilizer ↥(f112EOdd L1 L2 S)
      (baseB (f112Gold L1 L2 S)))
    (hxodd : Odd (orderOf x)) : x ∈ M := by
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Kβ : Subgroup ↥E := MulAction.stabilizer ↥E (baseB X)
  let Mβ : Subgroup ↥E := M ⊓ Kβ
  have hKβdef : Kβ = (MulAction.stabilizer X.Universal (baseB X)).subgroupOf E := by
    change MulAction.stabilizer ↥E (baseB X) = _
    rw [← MulAction.stabilizer_subgroupOf]
  haveI hKβfin : Finite ↥Kβ := by
    rw [hKβdef]
    haveI : Finite (MulAction.stabilizer X.Universal (baseB X)) :=
      finite_stabilizer X (baseB X)
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer X.Universal (baseB X)).subgroupOf E) =>
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
      have heven := f112sa_preservesParts_E (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseB X)
      rw [hdist] at heven
      norm_num at heven
  let Mβ' : Subgroup X.Universal := Mβ.map E.subtype
  let M₀' : Subgroup ↥(f112P2 L1 L2 S) := Mβ'.comap X.ofB
  let M₀ : Subgroup H := M₀'.map (f112P2 L1 L2 S).subtype
  have hM₀_le : M₀ ≤ f112P2 L1 L2 S := Subgroup.map_subtype_le _
  have hXedgeB : X.edgeB =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) := by
    change (Subgroup.inclusion inf_le_right).range = _
    exact Subgroup.inclusion_range inf_le_right
  have hMβ'_norm : ∀ g ∈ Kβ, ∀ u ∈ Mβ',
      (g : X.Universal) * u * (g : X.Universal)⁻¹ ∈ Mβ' := by
    intro g hg u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
    have hconjM : g * m * g⁻¹ ∈ M := hMnorm.conj_mem m hm.1 g
    have hconjK : g * m * g⁻¹ ∈ Kβ :=
      Kβ.mul_mem (Kβ.mul_mem hg hm.2) (Kβ.inv_mem hg)
    exact Subgroup.mem_map_of_mem E.subtype (Subgroup.mem_inf.mpr ⟨hconjM, hconjK⟩)
  have hconj_gen : ∀ y ∈ oTwoRes L2, ∀ m ∈ M₀, y * m * y⁻¹ ∈ M₀ := by
    intro y hy m hm
    have hyP2 : y ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) hy)
    have hyE : X.ofB ⟨y, hyP2⟩ ∈ E := f112sa_ofB_mem_EOdd hy hyP2
    have hyKβ : (⟨X.ofB ⟨y, hyP2⟩, hyE⟩ : ↥E) ∈ Kβ := by
      change (⟨X.ofB ⟨y, hyP2⟩, hyE⟩ : ↥E) ∈ MulAction.stabilizer ↥E (baseB X)
      rw [MulAction.mem_stabilizer_iff]
      show ((⟨X.ofB ⟨y, hyP2⟩, hyE⟩ : ↥E) : X.Universal) • baseB X = baseB X
      exact MulAction.mem_stabilizer_iff.mp (by
        rw [stabilizer_baseB X]
        exact ⟨⟨y, hyP2⟩, rfl⟩)
    obtain ⟨q, hqM₀', hqm⟩ := Subgroup.mem_map.mp hm
    have hqMβ' : X.ofB q ∈ Mβ' := Subgroup.mem_comap.mp hqM₀'
    have hconj' : X.ofB (⟨y, hyP2⟩ * q * ⟨y, hyP2⟩⁻¹) ∈ Mβ' := by
      have h := hMβ'_norm ⟨X.ofB ⟨y, hyP2⟩, hyE⟩ hyKβ (X.ofB q) hqMβ'
      have h' : X.ofB ⟨y, hyP2⟩ * X.ofB q * (X.ofB ⟨y, hyP2⟩)⁻¹ ∈ Mβ' := h
      rw [← map_inv, ← map_mul, ← map_mul] at h'
      exact h'
    have hq' : (⟨y, hyP2⟩ * q * ⟨y, hyP2⟩⁻¹) ∈ M₀' := Subgroup.mem_comap.mpr hconj'
    have hfin : ((⟨y, hyP2⟩ * q * ⟨y, hyP2⟩⁻¹ : ↥(f112P2 L1 L2 S)) : H) ∈ M₀ :=
      Subgroup.mem_map_of_mem _ hq'
    rw [← hqm]
    exact hfin
  have hO2_norm_M₀ : oTwoRes L2 ≤ Subgroup.normalizer (M₀ : Set H) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact hconj_gen y hy m
    · intro hm
      have h := hconj_gen y⁻¹ ((oTwoRes L2).inv_mem hy) (y * m * y⁻¹) hm
      simpa [mul_assoc] using h
  have hmul_M₀ : ∀ x ∈ oTwoRes L2, ∃ m ∈ M₀, ∃ b ∈ bigB L1 L2 S, x = m * b := by
    intro x hx
    have hxP2 : x ∈ f112P2 L1 L2 S := Subgroup.mem_sup_left ((oTwoRes_le L2) hx)
    have hbaseA_adj : X.treeGraph.Adj (baseB X) (baseA X) := (adj_baseA_baseB X).symm
    have hxfixβ : X.ofB ⟨x, hxP2⟩ • baseB X = baseB X :=
      MulAction.mem_stabilizer_iff.mp (by
        rw [stabilizer_baseB X]
        exact ⟨⟨x, hxP2⟩, rfl⟩)
    have hxadj : X.treeGraph.Adj (baseB X) (X.ofB ⟨x, hxP2⟩ • baseA X) := by
      have h := (adj_smul X (X.ofB ⟨x, hxP2⟩) (baseB X) (baseA X)).2 hbaseA_adj
      rwa [hxfixβ] at h
    obtain ⟨g, hgMβ, hg⟩ := hMβ_transB (X.ofB ⟨x, hxP2⟩ • baseA X) (baseA X)
      hxadj hbaseA_adj
    have hgK : g ∈ Kβ := (Subgroup.mem_inf.mp hgMβ).2
    have hgrange : (g : X.Universal) ∈ X.ofB.range := by
      have hsub : g ∈ (MulAction.stabilizer X.Universal (baseB X)).subgroupOf E := by
        rwa [MulAction.stabilizer_subgroupOf]
      rw [stabilizer_baseB X] at hsub
      exact hsub
    obtain ⟨q, hq⟩ := hgrange
    let qx : ↥(f112P2 L1 L2 S) := q * ⟨x, hxP2⟩
    have hqx_def : qx = q * ⟨x, hxP2⟩ := rfl
    have hqx_fixA : X.ofB qx • baseA X = baseA X := by
      rw [hqx_def, map_mul, mul_smul, hq]
      exact hg
    have hqx_ofA : X.ofB qx ∈ X.ofA.range := by
      rw [← stabilizer_baseA X]
      exact MulAction.mem_stabilizer_iff.mpr hqx_fixA
    have hqx_edge : qx ∈ X.edgeB := (ofB_mem_ofA_range_iff X qx).1 hqx_ofA
    have hqx_bigB : (qx : H) ∈ bigB L1 L2 S := by
      rw [← f112_inf_eq_bigB_of_hyp111R hR]
      exact Subgroup.mem_subgroupOf.mp (hXedgeB ▸ hqx_edge)
    have hqM₀' : q ∈ M₀' := by
      rw [Subgroup.mem_comap, hq]
      exact Subgroup.mem_map_of_mem E.subtype hgMβ
    have hqM₀ : (q : H) ∈ M₀ := Subgroup.mem_map_of_mem _ hqM₀'
    refine ⟨(q : H)⁻¹, M₀.inv_mem hqM₀, (qx : H), hqx_bigB, ?_⟩
    rw [hqx_def]
    change x = (q : H)⁻¹ * ((q : H) * x)
    group
  have hO2_le_M₀ : oTwoRes L2 ≤ M₀ :=
    f112sa_oTwoRes_le_of_le_mul hF h1 hn h2 hM₀_le hO2_norm_M₀ hmul_M₀
  have hxU : (x : X.Universal) ∈ MulAction.stabilizer X.Universal (baseB X) := by
    have hxsub : x ∈ (MulAction.stabilizer X.Universal (baseB X)).subgroupOf E := by
      rwa [MulAction.stabilizer_subgroupOf]
    exact hxsub
  rw [stabilizer_baseB X] at hxU
  obtain ⟨y, hy⟩ := hxU
  have hyodd : Odd (orderOf y) := by
    have hofB : orderOf (X.ofB y) = orderOf y :=
      orderOf_injective X.ofB X.ofB_injective y
    have hxord : orderOf (x : X.Universal) = orderOf x := Subgroup.orderOf_coe x
    rw [← hofB, hy, hxord]
    exact hxodd
  have hyodd' : Odd (orderOf (y : H)) := by
    rw [Subgroup.orderOf_coe]
    exact hyodd
  have hyO2 : (y : H) ∈ oTwoRes L2 := f112sa_mem_oTwoRes_of_odd hF h1 y.2 hyodd'
  have hyM₀ : (y : H) ∈ M₀ := hO2_le_M₀ hyO2
  have hyM₀' : y ∈ M₀' := by
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hyM₀
    have hqy' : q = y := Subtype.ext hqy
    rwa [hqy'] at hq
  have hyMβ' : X.ofB y ∈ Mβ' := Subgroup.mem_comap.mp hyM₀'
  have hyMmap : X.ofB y ∈ M.map E.subtype :=
    (Subgroup.map_mono (f := E.subtype) inf_le_left) hyMβ'
  obtain ⟨m, hmM, hmval⟩ := Subgroup.mem_map.mp hyMmap
  have hxeq : x = m := by
    apply Subtype.ext
    calc (x : X.Universal) = X.ofB y := hy.symm
      _ = (m : X.Universal) := hmval.symm
  rwa [hxeq]

theorem f112sa_minimality {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ M : Subgroup ↥(f112EOdd L1 L2 S), M.Normal →
      EdgeTransitive (f112Gold L1 L2 S).treeGraph M → M = ⊤ := by

  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  intro M hMnorm hMtrans
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Kα : Subgroup ↥E := MulAction.stabilizer ↥E (baseA X)
  let Kβ : Subgroup ↥E := MulAction.stabilizer ↥E (baseB X)
  let L' : Subgroup ↥E := Kα ⊓ Kβ
  let Mα : Subgroup ↥E := M ⊓ Kα
  let Mβ : Subgroup ↥E := M ⊓ Kβ
  have hKαdef : Kα = (MulAction.stabilizer X.Universal (baseA X)).subgroupOf E := by
    change MulAction.stabilizer ↥E (baseA X) = _
    rw [← MulAction.stabilizer_subgroupOf]
  have hKβdef : Kβ = (MulAction.stabilizer X.Universal (baseB X)).subgroupOf E := by
    change MulAction.stabilizer ↥E (baseB X) = _
    rw [← MulAction.stabilizer_subgroupOf]
  haveI hKαfin : Finite ↥Kα := by
    rw [hKαdef]
    haveI : Finite (MulAction.stabilizer X.Universal (baseA X)) :=
      finite_stabilizer X (baseA X)
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer X.Universal (baseA X)).subgroupOf E) =>
        (⟨(x.1 : X.Universal), x.2⟩ : ↥(MulAction.stabilizer X.Universal (baseA X))))
      (by intro a b h
          exact Subtype.ext (Subtype.ext
            (congrArg (fun y : ↥(MulAction.stabilizer X.Universal (baseA X)) =>
              (y : X.Universal)) h)))
  haveI hKβfin : Finite ↥Kβ := by
    rw [hKβdef]
    haveI : Finite (MulAction.stabilizer X.Universal (baseB X)) :=
      finite_stabilizer X (baseB X)
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer X.Universal (baseB X)).subgroupOf E) =>
        (⟨(x.1 : X.Universal), x.2⟩ : ↥(MulAction.stabilizer X.Universal (baseB X))))
      (by intro a b h
          exact Subtype.ext (Subtype.ext
            (congrArg (fun y : ↥(MulAction.stabilizer X.Universal (baseB X)) =>
              (y : X.Universal)) h)))
  haveI hL'fin : Finite ↥L' :=
    Finite.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
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
      have heven := f112sa_preservesParts_E (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseA X)
      rw [hdist] at heven
      norm_num at heven
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
      have heven := f112sa_preservesParts_E (L1 := L1) (L2 := L2) (S := S) (g := g)
        (baseB X)
      rw [hdist] at heven
      norm_num at heven
  have hβ_odd_mem : ∀ x : ↥E, x ∈ Kβ → Odd (orderOf x) → x ∈ M :=
    fun x hxK hxodd => f112sa_minimality_beta_of_hyp111R hF hR h1 hn h2 hMnorm hMtrans hxK hxodd
  have hKα_eq : Kα = Mα ⊔ L' := by
    apply le_antisymm
    · intro g hg
      have hgfix : g • baseA X = baseA X := MulAction.mem_stabilizer_iff.mp hg
      have hbase : X.treeGraph.Adj (baseA X) (g • baseB X) := by
        have h := (adj_smul X (g : X.Universal) (baseA X) (baseB X)).2
          (adj_baseA_baseB X)
        have hgfix' : (g : X.Universal) • baseA X = baseA X := hgfix
        rwa [hgfix'] at h
      obtain ⟨m, hmMα, hmB⟩ := hMα_transA (baseB X) (g • baseB X)
        (adj_baseA_baseB X) hbase
      have hmK : m ∈ Kα := (Subgroup.mem_inf.mp hmMα).2
      have hmfix : m • baseA X = baseA X := MulAction.mem_stabilizer_iff.mp hmK
      have hmemL' : m⁻¹ * g ∈ L' := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [MulAction.mem_stabilizer_iff]
          rw [mul_smul, hgfix]
          exact MulAction.mem_stabilizer_iff.mp (Kα.inv_mem hmK)
        · rw [MulAction.mem_stabilizer_iff]
          rw [mul_smul, ← hmB, inv_smul_smul]
      have hgdec : g = m * (m⁻¹ * g) := by group
      rw [hgdec]
      exact Subgroup.mul_mem_sup hmMα hmemL'
    · exact sup_le inf_le_right inf_le_left
  have hodd_edge_mem : ∀ x : ↥E, x ∈ L' → Odd (orderOf x) → x ∈ Mα := by
    intro x hxL hxodd
    have hxKβ : x ∈ Kβ := (Subgroup.mem_inf.mp hxL).2
    have hxM : x ∈ M := hβ_odd_mem x hxKβ hxodd
    exact Subgroup.mem_inf.mpr ⟨hxM, (Subgroup.mem_inf.mp hxL).1⟩
  haveI hNnormal : (Mα.subgroupOf L').Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnM : (n : ↥E) ∈ M := (Subgroup.mem_inf.mp hn).1
    have hnK : (n : ↥E) ∈ Kα := (Subgroup.mem_inf.mp hn).2
    have hgK : (g : ↥E) ∈ Kα := (Subgroup.mem_inf.mp g.2).1
    exact Subgroup.mem_inf.mpr
      ⟨hMnorm.conj_mem _ hnM _, Kα.mul_mem (Kα.mul_mem hgK hnK) (Kα.inv_mem hgK)⟩
  have hL'odd_mem : ∀ x : ↥L', ¬ 2 ∣ orderOf x → x ∈ Mα.subgroupOf L' := by
    intro x hx
    have hxne : ¬ Even (orderOf x) := fun h => hx (even_iff_two_dvd.mp h)
    have hxodd : Odd (orderOf x) := Nat.not_even_iff_odd.mp hxne
    have hxE : (x : ↥E) ∈ Mα := hodd_edge_mem (x : ↥E) x.2 (by
      rw [Subgroup.orderOf_coe]
      exact hxodd)
    exact Subgroup.mem_subgroupOf.mpr hxE
  have hquot : IsPGroup 2 (↥L' ⧸ Mα.subgroupOf L') :=
    CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem
      (Mα.subgroupOf L') hL'odd_mem
  have hMα_normal : (Mα.subgroupOf Kα).Normal := by
    have h := hMnorm.subgroupOf Kα
    have heq : M.subgroupOf Kα = Mα.subgroupOf Kα := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
    rwa [heq] at h
  have hsupK : (Mα.subgroupOf Kα) ⊔ (L'.subgroupOf Kα) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup inf_le_right inf_le_left,
      Subgroup.subgroupOf_eq_top]
    exact hKα_eq.le
  have hNrel : (Mα.subgroupOf Kα).relIndex (L'.subgroupOf Kα) =
      (Mα.subgroupOf L').index := by
    rw [Subgroup.relIndex_subgroupOf inf_le_left,
      ← Subgroup.inf_relIndex_right (H := Mα) (K := L')]
    change ((Mα ⊓ L').subgroupOf L').index = (Mα.subgroupOf L').index
    rw [Subgroup.inf_subgroupOf_right]
  have hIdx : ∃ k, (Mα.subgroupOf Kα).index = 2 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)
      (G := ↥L' ⧸ Mα.subgroupOf L')).mp hquot
    refine ⟨k, ?_⟩
    have h1 : (Mα.subgroupOf Kα).index =
        (Mα.subgroupOf Kα).relIndex (L'.subgroupOf Kα) := by
      rw [← Subgroup.relIndex_top_right (H := Mα.subgroupOf Kα), ← hsupK,
        Subgroup.relIndex_sup_left]
    have h2 : (Mα.subgroupOf Kα).relIndex (L'.subgroupOf Kα) = 2 ^ k := by
      rw [hNrel, Subgroup.index_eq_card]
      exact hk
    rw [h1, h2]
  haveI : (Mα.subgroupOf Kα).Normal := hMα_normal
  have hα_odd_mem : ∀ x : ↥E, x ∈ Kα → Odd (orderOf x) → x ∈ M := by
    intro x hxK hxodd
    have hx' : (⟨x, hxK⟩ : ↥Kα) ∈ Mα.subgroupOf Kα :=
      CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_two_pow_index
        (Mα.subgroupOf Kα) hIdx (by
          rw [← Subgroup.orderOf_coe (⟨x, hxK⟩ : ↥Kα)]
          exact hxodd)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx')).1
  have hsub : {u | (u ∈ X.ofA.range ∨ u ∈ X.ofB.range) ∧ Odd (orderOf u)} ⊆
      M.map E.subtype := by
    rintro u ⟨hor, huodd⟩
    have hxE : u ∈ E := Subgroup.subset_closure ⟨hor, huodd⟩
    have hxM : (⟨u, hxE⟩ : ↥E) ∈ M := by
      have huodd' : Odd (orderOf (⟨u, hxE⟩ : ↥E)) := by
        rw [Subgroup.orderOf_mk]
        exact huodd
      rcases hor with huA | huB
      · have huK : (⟨u, hxE⟩ : ↥E) ∈ Kα := by
          change (⟨u, hxE⟩ : ↥E) ∈ MulAction.stabilizer ↥E (baseA X)
          rw [MulAction.mem_stabilizer_iff]
          show ((⟨u, hxE⟩ : ↥E) : X.Universal) • baseA X = baseA X
          exact MulAction.mem_stabilizer_iff.mp (by
            rw [stabilizer_baseA X]
            exact huA)
        exact hα_odd_mem ⟨u, hxE⟩ huK huodd'
      · have huK : (⟨u, hxE⟩ : ↥E) ∈ Kβ := by
          change (⟨u, hxE⟩ : ↥E) ∈ MulAction.stabilizer ↥E (baseB X)
          rw [MulAction.mem_stabilizer_iff]
          show ((⟨u, hxE⟩ : ↥E) : X.Universal) • baseB X = baseB X
          exact MulAction.mem_stabilizer_iff.mp (by
            rw [stabilizer_baseB X]
            exact huB)
        exact hβ_odd_mem ⟨u, hxE⟩ huK huodd'
    exact ⟨⟨u, hxE⟩, hxM, rfl⟩
  have hclos : E ≤ M.map E.subtype := by
    change Subgroup.closure {u | (u ∈ X.ofA.range ∨ u ∈ X.ofB.range) ∧
      Odd (orderOf u)} ≤ M.map E.subtype
    exact (Subgroup.closure_le _).mpr hsub
  rw [eq_top_iff]
  intro m _
  have hmval : (m : X.Universal) ∈ M.map E.subtype := hclos m.2
  obtain ⟨m', hm', hmm'⟩ := Subgroup.mem_map.mp hmval
  have hmeq : m' = m := Subtype.ext hmm'
  simpa [hmeq] using hm'

theorem f112sa_charTwoStab {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CharTwoStab (V := Vtx (f112Gold L1 L2 S)) (G := ↥(f112EOdd L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  intro v
  let X := f112Gold L1 L2 S
  let Uv : Subgroup X.Universal := MulAction.stabilizer X.Universal v
  let E := f112EOdd L1 L2 S
  haveI hUvfin : Finite Uv := finite_stabilizer X v
  have hEn : (E.subgroupOf Uv).Normal := (f112sa_EOdd_normal hF h1 hn h2).subgroupOf Uv
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

private theorem f112sa_hyp30_of_locL2_of_hyp111R {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hl2 : ∀ v : Vtx (f112Gold L1 L2 S),
      ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
        IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) v
          (nOf (f112Gold L1 L2 S).treeGraph v) N) :
    Hyp30 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) where
  isTree := (f112Gold L1 L2 S).treeGraph_isTree
  adj_smul := by
    intro g u v
    exact adj_smul (f112Gold L1 L2 S) (g : (f112Gold L1 L2 S).Universal) u v
  faithful := by
    intro g hg
    apply Subtype.ext
    exact f112_faithful_of_hyp111R hR (g : (f112Gold L1 L2 S).Universal) (fun v => hg v)
  edgeTrans := f112sa_edgeTransitive_top hF h1 hn h2
  minimal := f112sa_minimality hF h1 hn h2
  finite_stab := by
    intro v
    haveI : Finite ↥(f112P1 L1 L2 S) := Subtype.finite
    haveI : Finite ↥(f112P2 L1 L2 S) := Subtype.finite
    haveI hfin : Finite (MulAction.stabilizer (f112Gold L1 L2 S).Universal v) :=
      finite_stabilizer (f112Gold L1 L2 S) v
    rw [← MulAction.stabilizer_subgroupOf (f112EOdd L1 L2 S) v]
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer (f112Gold L1 L2 S).Universal v).subgroupOf
          (f112EOdd L1 L2 S)) =>
        (⟨(x.1 : (f112Gold L1 L2 S).Universal), x.2⟩ :
          ↥(MulAction.stabilizer (f112Gold L1 L2 S).Universal v)))
      (by
        intro a b h
        have hU : (a.1.1 : (f112Gold L1 L2 S).Universal) = b.1.1 :=
          congrArg (fun x : ↥(MulAction.stabilizer (f112Gold L1 L2 S).Universal v) =>
            (x : (f112Gold L1 L2 S).Universal)) h
        exact Subtype.ext (Subtype.ext hU))
  valency := fun v => f112sa_valency hF h1 hn h2 v
  locL2 := hl2

theorem f112sa_hyp30_of_locL2 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hl2 : ∀ v : Vtx (f112Gold L1 L2 S),
      ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
        IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) v
          (nOf (f112Gold L1 L2 S).treeGraph v) N) :
    Hyp30 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) :=
  f112sa_hyp30_of_locL2_of_hyp111R hF
    (hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2) h1 hn h2 hl2

end CFSG.Quasithin.F112R.St84
