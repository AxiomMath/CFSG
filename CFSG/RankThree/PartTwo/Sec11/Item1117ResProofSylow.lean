module

import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofKernel
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.KFacts.K71bCentList
public import CFSG.RankThree.PartTwo.Sec11.Item1116KFact
public import CFSG.RankThree.PartTwo.Sec11.Skeleton
public import CFSG.RankThree.PartTwo.Sec11.Sylow1129Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Sylow11LocalCentWA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g e : G) (Y' : Subgroup G), Sec11Data G A c L a R Y d x s r g →
      e ∈ A → e ∉ Subgroup.closure {c, d} → Y' ∈ thetaComponentsAt 3 e → sec11K L e ≤ Y' →
      ¬ KFacts.InducesStdKind Y' c .field → Sylow11Case c a R Y d x s r g e Y' →
      ∀ (X : Type) [Group X], IsList119 X →
        Nonempty (sec11YA e Y' A ≃* Multiplicative (ZMod 3) × X) →
      ¬ Sec8.IsZ3PGLThreePi (sec11YA e Y' A) →
      ∀ Q : Subgroup G, IsSylowOf 3 Q (Subgroup.centralizer {e}) →
        sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q →
          Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
            Subgroup.centralizer (A : Set G)

namespace Item1117ResProof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem mem_zpowers_of_mem_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y') {w : G} (hwR : w ∈ R)
    (hwe : w * e = e * w) (hwY : w ∈ Sec4.thetaQuotCentralizer Y') :
    w ∈ Subgroup.zpowers e := by
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  obtain ⟨heN, he3, -, -, -⟩ :=
    basic_facts_of_conj h45 h.toSec11Std h.inf_eq h.closure_eq heA hecd
  have hout : Sec4.InducesOuterTheta e L :=
    ⟨heN, not_isInnerAut_of_not_mem_closure h.toHyp91 h.inf_eq h.closure_eq heA hecd heN⟩
  have heR : e ∈ R := Item1115Proof.A_le_R h.toHyp91 heA
  have htK := Item1119StepsProof.commutator_mem_theta_sec11K_of_mem_thetaQuotCentralizer_Y hstdE
    (hRL hwR) hwe hwY
  obtain ⟨i, hi⟩ := KFacts.exists_mul_pow_mem_thetaQuotCentralizer_of_list h.isList1016 hout he3
    (hRL hwR) (Item1116Proof.exists_pow_eq_one_of_mem h hwR) hwe htK
  have hus : w * e ^ i ∈ Subgroup.zpowers s := by
    rw [← h.inf_centralizer_eq]
    exact ⟨R.mul_mem hwR (R.pow_mem heR i), hi⟩
  have huY : w * e ^ i ∈ Sec4.thetaQuotCentralizer Y' :=
    Subgroup.mul_mem _ hwY (Subgroup.pow_mem _
      (Item1119StepsProof.a_mem_thetaQuotCentralizer_Y hstdE) i)
  have h1 : w * e ^ i = 1 := by
    by_contra hu1
    have hcu := Item1119StepsProof.mem_zpowers_c_of_mem_zpowers_s h hus hu1
    have hcY : c ∈ Sec4.thetaQuotCentralizer Y' := Subgroup.zpowers_le.mpr huY hcu
    have hsec := Item1119StepsProof.mem_sectionCentralizer_of_mem_thetaQuotCentralizer h.mem_A hcY
    rw [(h118 G A c L e R Y' hstdE d g h.inf_eq hA' h.g_mem.2 h.g_not_mem h.conj_mem).2.2] at hsec
    exact (hstdE.not_mem_facts h.inf_eq hA').1 hsec
  have hw : w = (e ^ i)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hw]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) i)

theorem inf_centralizer_A_eq (h : Sec11Data G A c L a R Y d x s r g) {e : G} (heA : e ∈ A)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q) :
    Q ⊓ Subgroup.centralizer (A : Set G) =
      (R ⊓ Subgroup.normalizer (A : Set G)) ⊓ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set CA := Subgroup.centralizer (A : Set G) with hCA
  have hCAH : CA ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hz c h.mem_A).symm)
      rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzc
      exact Subgroup.centralizer_le_normalizer _ hzc
    · exact Subgroup.centralizer_le_normalizer _ hz
  have hNCA : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (CA : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hz ⊢
    intro y hy
    have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hn.2) y).mp hy
    rw [inv_inv] at hy'
    have h1 := hz _ hy'
    calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * y := by group
  have hS := h.isSylowOf_inf.inf_of_le_normalizer hCAH hNCA
  have hle : (R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA ≤ Q ⊓ CA := by
    refine le_inf ?_ inf_le_right
    intro z hz
    refine hTQ ⟨Item1119Proof.R_le_P R g hz.1.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 e heA).symm
  exact hS.eq_of_le hle inf_le_right (hQ.isPGroup.to_le inf_le_left)

theorem mem_zpowers_of_mem_centralizer_A (h45 : Sec4.Item4_5) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y') {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q) {v : G}
    (hv : v ∈ Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G))
    (hvA : v ∈ Subgroup.centralizer (A : Set G)) : v ∈ Subgroup.zpowers e := by
  have hvQ : v ∈ Q ⊓ Subgroup.centralizer (A : Set G) := ⟨hv.1.1, hvA⟩
  rw [inf_centralizer_A_eq h heA hQ hTQ] at hvQ
  exact mem_zpowers_of_mem_thetaQuotCentralizer h45 h118 h heA hecd hY' hKY' hvQ.1.1
    (Subgroup.mem_centralizer_iff.mp hvA e heA).symm hv.1.2

end Item1117ResProof

end CFSG.RankThree.PartTwo.Sec11
