module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAS3
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112slLQ_le_normalizer_Halpha {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saLQ L1 L2 S ≤
      Subgroup.normalizer (f112saHalpha L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  have hNE : f112saLQ L1 L2 S ≤
      Subgroup.normalizer (f112EOdd L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
    haveI : (f112EOdd L1 L2 S).Normal := f112sa_EOdd_normal hF h1 hn h2
    exact Subgroup.le_normalizer_of_normal
  have hNU : f112saLQ L1 L2 S ≤
      Subgroup.normalizer ((f112Gold L1 L2 S).ofA.range :
        Set (f112Gold L1 L2 S).Universal) :=
    (f112saLQ_le_range L1 L2 S).trans Subgroup.le_normalizer
  have hN : f112saLQ L1 L2 S ≤
      Subgroup.normalizer (f112saNalpha L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
    (le_inf hNE hNU).trans (Subgroup.inf_normalizer_le_normalizer_inf
      (H := f112EOdd L1 L2 S) (K := (f112Gold L1 L2 S).ofA.range))
  exact (le_inf hN Subgroup.le_normalizer).trans
    (Subgroup.inf_normalizer_le_normalizer_inf
      (H := f112saNalpha L1 L2 S) (K := f112saLQ L1 L2 S))

theorem f112slNalpha_le_normalizer_NlocalA {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saNalpha L1 L2 S ≤
      Subgroup.normalizer (f112saNlocalA L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (le_inf (f112saNalpha_le_normalizer_Halpha hF)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saNalpha L1 L2 S))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (f112saHalpha L1 L2 S)
      (pCoreOf 2 (f112saNalpha L1 L2 S)))

theorem f112sl_pCoreOf_Halpha {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (f112saHalpha L1 L2 S) = f112saHalpha L1 L2 S ⊓ f112saQ1 L1 L2 S := by
  rw [← f112sa_pCoreOf_LQ hF]
  exact (inf_pCoreOf_eq_pCoreOf (f112saHalpha_le_LQ L1 L2 S)
    (f112slLQ_le_normalizer_Halpha hF h1 hn h2)).symm

theorem f112sl_card_oTwoQuot_Halpha {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) =
      (f112saQ1 L1 L2 S).relIndex
        (f112saHalpha L1 L2 S ⊔ f112saQ1 L1 L2 S) := by
  let A := f112saHalpha L1 L2 S
  let B := f112saQ1 L1 L2 S
  have hAB : A ≤ Subgroup.normalizer (B : Set (f112Gold L1 L2 S).Universal) :=
    f112saHalpha_le_normalizer_Q1 hF
  have hpc : CFSG.pCore 2 ↥A = B.subgroupOf A := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 A, f112sl_pCoreOf_Halpha hF h1 hn h2]
    exact Subgroup.inf_subgroupOf_left B A
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  calc Nat.card (oTwoQuot ↥A) = Nat.card (↥A ⧸ B.subgroupOf A) := by
        change Nat.card (↥A ⧸ CFSG.pCore 2 ↥A) = Nat.card (↥A ⧸ B.subgroupOf A)
        rw [hpc]
    _ = Nat.card (↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) :=
        Nat.card_congr
          (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB).toEquiv
    _ = B.relIndex (A ⊔ B) := rfl

theorem f112sl_three_dvd_relIndex {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    3 ∣ (f112saQ1 L1 L2 S).relIndex
      (f112saHalpha L1 L2 S ⊔ f112saQ1 L1 L2 S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyL, hy3⟩ := f112sa_exists_orderThree_L1 (L2 := L2) (S := S) h1
  let X := f112Gold L1 L2 S
  let y' : ↥(f112P1 L1 L2 S) := ⟨y, Subgroup.mem_sup_left hyL⟩
  have hy'3 : orderOf y' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hy3
  let A := f112saHalpha L1 L2 S
  let B := f112saQ1 L1 L2 S
  have hx3 : orderOf (X.ofA y') = 3 := by
    rw [orderOf_injective X.ofA X.ofA_injective y', hy'3]
  have hxA : X.ofA y' ∈ A := f112sa_ofA_mem_Halpha hF h1 hyL hy3
  have hxB : X.ofA y' ∉ B := by
    intro hmem
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
    have hzQ : (z : H) ∈ pCoreOf 2 (f112P1 L1 L2 S) := Subgroup.mem_subgroupOf.mp hz
    have hzy' : z = y' := by
      apply X.ofA_injective
      exact hzy
    have hz3 : orderOf z = 3 := hzy' ▸ hy'3
    let zQ : ↥(pCoreOf 2 (f112P1 L1 L2 S)) := ⟨(z : H), hzQ⟩
    have hzQ3 : orderOf zQ = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      exact hz3
    obtain ⟨n, hn⟩ :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112P1 L1 L2 S)).exists_card_eq
    have hdvd : 3 ∣ 2 ^ n := by
      have h := orderOf_dvd_natCard zQ
      rw [hzQ3, hn] at h
      exact h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32
  have hNorm : (B.subgroupOf (A ⊔ B)).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    exact sup_le (f112saHalpha_le_normalizer_Q1 hF) Subgroup.le_normalizer
  haveI : (B.subgroupOf (A ⊔ B)).Normal := hNorm
  let π : ↥(A ⊔ B) →* (↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) :=
    QuotientGroup.mk' (B.subgroupOf (A ⊔ B))
  have hxAB : X.ofA y' ∈ A ⊔ B := Subgroup.mem_sup_left hxA
  let x' : ↥(A ⊔ B) := ⟨X.ofA y', hxAB⟩
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    show (X.ofA y') ^ 3 = 1
    rw [← hx3]
    exact pow_orderOf_eq_one _
  have hq3 : π x' ^ 3 = 1 := by
    rw [← map_pow, hx'3, map_one]
  have hord : orderOf (π x') ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hne : π x' ≠ 1 := by
    intro h
    exact hxB (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x').mp h))
  have hord3 : orderOf (π x') = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hdiv : 3 ∣ Nat.card (↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) := by
    rw [← hord3]
    exact orderOf_dvd_natCard (π x')
  simpa [Subgroup.relIndex, Subgroup.index] using hdiv

theorem f112sl_Halpha_dichotomy {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saHalpha L1 L2 S ⊔ f112saQ1 L1 L2 S = f112saLQ L1 L2 S ∨
      Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3 := by
  let A := f112saHalpha L1 L2 S
  let B := f112saQ1 L1 L2 S
  let LQ := f112saLQ L1 L2 S
  have hAB_le : A ⊔ B ≤ LQ :=
    sup_le (f112saHalpha_le_LQ L1 L2 S) (f112saQ1_le_LQ L1 L2 S)
  have hcard : Nat.card (oTwoQuot ↥A) = B.relIndex (A ⊔ B) :=
    f112sl_card_oTwoQuot_Halpha hF h1 hn h2
  have hcardLQ : B.relIndex LQ = 6 := f112saQ1_relIndex_LQ hF h1
  have hmul : B.relIndex (A ⊔ B) * (A ⊔ B).relIndex LQ = B.relIndex LQ :=
    Subgroup.relIndex_mul_relIndex B (A ⊔ B) LQ le_sup_right hAB_le
  have hdvd : B.relIndex (A ⊔ B) ∣ 6 :=
    ⟨(A ⊔ B).relIndex LQ, by rw [hmul, hcardLQ]⟩
  have h3 : 3 ∣ B.relIndex (A ⊔ B) := f112sl_three_dvd_relIndex hF h1
  rw [hcard]
  generalize hdef : B.relIndex (A ⊔ B) = r at hdvd hmul h3 ⊢
  by_cases h6 : r = 6
  · left
    have hone : (A ⊔ B).relIndex LQ = 1 := by
      have h' : 6 * (A ⊔ B).relIndex LQ = 6 * 1 := by
        rw [h6] at hmul
        rw [hcardLQ] at hmul
        rw [mul_one]
        exact hmul
      exact Nat.mul_left_cancel (by norm_num) h'
    exact le_antisymm hAB_le (Subgroup.relIndex_eq_one.mp hone)
  · right
    have hpos : 0 < r := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    have hge : 3 ≤ r := Nat.le_of_dvd hpos h3
    have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases r
    · rfl
    · norm_num at h3
    · norm_num at h3
    · exact absurd rfl h6

theorem f112slHalpha_quot_perm3 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hgood : f112saHalpha L1 L2 S ⊔ f112saQ1 L1 L2 S = f112saLQ L1 L2 S) :
    Nonempty (↥(f112saHalpha L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112saHalpha L1 L2 S) ≃*
      Equiv.Perm (Fin 3)) := by
  have hsup : f112saHalpha L1 L2 S ⊔ pCoreOf 2 (f112saLQ L1 L2 S) = f112saLQ L1 L2 S := by
    rw [f112sa_pCoreOf_LQ hF]
    exact hgood
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf
    (f112saHalpha_le_LQ L1 L2 S) (f112slLQ_le_normalizer_Halpha hF h1 hn h2) hsup
  obtain ⟨e2⟩ := f112saLQ_quot_perm3 hF h1
  exact ⟨e1.trans e2⟩

theorem f112slNlocalA_quot_perm3 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hgood : f112saHalpha L1 L2 S ⊔ f112saQ1 L1 L2 S = f112saLQ L1 L2 S) :
    Nonempty (↥(f112saNlocalA L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112saNlocalA L1 L2 S) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal
    (M := f112saHalpha L1 L2 S) (K := f112saNalpha L1 L2 S)
    (f112saHalpha_le_Nalpha L1 L2 S) (f112saNalpha_le_normalizer_Halpha hF)
  obtain ⟨e2⟩ := f112slHalpha_quot_perm3 hF h1 hn h2 hgood
  exact ⟨e1.trans e2⟩

theorem f112sl_localL2_baseA_of_sup_eq {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hgood : f112saHalpha L1 L2 S ⊔ f112saQ1 L1 L2 S = f112saLQ L1 L2 S) :
    ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) (baseA (f112Gold L1 L2 S)) 1 N := by
  have hR111 : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let E := f112EOdd L1 L2 S
  let X := f112Gold L1 L2 S
  let N : Subgroup ↥E := (f112saNlocalA L1 L2 S).subgroupOf E
  have hstab : MulAction.stabilizer ↥E (baseA X) = (f112saNalpha L1 L2 S).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E (baseA X), stabilizer_baseA X, f112saNalpha,
      Subgroup.inf_subgroupOf_left]
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hstab]
    exact Subgroup.subgroupOf_mono E (f112saNlocalA_le_Nalpha L1 L2 S)
  ·
    rw [hstab]
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : ↥E) : X.Universal) ∈ f112saNlocalA L1 L2 S := by
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn)
    have hg' : ((g : ↥E) : X.Universal) ∈ f112saNalpha L1 L2 S :=
      Subgroup.mem_subgroupOf.mp g.2
    have hconj : ((g : ↥E) : X.Universal) * ((n : ↥E) : X.Universal) *
        ((g : ↥E) : X.Universal)⁻¹ ∈ f112saNlocalA L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp
        (f112slNalpha_le_normalizer_NlocalA hF hg')
        ((n : ↥E) : X.Universal)).mp hn'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hconj
  ·
    rw [hstab]
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hpc := CFSG.Quasithin.St84.pCoreOf_subgroupOf_map
      (K := f112saNalpha L1 L2 S) (E := E) inf_le_left
    have hmem : (y : X.Universal) ∈
        (pCoreOf 2 ((f112saNalpha L1 L2 S).subgroupOf E)).map E.subtype :=
      Subgroup.mem_map_of_mem E.subtype hy
    rw [hpc] at hmem
    exact (show pCoreOf 2 (f112saNalpha L1 L2 S) ≤ f112saNlocalA L1 L2 S from
      le_sup_right) hmem
  ·
    obtain ⟨eN⟩ := f112slNlocalA_quot_perm3 hF h1 hn h2 hgood
    exact CFSG.Quasithin.isL2Quot_one_iff_perm3.mpr
      ⟨(pCoreQuotientMulEquiv 2
        (Subgroup.subgroupOfEquivOfLe (f112saNlocalA_le_E L1 L2 S))).trans eN⟩
  ·
    intro a b ha hb
    obtain ⟨y, hyL, hy3⟩ := f112sa_exists_orderThree_L1 (L2 := L2) (S := S) h1
    let y' : ↥(f112P1 L1 L2 S) := ⟨y, Subgroup.mem_sup_left hyL⟩
    have hy'3 : orderOf y' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hy3
    have hxN : X.ofA y' ∈ f112saNlocalA L1 L2 S :=
      Subgroup.mem_sup_left (f112sa_ofA_mem_Halpha hF h1 hyL hy3)
    have hx3 : orderOf (X.ofA y') = 3 := by
      rw [orderOf_injective X.ofA X.ofA_injective y', hy'3]
    have hxfix : X.ofA y' • baseA X = baseA X :=
      MulAction.mem_stabilizer_iff.mp (by
        rw [stabilizer_baseA X]
        exact ⟨y', rfl⟩)
    obtain ⟨g, hg, hgab⟩ := f112sa_transitive_of_prime_order (p := 3)
      (L1 := L1) (L2 := L2) (S := S) (E := f112saNlocalA L1 L2 S)
      hxN hxfix hx3
      (fun w hw => f112sa_orderThree_not_fixed_of_hyp111R hF hR111 h1 hyL hy'3 hw)
      (f112sa_ncard_neighborSet_baseA hF h1 hn h2) a b ha hb
    exact ⟨⟨g, f112saNlocalA_le_E L1 L2 S hg.1⟩,
      Subgroup.mem_subgroupOf.mpr hg.1, hgab⟩

end CFSG.Quasithin.F112R.St84
