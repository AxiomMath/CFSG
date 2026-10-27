module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeSLB
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLE
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLP2
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLS3
import CFSG.Quasithin.Recognition.St84.Gen.PushZL2
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TreeEOdd
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.Quasithin.Background.C1GNBlockLemmas

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

private theorem f112sl_relIndex_sup_eq_relIndex_inf {G : Type*} [Group G] {N B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (N : Set G)) [Finite ↥B] :
    B.relIndex (N ⊔ B) = (N ⊓ B).relIndex N := by
  let C : Subgroup G := N ⊓ B
  have h1 : C.relIndex B * B.relIndex (N ⊔ B) = C.relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex C B (N ⊔ B) inf_le_right le_sup_right
  have h2 : C.relIndex N * N.relIndex (N ⊔ B) = C.relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex C N (N ⊔ B) inf_le_left le_sup_left
  have h3 : N.relIndex (N ⊔ B) = C.relIndex B := by
    rw [sup_comm]
    exact (CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hB).trans
      (Subgroup.inf_relIndex_right N B).symm
  have h4 : 0 < C.relIndex B :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := C.subgroupOf B))
  have heq : C.relIndex B * B.relIndex (N ⊔ B) = C.relIndex B * C.relIndex N := by
    calc C.relIndex B * B.relIndex (N ⊔ B) = C.relIndex (N ⊔ B) := h1
      _ = C.relIndex N * N.relIndex (N ⊔ B) := h2.symm
      _ = C.relIndex N * C.relIndex B := by rw [h3]
      _ = C.relIndex B * C.relIndex N := mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_left h4 heq

theorem f112slP2_V_relIndex_X2_odd_of_hyp111R {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Odd ((f112saP2_V L2 S).relIndex (f112saX2 L1 L2 S)) := by
  haveI hN : ((f112saP2_V L2 S).subgroupOf (f112saX2 L1 L2 S)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (f112saX2_le_normalizer_V_of_hyp111R hF hR)
  refine f112sa_odd_relIndex_of_two_elements_mem
    (le_inf (f112saP2_V_le_M L2 S)
      (fun _ hx => (le_sup_right : S ≤ bigB L1 L2 S) hx.1.1)) ?_
  intro x hz
  have hzH : IsPGroup 2 (Subgroup.zpowers (x : H)) := by
    have h2 := hz.map (Subgroup.subtype (f112saX2 L1 L2 S))
    have hEq := MonoidHom.map_zpowers (Subgroup.subtype (f112saX2 L1 L2 S)) x
    rwa [hEq] at h2
  exact f112saP2_le_V_of_isPGroup_of_hyp111R hF hR hzH
    (Subgroup.zpowers_le.mpr x.2) (Subgroup.mem_zpowers (x : H))

theorem f112slX2_inf_LQ_relIndex_odd {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Odd (((f112saX2 L1 L2 S) ⊓
      (L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S))).relIndex (f112saX2 L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let V := f112saP2_V L2 S
  let X2 := f112saX2 L1 L2 S
  let LQH : Subgroup H := L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S)
  have hodd : Odd (V.relIndex X2) := f112slP2_V_relIndex_X2_odd_of_hyp111R hF hR h2
  have hVle : V ≤ X2 ⊓ LQH := by
    refine le_inf (f112saP2_V_le_X2 hF h1) ?_
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (f112saP2_V_le_X2 hF h1) (f112saX2_le_normalizer_V_of_hyp111R hF hR)
      (f112saP2_V_isPGroup hF)).trans
      (f112sl_pCoreOf_X2_le_sup_P1 hF h1 hn h2)
  have htower : V.relIndex (X2 ⊓ LQH) * (X2 ⊓ LQH).relIndex X2 = V.relIndex X2 :=
    Subgroup.relIndex_mul_relIndex _ _ _ hVle inf_le_left
  have hprod : Odd (V.relIndex (X2 ⊓ LQH) * (X2 ⊓ LQH).relIndex X2) := htower ▸ hodd
  exact Odd.of_dvd_nat hprod
    (dvd_mul_left ((X2 ⊓ LQH).relIndex X2) (V.relIndex (X2 ⊓ LQH)))

theorem f112sl_twoElement_Ealpha_mem_LQ {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {u : (f112Gold L1 L2 S).Universal}
    (hu : u ∈ f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) :
    u ∈ f112saLQ L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  classical
  let X := f112Gold L1 L2 S
  let P := f112P1 L1 L2 S
  let X2 := f112saX2 L1 L2 S
  let LQH : Subgroup H := L1 ⊔ pCoreOf 2 P
  obtain ⟨huE, huA⟩ := hu
  obtain ⟨p, hp⟩ : ∃ p : ↥P, X.ofA p = u := huA
  have hrange : f112EOdd L1 L2 S ⊓ X.ofA.range =
      ((f112saP1' L1 L2 S).subgroupOf P).map X.ofA :=
    f112_EOdd_inf_ofA_range_of_hyp111R hF.toW hR
  have hpP1' : (p : H) ∈ f112saP1' L1 L2 S := by
    have hu' : (X.ofA p) ∈ ((f112saP1' L1 L2 S).subgroupOf P).map X.ofA := by
      rw [← hrange]
      refine ⟨?_, ⟨p, rfl⟩⟩
      rwa [hp]
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hu'
    have hpq : q = p := X.ofA_injective hqp
    exact hpq ▸ Subgroup.mem_subgroupOf.mp hq
  have hordp : orderOf p = orderOf u := by
    rw [← hp]
    exact (orderOf_injective X.ofA X.ofA_injective p).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hu2) ⟨u, Subgroup.mem_zpowers u⟩
  have hk' : orderOf u = 2 ^ k := by
    rw [← Subgroup.orderOf_mk u (Subgroup.mem_zpowers u)]
    exact hk
  have hp2pow : p ^ 2 ^ k = 1 := by
    have h := pow_orderOf_eq_one p
    rwa [hordp, hk'] at h
  have hX2norm : X2 ≤ Subgroup.normalizer (oTwoRes L1 : Set H) :=
    (f112sa_X2_le_bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_oTwoRes_left hF.toW)
  have hpP1'sup : (p : H) ∈ oTwoRes L1 ⊔ X2 := by
    simpa [f112saP1', X2] using hpP1'
  obtain ⟨a, ha, b, hb, hpb⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := oTwoRes L1) (K := X2) hX2norm).mp hpP1'sup
  have haP : a ∈ P := Subgroup.mem_sup_left ((oTwoRes_le L1) ha)
  have hbP : b ∈ P := Subgroup.mem_sup_right ((f112sa_X2_le_bigB L1 L2 S) hb)
  have hLQnormP : (LQH.subgroupOf P).Normal := f112sa_normal_subgroupOf hF
  have hPnormLQH : P ≤ Subgroup.normalizer (LQH : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show LQH ≤ P from sup_le le_sup_left
        (CFSG.LieType.BorelTits.pCoreOf_le 2 P))).mp hLQnormP
  have hX2normLQH : X2 ≤ Subgroup.normalizer (LQH : Set H) :=
    ((f112sa_X2_le_bigB L1 L2 S).trans le_sup_right).trans hPnormLQH
  let πP : ↥P →* ↥P ⧸ LQH.subgroupOf P := QuotientGroup.mk' (LQH.subgroupOf P)
  have haLQH : a ∈ LQH := Subgroup.mem_sup_left ((oTwoRes_le L1) ha)
  have hp_eq : (⟨(p : H), p.2⟩ : ↥P) = ⟨a, haP⟩ * ⟨b, hbP⟩ :=
    Subtype.ext hpb
  have hb_eq : (⟨b, hbP⟩ : ↥P) = ⟨a, haP⟩⁻¹ * ⟨p, p.2⟩ := by
    rw [hp_eq]
    group
  have hbclass : πP ⟨b, hbP⟩ = πP ⟨p, p.2⟩ := by
    rw [hb_eq, map_mul, map_inv]
    have ha1 : πP ⟨a, haP⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr haLQH)
    rw [ha1, inv_one, one_mul]
  have hbpow : b ^ 2 ^ k ∈ LQH := by
    have h1 : πP ⟨b, hbP⟩ ^ 2 ^ k = 1 := by
      rw [hbclass, ← map_pow, hp2pow, map_one]
    have hmem : (⟨b, hbP⟩ : ↥P) ^ 2 ^ k ∈ LQH.subgroupOf P :=
      (QuotientGroup.eq_one_iff _).mp h1
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hbpowI : b ^ 2 ^ k ∈ X2 ⊓ LQH := ⟨X2.pow_mem hb (2 ^ k), hbpow⟩
  have hX2LQnorm : X2 ≤ Subgroup.normalizer ((X2 ⊓ LQH : Subgroup H) : Set H) :=
    (le_inf Subgroup.le_normalizer hX2normLQH).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := X2) (K := LQH))
  haveI hN : ((X2 ⊓ LQH).subgroupOf X2).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hX2LQnorm
  let πX : ↥X2 →* ↥X2 ⧸ (X2 ⊓ LQH).subgroupOf X2 :=
    QuotientGroup.mk' ((X2 ⊓ LQH).subgroupOf X2)
  let b' : ↥X2 := ⟨b, hb⟩
  have hclasspow : πX b' ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hbpowI)
  have hdvd1 : orderOf (πX b') ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hclasspow
  have hquotodd : Odd (Nat.card (↥X2 ⧸ (X2 ⊓ LQH).subgroupOf X2)) := by
    have hrel := f112slX2_inf_LQ_relIndex_odd hF h1 hn h2
    simpa [X2, LQH, Subgroup.relIndex, Subgroup.index_eq_card] using hrel
  have hdvd2 : orderOf (πX b') ∣ Nat.card (↥X2 ⧸ (X2 ⊓ LQH).subgroupOf X2) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (↥X2 ⧸ (X2 ⊓ LQH).subgroupOf X2)) :=
    (Nat.coprime_two_left.mpr hquotodd).pow_left k
  have hord1 : orderOf (πX b') = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hb1 : πX b' = 1 := orderOf_eq_one_iff.mp hord1
  have hbmem : b' ∈ (X2 ⊓ LQH).subgroupOf X2 := (QuotientGroup.eq_one_iff b').mp hb1
  have hbLQ : b ∈ LQH := (Subgroup.mem_subgroupOf.mp hbmem).2
  have hpLQH : (p : H) ∈ LQH := by
    rw [hpb]
    exact LQH.mul_mem haLQH hbLQ
  have hmap : X.ofA p ∈ (LQH.subgroupOf P).map X.ofA :=
    Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hpLQH, rfl⟩
  rw [← hp]
  simpa [f112saLQ, LQH, P] using hmap

theorem f112slBigT_le_Q1 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigT L1 L2 S ≤ f112saQ1 L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hTle : f112saBigT L1 L2 S ≤ f112saLQ L1 L2 S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saHalpha L1 L2 S)).trans
      (f112saHalpha_le_LQ L1 L2 S)
  have hLQnorm : f112saLQ L1 L2 S ≤
      Subgroup.normalizer (f112saBigT L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
    (f112slLQ_le_normalizer_Halpha hF h1 hn h2).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saHalpha L1 L2 S))
  have hmono := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    hTle hLQnorm (f112saBigT_isPGroup hF)
  rwa [f112sa_pCoreOf_LQ hF] at hmono

theorem f112slBigT_le_Ualphabeta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigT L1 L2 S ≤ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hQ1B : f112saQ1 L1 L2 S ≤
      ((bigB L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ (F1.pCoreOf_parabolic_le_bigB hR))
  have hle : f112saBigT L1 L2 S ≤
      ((bigB L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA :=
    (f112slBigT_le_Q1 hF h1 hn h2).trans hQ1B
  refine le_inf ?_ ?_
  · exact hle.trans (Subgroup.map_le_range (f := (f112Gold L1 L2 S).ofA) _)
  · intro u hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp (hle hu)
    have hbB : (b : H) ∈ bigB L1 L2 S := Subgroup.mem_subgroupOf.mp hb
    have hbP2 : (b : H) ∈ f112P2 L1 L2 S := (f112_inf_eq_bigB_of_hyp111R hR) ▸ hbB |>.2
    rw [f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨b.2, hbP2⟩]
    exact ⟨⟨(b : H), hbP2⟩, rfl⟩

theorem f112sl_twoElement_Ealpha_mem_Halpha
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {u : (f112Gold L1 L2 S).Universal} (hu : u ∈ f112saNalpha L1 L2 S)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) :
    u ∈ f112saHalpha L1 L2 S :=
  Subgroup.mem_inf.mpr ⟨hu, f112sl_twoElement_Ealpha_mem_LQ hF h1 hn h2 hu hu2⟩

theorem f112sl_finite_Nalpha_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) :
    Finite ↥(f112saNalpha L1 L2 S) := by
  change Finite ↥(f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range)
  rw [show f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range =
      ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map
        (f112Gold L1 L2 S).ofA from f112_EOdd_inf_ofA_range_of_hyp111R hF.toW hR]
  let e := Subgroup.equivMapOfInjective
    ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S))
    (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective
  haveI : Finite ↥((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) := Subtype.finite
  exact Finite.of_equiv _ e.toEquiv

theorem f112sl_odd_relIndex_Halpha_Nalpha
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Odd ((f112saHalpha L1 L2 S).relIndex (f112saNalpha L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  haveI : Finite ↥(f112saNalpha L1 L2 S) := f112sl_finite_Nalpha_of_hyp111R hF hR
  haveI : ((f112saHalpha L1 L2 S).subgroupOf (f112saNalpha L1 L2 S)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (f112saNalpha_le_normalizer_Halpha hF)
  refine f112sa_odd_relIndex_of_two_elements_mem (f112saHalpha_le_Nalpha L1 L2 S) ?_
  intro x hx
  have hxU : IsPGroup 2 (Subgroup.zpowers (x : (f112Gold L1 L2 S).Universal)) := by
    have h := hx.map (Subgroup.subtype (f112saNalpha L1 L2 S))
    have hEq := MonoidHom.map_zpowers (Subgroup.subtype (f112saNalpha L1 L2 S)) x
    exact hEq ▸ h
  exact f112sl_twoElement_Ealpha_mem_Halpha hF h1 hn h2 x.2 hxU

theorem f112slBigT_isSylowTwoOf_Nalpha
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hbad : Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3) :
    IsSylowTwoOf (f112saBigT L1 L2 S) (f112saNalpha L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saHalpha L1 L2 S)).trans
      (f112saHalpha_le_Nalpha L1 L2 S))
    (f112saBigT_isPGroup hF) ?_
  have hTrel : (f112saBigT L1 L2 S).relIndex (f112saHalpha L1 L2 S) = 3 := by
    have hpc : (f112saBigT L1 L2 S).subgroupOf (f112saHalpha L1 L2 S) =
        CFSG.pCore 2 ↥(f112saHalpha L1 L2 S) :=
      CFSG.openPCoreOf_subgroupOf 2 (f112saHalpha L1 L2 S)
    rw [Subgroup.relIndex, hpc, Subgroup.index_eq_card]
    simpa [oTwoQuot] using hbad
  have htower := Subgroup.relIndex_mul_relIndex (f112saBigT L1 L2 S)
    (f112saHalpha L1 L2 S) (f112saNalpha L1 L2 S)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (f112saHalpha_le_Nalpha L1 L2 S)
  rw [hTrel] at htower
  intro h2dvd
  rw [← htower] at h2dvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd with h | h
  · norm_num at h
  · exact (Nat.not_even_iff_odd.mpr (f112sl_odd_relIndex_Halpha_Nalpha hF h1 hn h2))
      (even_iff_two_dvd.mpr h)

theorem f112sl_relIndex_K_P2' {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112saK L1 L2 S).relIndex (f112saP2' L1 L2 S) = 2 ^ n + 1 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hBnorm : bigB L1 L2 S ≤
      Subgroup.normalizer (f112saP2' L1 L2 S : Set H) := by
    rw [f112saP2']
    exact F1.le_normalizer_sup (f112sa_bigB_le_normalizer_oTwoRes_right hF.toW)
      (f112sa_bigB_le_normalizer_X1 hF.toW)
  have h := CFSG.Quasithin.F112W.relIndex_sup_eq_relIndex_inf
    (N := f112saP2' L1 L2 S) (B := bigB L1 L2 S) hBnorm
  rw [← f112sa_P2_eq_P2'_sup_bigB hF.toW, f112sa_P2'_inf_bigB hF.toW] at h
  have h5 : (bigB L1 L2 S).relIndex (f112P2 L1 L2 S) = 2 ^ n + 1 := by
    have h' := f112sa_relIndex_right hF h1 hn h2
    rwa [f112_inf_eq_bigB_of_hyp111R hR] at h'
  rw [h5] at h
  exact h.symm

theorem f112sl_EOdd_edge_eq_map_ofB_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
      ((f112saK L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := by
  let X := f112Gold L1 L2 S
  rw [f112_EOdd_inf_ofA_range_inf_ofB_range_of_hyp111R hF.toW hR]
  refine le_antisymm ?_ ?_
  · rintro u ⟨k, hk, rfl⟩
    have hkK : (k : H) ∈ f112saK L1 L2 S := Subgroup.mem_subgroupOf.mp hk
    have hkB : (k : H) ∈ bigB L1 L2 S := f112sa_K_le_bigB L1 L2 S hkK
    have hkP2 : (k : H) ∈ f112P2 L1 L2 S :=
      ((f112_inf_eq_bigB_of_hyp111R hR).symm ▸ hkB).2
    rw [f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨k.2, hkP2⟩]
    exact Subgroup.mem_map.mpr
      ⟨⟨(k : H), hkP2⟩, Subgroup.mem_subgroupOf.mpr hkK, rfl⟩
  · rintro u ⟨k, hk, rfl⟩
    have hkK : (k : H) ∈ f112saK L1 L2 S := Subgroup.mem_subgroupOf.mp hk
    have hkB : (k : H) ∈ bigB L1 L2 S := f112sa_K_le_bigB L1 L2 S hkK
    have hkP1 : (k : H) ∈ f112P1 L1 L2 S :=
      ((f112_inf_eq_bigB_of_hyp111R hR).symm ▸ hkB).1
    rw [← f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hkP1, k.2⟩]
    exact Subgroup.mem_map.mpr
      ⟨⟨(k : H), hkP1⟩, Subgroup.mem_subgroupOf.mpr hkK, rfl⟩

theorem f112sl_relIndex_Ebeta_edge {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓
        (f112Gold L1 L2 S).ofB.range).relIndex
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range) = 2 ^ n + 1 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  rw [f112sl_EOdd_edge_eq_map_ofB_of_hyp111R hF hR,
    f112_EOdd_inf_ofB_range_of_hyp111R hF.toW hR,
    Subgroup.relIndex_map_map_of_injective (f := X.ofB) _ _ X.ofB_injective]
  have hKle : f112saK L1 L2 S ≤ f112saP2' L1 L2 S := by
    rw [f112saK, f112saP2']
    exact sup_le le_sup_right ((inf_le_left : f112saX2 L1 L2 S ≤ oTwoRes L2).trans le_sup_left)
  rw [Subgroup.relIndex_subgroupOf (H := f112saK L1 L2 S)
    (K := f112saP2' L1 L2 S) (L := f112P2 L1 L2 S) (f112sa_P2'_le_P2 hF.toW)]
  exact f112sl_relIndex_K_P2' hF h1 hn h2

theorem f112slBigT_le_Ebeta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigT L1 L2 S ≤
      f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  refine le_inf ?_ ?_
  · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saHalpha L1 L2 S)).trans
      ((f112saHalpha_le_Nalpha L1 L2 S).trans inf_le_left)
  · exact (f112slBigT_le_Ualphabeta hF h1 hn h2).trans inf_le_right

theorem f112slBigT_isSylowTwoOf_edge {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hbad : Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3) :
    IsSylowTwoOf (f112saBigT L1 L2 S)
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓
        (f112Gold L1 L2 S).ofB.range) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hTedge : f112saBigT L1 L2 S ≤
      f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓
        (f112Gold L1 L2 S).ofB.range := by
    refine le_inf ?_ ((f112slBigT_le_Ualphabeta hF h1 hn h2).trans inf_le_right)
    exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      ((f112saHalpha_le_Nalpha L1 L2 S).trans inf_le_left))
      ((f112slBigT_le_Ualphabeta hF h1 hn h2).trans inf_le_left)
  refine CFSG.Quasithin.F7.isSylowTwoOf_mono_right
    (f112slBigT_isSylowTwoOf_Nalpha hF h1 hn h2 hbad) hTedge ?_
  rintro u ⟨⟨huE, huA⟩, -⟩
  exact ⟨huE, huA⟩

theorem f112slBigT_isSylowTwoOf_Ebeta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hbad : Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3) :
    IsSylowTwoOf (f112saBigT L1 L2 S)
      (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let T := f112saBigT L1 L2 S
  let Eβ := f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range
  let D := f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓
    (f112Gold L1 L2 S).ofB.range
  have hTD : T ≤ D := by
    refine le_inf ?_ ((f112slBigT_le_Ualphabeta hF h1 hn h2).trans inf_le_right)
    exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      ((f112saHalpha_le_Nalpha L1 L2 S).trans inf_le_left))
      ((f112slBigT_le_Ualphabeta hF h1 hn h2).trans inf_le_left)
  have hDE : D ≤ Eβ := fun u hu => ⟨hu.1.1, hu.2⟩
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex
    (hTD.trans hDE) (f112saBigT_isPGroup hF) ?_
  have htower := Subgroup.relIndex_mul_relIndex T D Eβ hTD hDE
  have hDodd : Odd (D.relIndex Eβ) := by
    rw [show D.relIndex Eβ = 2 ^ n + 1 from f112sl_relIndex_Ebeta_edge hF h1 hn h2]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hTodd : Odd (T.relIndex D) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex
        (f112slBigT_isSylowTwoOf_edge hF h1 hn h2 hbad)))
  have hprod : Odd (T.relIndex D * D.relIndex Eβ) := hTodd.mul hDodd
  intro h2dvd
  rw [← htower] at h2dvd
  exact (Nat.not_even_iff_odd.mpr hprod) (even_iff_two_dvd.mpr h2dvd)

theorem f112slBigW_le_Ebeta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigW L1 L2 S ≤
      f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range :=
  sup_le f112slMB_le_Nbeta (f112slBigT_le_Ebeta hF h1 hn h2)

theorem f112slBigW_trans {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ w ∈ f112saBigW L1 L2 S, w • a = b := by
  intro a b ha hb
  obtain ⟨g, hg, hgab⟩ := f112slMB_trans hF.toW hn h2 a b ha hb
  exact ⟨g, Subgroup.mem_sup_left hg, hgab⟩

theorem f112sl_finite_Ebeta_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) :
    Finite ↥(f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range) := by
  rw [f112_EOdd_inf_ofB_range_of_hyp111R hF.toW hR]
  let e := Subgroup.equivMapOfInjective
    ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S))
    (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective
  haveI : Finite ↥((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) := Subtype.finite
  exact Finite.of_equiv _ e.toEquiv

theorem f112sl_charTwo_Ebeta {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CharTwo (f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  let Eβ : Subgroup X.Universal := E ⊓ X.ofB.range
  have hstab : MulAction.stabilizer ↥E (baseB X) = Eβ.subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E (baseB X), stabilizer_baseB X]
    ext x
    rw [Subgroup.mem_subgroupOf]
    change (x : X.Universal) ∈ X.ofB.range ↔ (x : X.Universal) ∈ E ⊓ X.ofB.range
    rw [Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hc : CharTwo (Eβ.subgroupOf E) := by
    rw [← hstab]
    exact f112sa_charTwoStab hF h1 hn h2 (baseB X)
  exact CFSG.Quasithin.F6.charTwo_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : Eβ ≤ E)) hc

theorem f112sl_charTwo_BigW {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hbad : Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3) :
    CharTwo (f112saBigW L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  let Eβ : Subgroup X.Universal := f112EOdd L1 L2 S ⊓ X.ofB.range
  let T := f112saBigT L1 L2 S
  let W := f112saBigW L1 L2 S
  have hWEβ : W ≤ Eβ := f112slBigW_le_Ebeta hF h1 hn h2
  haveI : Finite ↥Eβ := f112sl_finite_Ebeta_of_hyp111R hF hR
  have hcharTop : CharTwo (⊤ : Subgroup ↥Eβ) :=
    f112_charTwo_top (f112sl_charTwo_Ebeta hF h1 hn h2)
  have hTEβ : IsSylowTwoOf T Eβ := f112slBigT_isSylowTwoOf_Ebeta hF h1 hn h2 hbad
  have hTtop : IsSylowTwoOf (T.subgroupOf Eβ) (⊤ : Subgroup ↥Eβ) := by
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hTEβ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTEβ.1).symm
    · rw [Subgroup.relIndex_top_right]
      exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hTEβ
  have hTleW : T.subgroupOf Eβ ≤ W.subgroupOf Eβ :=
    Subgroup.subgroupOf_mono Eβ (le_sup_right : T ≤ f112saMB L1 L2 S ⊔ T)
  have hWtop : CharTwo (W.subgroupOf Eβ) :=
    CFSG.Quasithin.C1GN.charTwo_of_le hcharTop hTtop hTleW le_top
  exact CFSG.Quasithin.F6.charTwo_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hWEβ) hWtop

theorem f112slBigT_isSylowTwoOf_BigW
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hbad : Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3) :
    IsSylowTwoOf (f112saBigT L1 L2 S) (f112saBigW L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  let MB := f112saMB L1 L2 S
  let T := f112saBigT L1 L2 S
  let Eβ : Subgroup X.Universal := f112EOdd L1 L2 S ⊓ X.ofB.range
  have hMBle : MB ≤ Eβ := f112slMB_le_Nbeta
  have hTEβ : IsSylowTwoOf T Eβ := f112slBigT_isSylowTwoOf_Ebeta hF h1 hn h2 hbad
  have hEβnorm : Eβ ≤ Subgroup.normalizer (MB : Set X.Universal) :=
    (inf_le_right : Eβ ≤ X.ofB.range).trans (f112saUbeta_le_normalizer_MB hF h1)
  have hTnorm : T ≤ Subgroup.normalizer (MB : Set X.Universal) :=
    (f112slBigT_le_Ebeta hF h1 hn h2).trans hEβnorm
  haveI : Finite ↥Eβ := f112sl_finite_Ebeta_of_hyp111R hF hR
  have hT'syl : IsSylowTwoOf (T.subgroupOf Eβ) (⊤ : Subgroup ↥Eβ) := by
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hTEβ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTEβ.1).symm
    · rw [Subgroup.relIndex_top_right]
      exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hTEβ
  have hT'norm : T.subgroupOf Eβ ≤
      Subgroup.normalizer ((MB.subgroupOf Eβ) : Set ↥Eβ) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp
        (hTnorm (Subgroup.mem_subgroupOf.mp ht)) (x : X.Universal)).mp hx
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp
        (hTnorm (Subgroup.mem_subgroupOf.mp ht)) (x : X.Universal)).mpr hx
  have hT'MB' : IsSylowTwoOf (T.subgroupOf Eβ ⊓ MB.subgroupOf Eβ)
      (MB.subgroupOf Eβ) :=
    CFSG.Quasithin.F7.isSylowTwoOf_inf_normal hT'syl le_top hT'norm
  have hinf : T.subgroupOf Eβ ⊓ MB.subgroupOf Eβ = (T ⊓ MB).subgroupOf Eβ := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hrel : ((T ⊓ MB).subgroupOf Eβ).relIndex (MB.subgroupOf Eβ) =
      (T ⊓ MB).relIndex MB :=
    Subgroup.relIndex_subgroupOf (H := T ⊓ MB) (K := MB) (L := Eβ) hMBle
  have hTMB : IsSylowTwoOf (T ⊓ MB) MB := by
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex inf_le_right
      (hTEβ.2.1.to_le inf_le_left) ?_
    have hodd := CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hT'MB'
    rwa [hinf, hrel] at hodd
  have hidx : T.relIndex (f112saBigW L1 L2 S) = (T ⊓ MB).relIndex MB := by
    change T.relIndex (MB ⊔ T) = (T ⊓ MB).relIndex MB
    haveI : Finite ↥(T.subgroupOf Eβ) := Subtype.finite
    haveI : Finite ↥T :=
      Finite.of_injective (fun x : ↥T =>
        (Subgroup.subgroupOfEquivOfLe hTEβ.1).symm x)
        (Subgroup.subgroupOfEquivOfLe hTEβ.1).symm.injective
    have h := f112sl_relIndex_sup_eq_relIndex_inf (N := MB) (B := T) hTnorm
    rwa [inf_comm MB T] at h
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex le_sup_right
    (f112saBigT_isPGroup hF) ?_
  rw [hidx]
  exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hTMB

theorem f112slBigR_le_bigB {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigR L1 L2 S ≤ bigB L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  rintro x ⟨p, hp, rfl⟩
  have hpT : (f112Gold L1 L2 S).ofB p ∈ f112saBigT L1 L2 S :=
    Subgroup.mem_comap.mp hp
  have hpA : (f112Gold L1 L2 S).ofB p ∈ (f112Gold L1 L2 S).ofA.range :=
    (f112slBigT_le_Ualphabeta hF h1 hn h2 hpT).1
  have hpE : p ∈ (f112Gold L1 L2 S).edgeB :=
    (ofB_mem_ofA_range_iff (f112Gold L1 L2 S) p).mp hpA
  rw [show (f112Gold L1 L2 S).edgeB =
      (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) from
    Subgroup.inclusion_range inf_le_right] at hpE
  have hpB : (p : H) ∈ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S :=
    Subgroup.mem_subgroupOf.mp hpE
  rwa [f112_inf_eq_bigB_of_hyp111R hR] at hpB

theorem f112slBigR_le_sup_pCoreOf {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigR L1 L2 S ≤
      oTwoRes L2 ⊔ pCoreOf 2 (f112P2 L1 L2 S) :=
  f112sl_le_sup_pCoreOf_P2 hF h1 hn h2 (f112saBigR_isPGroup hF)
    (f112slBigR_le_bigB hF h1 hn h2) (f112saBigR_normalized_X2 hF)

theorem f112slBigT_le_BigL {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigT L1 L2 S ≤ f112saBigL L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  let P := f112P2 L1 L2 S
  intro t ht
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp
    ((f112slBigT_le_Ualphabeta hF h1 hn h2 ht).2)
  have hpT : X.ofB p ∈ f112saBigT L1 L2 S := hp ▸ ht
  have hpR : (p : H) ∈ f112saBigR L1 L2 S :=
    Subgroup.mem_map.mpr ⟨p, Subgroup.mem_comap.mpr hpT, rfl⟩
  have hpK : (p : H) ∈ oTwoRes L2 ⊔ pCoreOf 2 P :=
    f112slBigR_le_sup_pCoreOf hF h1 hn h2 hpR
  have hmem : X.ofB p ∈
      ((oTwoRes L2 ⊔ pCoreOf 2 P).subgroupOf P).map X.ofB :=
    Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hpK, rfl⟩
  rw [← hp]
  exact hmem

theorem f112slBigW_le_BigL {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigW L1 L2 S ≤ f112saBigL L1 L2 S :=
  sup_le (f112saMB_le_BigL hF) (f112slBigT_le_BigL hF h1 hn h2)

theorem f112slBigW_sup_Q2B_eq_BigL {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112saBigW L1 L2 S ⊔ f112saQ2B L1 L2 S = f112saBigL L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  refine le_antisymm (sup_le (f112slBigW_le_BigL hF h1 hn h2) ?_) ?_
  · rw [f112saBigL_eq_sup hF]
    exact le_sup_right
  · rw [f112saBigL_eq_sup hF]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

theorem f112slBigK_quot_L2 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nonempty (oTwoQuot ↥(f112saBigK L1 L2 S) ≃* oTwoQuot ↥L2) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let M : Subgroup H := oTwoRes L2
  let P : Subgroup H := f112P2 L1 L2 S
  let Q : Subgroup H := pCoreOf 2 P
  let K : Subgroup H := M ⊔ Q
  have hMK : M ≤ P := (oTwoRes_le L2).trans le_sup_left
  have hnormK : K ≤ Subgroup.normalizer (M : Set H) :=
    sup_le Subgroup.le_normalizer
      (fun x hx =>
        f112saP2_oTwoRes_normal hF h1 (CFSG.LieType.BorelTits.pCoreOf_le 2 P hx))
  have hQK : pCoreOf 2 K = Q := by
    change pCoreOf 2 (M ⊔ Q) = Q
    exact @pCoreOf_sup_pCoreOf H _ (oTwoRes L2) (f112P2 L1 L2 S) hMK
      (f112saP2_oTwoRes_normal hF h1)
  have hsupK : M ⊔ pCoreOf 2 K = K := by rw [hQK]
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf (M := M) (L := K)
    le_sup_left hnormK hsupK
  obtain ⟨e2⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf (M := M) (L := L2)
    (oTwoRes_le L2) (le_normalizer_oTwoRes L2) (f112sl_oTwoRes_sup_pCoreOf hn h2)
  exact ⟨e1.symm.trans e2⟩

theorem f112slBigW_quot_inf_Q2B {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    [hNQ : ((f112saQ2B L1 L2 S).subgroupOf (f112saBigW L1 L2 S)).Normal] :
    Nonempty (↥(f112saBigW L1 L2 S) ⧸
        (f112saQ2B L1 L2 S).subgroupOf (f112saBigW L1 L2 S) ≃*
      oTwoQuot ↥(f112saBigW L1 L2 S ⊔ f112saQ2B L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let W := f112saBigW L1 L2 S
  let Q := f112saQ2B L1 L2 S
  let L := f112saBigL L1 L2 S
  have hWQ : W ⊔ Q = L := f112slBigW_sup_Q2B_eq_BigL hF h1 hn h2
  have hpc : CFSG.pCore 2 ↥(W ⊔ Q) = Q.subgroupOf (W ⊔ Q) := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (W ⊔ Q), hWQ, f112sa_pCoreOf_L hF h1]
  have hQnorm : W ≤ Subgroup.normalizer (Q : Set (f112Gold L1 L2 S).Universal) := by
    refine (f112slBigW_le_BigL hF h1 hn h2).trans ?_
    rw [show Q = pCoreOf 2 L from (f112sa_pCoreOf_L hF h1).symm]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLnorm : W ⊔ Q ≤ Subgroup.normalizer (Q : Set (f112Gold L1 L2 S).Universal) :=
    sup_le hQnorm Subgroup.le_normalizer
  haveI : (Q.subgroupOf (W ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  let e1 := QuotientGroup.quotientInfEquivProdNormalizerQuotient W Q hQnorm
  have e2 : ↥(W ⊔ Q) ⧸ Q.subgroupOf (W ⊔ Q) ≃* oTwoQuot ↥(W ⊔ Q) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).symm
  exact ⟨e1.trans e2⟩

theorem f112slBigW_pCoreOf {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (f112saBigW L1 L2 S) =
      f112saBigW L1 L2 S ⊓ f112saQ2B L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let W := f112saBigW L1 L2 S
  let Q := f112saQ2B L1 L2 S
  let N : Subgroup (f112Gold L1 L2 S).Universal := W ⊓ Q
  have hWQ : W ⊔ Q = f112saBigL L1 L2 S := f112slBigW_sup_Q2B_eq_BigL hF h1 hn h2
  have hQnorm : W ≤ Subgroup.normalizer (Q : Set (f112Gold L1 L2 S).Universal) := by
    refine (f112slBigW_le_BigL hF h1 hn h2).trans ?_
    rw [show Q = pCoreOf 2 (f112saBigL L1 L2 S) from
      (f112sa_pCoreOf_L hF h1).symm]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saBigL L1 L2 S)
  have hsub : N.subgroupOf W = Q.subgroupOf W := by
    ext x
    simp [N]
  have hNQ : (Q.subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQnorm
  haveI := hNQ
  have hNnorm : (N.subgroupOf W).Normal := by
    rw [hsub]
    exact hNQ
  haveI := hNnorm
  have hNle : N ≤ pCoreOf 2 W :=
    CFSG.LieType.BorelTits.le_pCoreOf (r := 2) inf_le_left hNnorm
      (f112saQ2B_isPGroup.to_le inf_le_right)
  obtain ⟨eW⟩ := f112slBigW_quot_inf_Q2B hF h1 hn h2
  let eL : oTwoQuot ↥(W ⊔ Q) ≃* oTwoQuot ↥(f112saBigL L1 L2 S) :=
    pCoreQuotientMulEquiv 2 (MulEquiv.subgroupCongr hWQ)
  obtain ⟨eK⟩ := f112saBigL_quot_BigK (L1 := L1) (L2 := L2) (S := S)
  obtain ⟨eL2⟩ := f112slBigK_quot_L2 hF h1 hn h2
  let e : ↥W ⧸ N.subgroupOf W ≃* oTwoQuot ↥L2 :=
    (QuotientGroup.quotientMulEquivOfEq hsub).trans (eW.trans (eL.trans (eK.trans eL2)))
  have hbotL2 : CFSG.pCore 2 (oTwoQuot ↥L2) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hbot : CFSG.pCore 2 (↥W ⧸ N.subgroupOf W) = ⊥ := by
    have hX := CFSG.pCore_map_iso 2 e.symm
    rw [hbotL2] at hX
    rw [← hX, Subgroup.map_bot]
  have hle : CFSG.pCore 2 ↥W ≤ N.subgroupOf W := by
    let q : ↥W →* ↥W ⧸ N.subgroupOf W := QuotientGroup.mk' (N.subgroupOf W)
    have hnorm : ((CFSG.pCore 2 ↥W).map q).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥W).Normal).map q (QuotientGroup.mk'_surjective _)
    have hp : IsPGroup 2 ((CFSG.pCore 2 ↥W).map q) :=
      (CFSG.pCore_isPGroup (G := ↥W) (p := 2)).map q
    have himage : (CFSG.pCore 2 ↥W).map q ≤
        CFSG.pCore 2 (↥W ⧸ N.subgroupOf W) :=
      CFSG.LieType.BorelTits.le_pCore (r := 2) hnorm hp
    rw [hbot] at himage
    have hker : CFSG.pCore 2 ↥W ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥W) (f := q)).mp
        (le_bot_iff.mp himage)
    simpa [q, QuotientGroup.ker_mk'] using hker
  have hge : N.subgroupOf W ≤ CFSG.pCore 2 ↥W := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 W]
    exact Subgroup.subgroupOf_mono W hNle
  have heq : CFSG.pCore 2 ↥W = N.subgroupOf W := le_antisymm hle hge
  rw [CFSG.openPCoreOf_eq_map_pCore 2 W, heq,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem f112slBigW_quot_L2 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nonempty (oTwoQuot ↥(f112saBigW L1 L2 S) ≃* oTwoQuot ↥L2) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let W := f112saBigW L1 L2 S
  let Q := f112saQ2B L1 L2 S
  let N : Subgroup (f112Gold L1 L2 S).Universal := W ⊓ Q
  have hQnorm : W ≤ Subgroup.normalizer (Q : Set (f112Gold L1 L2 S).Universal) := by
    refine (f112slBigW_le_BigL hF h1 hn h2).trans ?_
    rw [show Q = pCoreOf 2 (f112saBigL L1 L2 S) from
      (f112sa_pCoreOf_L hF h1).symm]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saBigL L1 L2 S)
  have hNQ : (Q.subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQnorm
  haveI := hNQ
  obtain ⟨eW⟩ := f112slBigW_quot_inf_Q2B hF h1 hn h2
  have hsub : N.subgroupOf W = Q.subgroupOf W := by
    ext x
    simp [N]
  haveI hN : (N.subgroupOf W).Normal := by
    rw [hsub]
    exact hNQ
  have hWQ : W ⊔ Q = f112saBigL L1 L2 S := f112slBigW_sup_Q2B_eq_BigL hF h1 hn h2
  let eL : oTwoQuot ↥(W ⊔ Q) ≃* oTwoQuot ↥(f112saBigL L1 L2 S) :=
    pCoreQuotientMulEquiv 2 (MulEquiv.subgroupCongr hWQ)
  obtain ⟨eK⟩ := f112saBigL_quot_BigK (L1 := L1) (L2 := L2) (S := S)
  obtain ⟨eL2⟩ := f112slBigK_quot_L2 hF h1 hn h2
  have hpc : CFSG.pCore 2 ↥W = N.subgroupOf W := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 W, f112slBigW_pCoreOf hF h1 hn h2]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans
    ((QuotientGroup.quotientMulEquivOfEq hsub).trans
      (eW.trans (eL.trans (eK.trans eL2))))⟩

theorem f112sl_isL2Quot_BigW {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsL2Quot n (oTwoQuot ↥(f112saBigW L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  obtain ⟨e⟩ := f112slBigW_quot_L2 hF h1 hn h2
  exact ⟨e.trans h2.some⟩

theorem f112sl_noCharNormal_BigT_BigW
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CFSG.QuasithinUnique.Setup.Campbell.NoCharNormal
      (f112saBigT L1 L2 S) (f112saBigW L1 L2 S) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  intro C hCT hCne hCchar hWN
  let X := f112Gold L1 L2 S
  let T := f112saBigT L1 L2 S
  have hCU : C ≤ X.ofA.range ⊓ X.ofB.range :=
    hCT.trans (f112slBigT_le_Ualphabeta hF h1 hn h2)
  have hEα : f112saNalpha L1 L2 S ≤ Subgroup.normalizer (C : Set X.Universal) := by
    have hmap : (C.subgroupOf T).map T.subtype = C :=
      Subgroup.map_subgroupOf_eq_of_le hCT
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T) (K := C.subgroupOf T)
    rw [hmap] at h
    exact (f112saBigT_le_normalizer_Nalpha hF).trans h
  have hX : C ≤ MulAction.stabilizer X.Universal (baseA X) ⊓
      MulAction.stabilizer X.Universal (baseB X) := by
    rw [stabilizer_baseA X, stabilizer_baseB X]
    exact hCU
  have hα : ∀ a b : Vtx X, X.treeGraph.Adj (baseA X) a →
      X.treeGraph.Adj (baseA X) b →
      ∃ g ∈ Subgroup.normalizer (C : Set X.Universal) ⊓
        MulAction.stabilizer X.Universal (baseA X), g • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := f112sa_transitive_alpha hF h1 hn h2 a b ha hb
    have hgA : g ∈ X.ofA.range := by
      rw [← stabilizer_baseA X]
      exact hg.2
    exact ⟨g, ⟨hEα ⟨hg.1, hgA⟩, hg.2⟩, hgab⟩
  have hβ : ∀ a b : Vtx X, X.treeGraph.Adj (baseB X) a →
      X.treeGraph.Adj (baseB X) b →
      ∃ g ∈ Subgroup.normalizer (C : Set X.Universal) ⊓
        MulAction.stabilizer X.Universal (baseB X), g • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := f112slBigW_trans hF hn h2 a b ha hb
    refine ⟨g, ⟨hWN hg, ?_⟩, hgab⟩
    rw [stabilizer_baseB X]
    exact (f112slBigW_le_Ebeta hF h1 hn h2 hg).2
  have hbot : C = ⊥ :=
    eq_bot_of_normalizer_trans_of_faithful X.treeGraph_isTree.connected (adj_smul X)
      (f112_faithful_of_hyp111R hR) f112sa_exists_adj (adj_baseA_baseB X) hX hα hβ
  exact hCne hbot

theorem f112sl_orderThree_trans {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ x : (f112Gold L1 L2 S).Universal,
      x ∈ MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseA (f112Gold L1 L2 S)) ∧
      x ∈ Subgroup.normalizer (f112saBigT L1 L2 S :
          Set (f112Gold L1 L2 S).Universal) ∧
      Odd (orderOf x) ∧
      (∀ a b : Vtx (f112Gold L1 L2 S),
        (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
        (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
        ∃ k : ℤ, x ^ k • a = b) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  obtain ⟨y, hyL, hy3⟩ := f112sa_exists_orderThree_L1 (L2 := L2) (S := S) h1
  let y' : ↥(f112P1 L1 L2 S) := ⟨y, Subgroup.mem_sup_left hyL⟩
  have hy'3 : orderOf y' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hy3
  let x : X.Universal := X.ofA y'
  have hx3 : orderOf x = 3 := by
    rw [orderOf_injective X.ofA X.ofA_injective y', hy'3]
  have hxH : x ∈ f112saHalpha L1 L2 S := f112sa_ofA_mem_Halpha hF h1 hyL hy3
  have hxα : x ∈ MulAction.stabilizer X.Universal (baseA X) := by
    rw [stabilizer_baseA X]
    exact ⟨y', rfl⟩
  have hxT : x ∈ Subgroup.normalizer (f112saBigT L1 L2 S : Set X.Universal) :=
    f112saBigT_le_normalizer_Halpha hF hxH
  have hxfix : x • baseA X = baseA X := MulAction.mem_stabilizer_iff.mp hxα
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxtr : ∀ a b : Vtx X, X.treeGraph.Adj (baseA X) a →
      X.treeGraph.Adj (baseA X) b → ∃ k : ℤ, x ^ k • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := f112sa_transitive_of_prime_order (p := 3)
      (E := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hxfix hx3
      (fun w hw => f112sa_orderThree_not_fixed_of_hyp111R hF hR h1 (y := y') hyL hy'3 hw)
      (f112sa_ncard_neighborSet_baseA hF h1 hn h2) a b ha hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg.1
    exact ⟨k, by simpa [hk] using hgab⟩
  exact ⟨x, hxα, hxT, by rw [hx3]; norm_num, hxtr⟩

theorem f112sl_bad_case_false {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hbad : Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) = 3) : False := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  have hchar : CharTwo (f112saBigW L1 L2 S) := f112sl_charTwo_BigW hF h1 hn h2 hbad
  have hquot : IsL2Quot n (oTwoQuot ↥(f112saBigW L1 L2 S)) :=
    f112sl_isL2Quot_BigW hF h1 hn h2
  have hT : IsSylowTwoOf (f112saBigT L1 L2 S) (f112saBigW L1 L2 S) :=
    f112slBigT_isSylowTwoOf_BigW hF h1 hn h2 hbad
  have hnc : CFSG.QuasithinUnique.Setup.Campbell.NoCharNormal
      (f112saBigT L1 L2 S) (f112saBigW L1 L2 S) :=
    f112sl_noCharNormal_BigT_BigW hF h1 hn h2
  obtain ⟨x, hxα, hxT, hxo, hxtr⟩ := f112sl_orderThree_trans hF h1 hn h2
  have hWβ : f112saBigW L1 L2 S ≤
      MulAction.stabilizer X.Universal (baseB X) := by
    rw [stabilizer_baseB X]
    exact (f112slBigW_le_Ebeta hF h1 hn h2).trans inf_le_right
  have hTα : f112saBigT L1 L2 S ≤
      MulAction.stabilizer X.Universal (baseA X) := by
    rw [stabilizer_baseA X]
    exact (f112slBigT_le_Ualphabeta hF h1 hn h2).trans inf_le_left
  exact lemmaR_of_faithful_L2 (G := X.Universal) (Γ := X.treeGraph)
    X.treeGraph_isTree.connected (adj_smul X) (f112_faithful_of_hyp111R hR) f112sa_exists_adj
    (adj_baseA_baseB X) (finite_stabilizer X (baseA X)) (finite_stabilizer X (baseB X))
    (by omega : 1 ≤ n) hWβ (f112slBigW_trans hF hn h2) hchar hquot hT hTα hnc
    hxα hxT hxo hxtr

theorem f112sl_card_oTwoQuot_Halpha_ne_three
    {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Nat.card (oTwoQuot ↥(f112saHalpha L1 L2 S)) ≠ 3 := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  intro hbad
  exact f112sl_bad_case_false hF h1 hn h2 hbad

theorem f112sl_localL2_baseA {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) (baseA (f112Gold L1 L2 S)) 1 N := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  rcases f112sl_Halpha_dichotomy hF h1 hn h2 with hgood | hbad
  · exact f112sl_localL2_baseA_of_sup_eq hF h1 hn h2 hgood
  · exact absurd hbad (f112sl_card_oTwoQuot_Halpha_ne_three hF h1 hn h2)

theorem f112sl_localL2 {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ v : Vtx (f112Gold L1 L2 S), ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) v
        (nOf (f112Gold L1 L2 S).treeGraph v) N := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  intro v
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  obtain ⟨w, hw⟩ := f112sa_exists_adj (L1 := L1) (L2 := L2) (S := S) v
  obtain ⟨g, -, hcase⟩ := f112sa_edgeTransitive_top hF h1 hn h2
    (baseA X) (baseB X) v w (adj_baseA_baseB X) hw
  have hadjE : ∀ (k : ↥E) (u w : Vtx X),
      X.treeGraph.Adj (k • u) (k • w) ↔ X.treeGraph.Adj u w :=
    fun k u w => adj_smul X (k : X.Universal) u w
  rcases hcase with ⟨hga, -⟩ | ⟨-, hgb⟩
  · obtain ⟨N, hN⟩ := f112sl_localL2_baseA hF h1 hn h2
    refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_⟩
    have htrans := IsLocL2.smul (Γ := X.treeGraph) hadjE hN g
    have hnα : nOf X.treeGraph (g • baseA X) = 1 :=
      f112sa_nOf_alpha hF h1 hn h2 (g : X.Universal)
    rw [← hga, hnα]
    exact htrans
  · obtain ⟨N, hN⟩ := f112sl_localL2_baseB hF.toW hn h2
    refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_⟩
    have htrans := IsLocL2.smul (Γ := X.treeGraph) hadjE hN g
    have hnβ : nOf X.treeGraph (g • baseB X) = n :=
      f112sa_nOf_beta hF h1 hn h2 (g : X.Universal)
    rw [← hgb, hnβ]
    exact htrans

theorem f112sl_hyp30 {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp30 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) :=
  f112sa_hyp30_of_locL2 hF h1 hn h2 (f112sl_localL2 hF h1 hn h2)

end CFSG.Quasithin.F112R.St84
