module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofBridge
import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Res163

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isSolvable_of_mem_scriptY4 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : ¬ Group.IsSolvable ↥Y := by
  intro hs
  have hq := hY.2.2.2
  have : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have : Group.IsSolvable (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y))
  exact Group.IsPerfect.not_isSolvable _ this

theorem commutator_mem_pCore_two_of_mem_scriptY4 {A Y : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hY : Y ∈ scriptY4 A LB) (y z : ↥Y)
    (hz : z ∈ CFSG.pPrimeCore 3 ↥Y) : ⁅y, z⁆ ∈ CFSG.pCore 2 ↥Y := by
  set P := CFSG.pCore 2 ↥Y with hP
  set π := QuotientGroup.mk' P with hπ
  set N := (CFSG.pPrimeCore 3 ↥Y).map π with hN
  have hNn : N.Normal :=
    (CFSG.pPrimeCore_normal (p := 3) (G := ↥Y)).map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hY.2.2.2 hNn with htop | hc
  · exfalso
    apply Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : π x ∈ N := htop ▸ Subgroup.mem_top _
    obtain ⟨t, ht, htx⟩ := hx
    have hpx : t⁻¹ * x ∈ P := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have htx' : (t : ↥Y ⧸ P) = (x : ↥Y ⧸ P) := htx
      rw [htx', inv_mul_cancel]
    have hxe : x = t * (t⁻¹ * x) := by group
    rw [hxe]
    exact mul_mem ht (pCore_two_le_pPrimeCore_three hpx)
  · have hzc : π z ∈ Subgroup.center (↥Y ⧸ P) := hc ⟨z, hz, rfl⟩
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have hcomm := Subgroup.mem_center_iff.mp hzc (y : ↥Y ⧸ P)
    have hcomm' : (y : ↥Y ⧸ P) * (z : ↥Y ⧸ P) = (z : ↥Y ⧸ P) * (y : ↥Y ⧸ P) := by
      rwa [hπ, QuotientGroup.mk'_apply] at hcomm
    rw [hcomm']
    group

theorem isQuasisimple_quot_pCore_two_of_commutator {K : Type*} [Group K] [Finite K]
    (hKp : Group.IsPerfect K) (hs : IsSimpleGroup (K ⧸ aschbacherSolvableCore 3 K))
    (hnc : ∃ a b : K ⧸ aschbacherSolvableCore 3 K, a * b ≠ b * a)
    (hc : ∀ k t : K, t ∈ aschbacherSolvableCore 3 K → ⁅k, t⁆ ∈ CFSG.pCore 2 K) :
    CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) := by
  have hθ := solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set θ := aschbacherSolvableCore 3 K with hθdef
  set O := CFSG.pCore 2 K with hOdef
  have : O.Normal := CFSG.pCore_normal
  have : θ.Normal := by
    have := hθ.2.1
    infer_instance
  have hOθ : O ≤ θ := hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
  set S := θ.map (QuotientGroup.mk' O) with hS
  have hSn : S.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have hSc : S ≤ Subgroup.center (K ⧸ O) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O q
    have h1 : ((⁅k, t⁆ : K) : K ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).mpr (hc k t ht)
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
    have h2 : (k : K ⧸ O) * (t : K ⧸ O) = (t : K ⧸ O) * (k : K ⧸ O) := by
      calc (k : K ⧸ O) * (t : K ⧸ O)
          = (k : K ⧸ O) * (t : K ⧸ O) * (k : K ⧸ O)⁻¹ * (t : K ⧸ O)⁻¹ *
              ((t : K ⧸ O) * (k : K ⧸ O)) := by group
        _ = (t : K ⧸ O) * (k : K ⧸ O) := by rw [h1, one_mul]
    exact h2
  have e : (K ⧸ O) ⧸ S ≃* K ⧸ θ := QuotientGroup.quotientQuotientEquivQuotient O θ hOθ
  have hperf : Group.IsPerfect (K ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hs' : IsSimpleGroup ((K ⧸ O) ⧸ S) := by
    have := hs
    exact e.isSimpleGroup
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient S hSc hperf hs' ?_
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩

omit [Finite G] in
theorem mem_pCore_two_of_mem_inf {K N : Subgroup G} (hN2 : IsPGroup 2 N)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) {k : ↥K} (hk : (k : G) ∈ N) :
    k ∈ CFSG.pCore 2 ↥K := by
  have hnorm : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKN g.2) n).mp hn
  have hp : IsPGroup 2 (N.subgroupOf K) := hN2.comap_subtype
  exact (le_sSup (show N.subgroupOf K ∈ {M : Subgroup ↥K | M.Normal ∧ IsPGroup 2 M} from
    ⟨hnorm, hp⟩)) (Subgroup.mem_subgroupOf.mpr hk)

theorem mem_scriptY4_of_theta_le {A Y K : Subgroup G} (hY : Y ∈ scriptY4 A (lB A))
    (hKY : K ≤ Y) (hKp : Group.IsPerfect ↥K)
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (hKΔ : K = deltaZero A (lB A) K)
    (hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y)
    (hs : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K)) (h3 : 3 ∣ Nat.card K) :
    K ∈ scriptY4 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨fun hK => hY.1.1 (top_le_iff.mp (hK ▸ hKY)), le_normalizer_of_eq_deltaZero hKΔ⟩,
    eq_oPrimeResidualOf_of_isSimpleGroup hKp hs h3,
    le_antisymm (hKΔ.le.trans (deltaZero_le_delta K)) (delta_le K), ?_⟩
  refine isQuasisimple_quot_pCore_two_of_commutator hKp hs ?_ fun k t ht => ?_
  · obtain ⟨-, hsq, a, b, hab⟩ := hKq
    have hZ : Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K) = ⊥ := by
      have := hs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K)) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  ·
    have htY : (t : G) ∈ pPrimeCoreOf 3 Y := hθ ⟨t, ht, rfl⟩
    obtain ⟨t', ht', htt'⟩ := Subgroup.mem_map.mp htY
    have hcomm := commutator_mem_pCore_two_of_mem_scriptY4 hY ⟨(k : G), hKY k.2⟩ t' ht'
    have hO2 : ((⁅(⟨(k : G), hKY k.2⟩ : ↥Y), t'⁆ : ↥Y) : G) ∈ CFSG.Open.pCoreOf 2 Y := by
      show _ ∈ (CFSG.Open.pCore 2 ↥Y).map Y.subtype
      exact ⟨_, hcomm, rfl⟩
    have hval : ((⁅(⟨(k : G), hKY k.2⟩ : ↥Y), t'⁆ : ↥Y) : G) = ((⁅k, t⁆ : ↥K) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((t' : ↥Y) : G) = (t : G) from htt']
    rw [hval] at hO2
    exact mem_pCore_two_of_mem_inf (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
      (hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) hO2

theorem lB_eq_bot_of_forall_isEmpty
    {A : Subgroup G}
    (hno : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (B : Subgroup G) : lB A B = ⊥ :=
  lB_eq_bot fun b _ Lb hc => (hno b Lb hc.2.1 (hc.2.2.1 ▸ Set.mem_singleton Lb)).false
    (Item148HJ.j2_of_isLBConfig hc).some

theorem exists_isHyperplane {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    ∃ B : Subgroup G, IsHyperplane A B := by
  have hD := h.toSec13Data
  have hc1 : c ≠ 1 := by
    intro h1
    have h3 := hD.card_zpowers
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  obtain ⟨y, hyA, hy⟩ : ∃ y ∈ A, y ∉ Subgroup.zpowers c := by
    by_contra hne
    push Not at hne
    have hle := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers c from fun y hy => hne y hy)
    rw [hD.card_eq, hD.card_zpowers] at hle
    omega
  exact ⟨_, Main148.isHyperplane_closure_pair148 h.isE27 hD.mem_A hyA hc1 hy⟩

end Res163

open Res163

theorem exists_point148_of_noHJ
    (hCore : Step148Core)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (hno : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hPoint : ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le)
    {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) :
    ¬ Group.IsSolvable ↥Y ∧ (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') ∧
      ∃ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le ∧
        Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e := by
  have hS : Sec14Std G A c L := h.toSec14Std
  have hD := h.toSec13Data
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.1
  have hYY : Y ∈ scriptY A := hY4.1
  have hYs : ¬ Group.IsSolvable ↥Y := not_isSolvable_of_mem_scriptY4 hY4
  have hLB : ∀ B : Subgroup G, lB A B = ⊥ := lB_eq_bot_of_forall_isEmpty hno
  have hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B' := fun B hB =>
    yBOne_of_lB_eq_bot hD.isElemAbelian.1 hB (hLB B)
  obtain ⟨B₀, hB₀⟩ := exists_isHyperplane hS
  have hYΔ : Y = deltaZero A (lB A) Y := rank3II_15_1_lB hS.isE27 ⟨B₀, hB₀, hLB B₀⟩ hY4
  have hex : ∃ B : Subgroup G, IsHyperplane A B ∧ ∃ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) ∧ ∃ b ∈ B, b ≠ 1 ∧
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    by_contra hne
    push Not at hne
    have h1 : Case148One A (lB A) Y := case148One_of_core hCore hS hYY hYs hYB hne
    apply Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : (y : G) ∈ pPrimeCoreOf 3 Y := h1 (hYΔ ▸ y.2)
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hy
    rwa [show y = y' from Subtype.ext hyy'.symm]
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hex
  obtain ⟨e, K, Le, hP⟩ := hPoint Y hYY hYs hYB B hB Q hQ hQY b hb hb1 hQb
  refine ⟨hYs, hYB, B, Q, e, K, Le, hP, ?_⟩
  rcases hP.2.2.2.2.2.2.2.2.2 with ⟨he, hLe⟩ | ⟨c', L', hc', -, hL', ⟨φJ⟩, -⟩
  · exact ⟨he, hLe⟩
  · exact ((hno c' L' hc' hL').false φJ).elim

theorem exists_meetsY4_of_point148
    (hCore : Step148Core)
    (hKT : Step148KType) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hno : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hPoint : ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le)
    {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) :
    ∃ (e : G) (Le : Subgroup G), Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
      MeetsY4 A (lB A) Le Y := by
  have hS : Sec14Std G A c L := h.toSec14Std
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.1
  have hYY : Y ∈ scriptY A := hY4.1
  obtain ⟨hYs, hYB, B, Q, e, K, Le, hP, he, hLe⟩ := exists_point148_of_noHJ hCore h hno hPoint hY
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hKLe : K ≤ Le := hP.2.2.2.2.2.2.2.1
  let := ker148_normal hYY.2
  have hkt := hKT G A c L hS Y hYY hYs hYB B Q e K Le hP
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hsα : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 hS hkt
  obtain ⟨hθ, ⟨ψ⟩⟩ := Main148.theta_equiv_of_img148 hKM hKp hKq hsα (MulEquiv.refl _)
  have hs : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := ψ.isSimpleGroup
  have h3 : 3 ∣ Nat.card K :=
    (Main148.three_dvd_card_img148_of_types hS hkt.2).trans (Main148.card_img148_dvd hKM)
  exact ⟨e, Le, he, hLe, K, mem_scriptY4_of_theta_le hY4 hKY hKp hKq hKΔ hθ hs h3,
    le_inf hKLe hKY⟩

theorem step1513MeetsPoint_of_steps148
    (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) : Sec15.Step1513MeetsPoint :=
  fun G _ _ A c L h hno _ hY => exists_meetsY4_of_point148 hCore hKT h hno
    (hPoint G A c L h.toSec14Std) hY

theorem step163MeetsPoint_of_steps148
    (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) : Step163MeetsPoint :=
  step163MeetsPoint_of_step1513MeetsPoint (step1513MeetsPoint_of_steps148 hCore hPoint hKT)

end CFSG.RankThree.PartTwo.Sec16
