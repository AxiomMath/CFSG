module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofHJ
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofGen
public import CFSG.RankThree.PartTwo.Sec17.RouteWire15

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen

namespace Proof156

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mk_mem_inf_centralizer {L : Subgroup G} (S : Sylow 3 ↥L) {b : ↥L}
    (hbS : b ∈ (S : Subgroup ↥L))
    (hb : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) b ∈
      Subgroup.centralizer (((S : Subgroup ↥L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) : Subgroup _) : Set _))
    {s : ↥L} (hs : s ∈ (S : Subgroup ↥L)) : s * b = b * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have h1 := Subgroup.mem_centralizer_iff.mp hb
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s) ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h1
  have hmemS : (s * b)⁻¹ * (b * s) ∈ (S : Subgroup ↥L) :=
    mul_mem (inv_mem (mul_mem hs hbS)) (mul_mem hbS hs)
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨_, hmemS⟩
  have hk' : ((s * b)⁻¹ * (b * s)) ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hθ.2.2.1 h1 hk'
  calc s * b = (s * b) * ((s * b)⁻¹ * (b * s)) := by rw [h2, mul_one]
    _ = b * s := by group

theorem exists_d_of_mem_sectionCentralizer
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A)
    {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A))
    (htype : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥X ⧸ CFSG.pCore 2 ↥X) (alternatingGroup (Fin 6)))
    (hc : c ∈ Late.sectionCentralizer A X (CFSG.Open.pCoreOf 2 X)) :
    ∃ d : G, d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
      Late.sectionCentralizer A X (CFSG.Open.pCoreOf 2 X) =
        (Subgroup.closure {c, d} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  have hq2 : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
  have hθO := inSubgroup_theta_eq_pCoreOf_of_type hq2 htype
  have hXq := isQuasisimple_theta_of_type hq2 htype
  have htype' := type_theta_of_type hq2 htype
  have hX3 := three_dvd_card_quot_center_of_type hXq htype'
  have hX3' : 3 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rcases card_of_type htype' with h | h <;> rw [h] <;> norm_num
  have hX5 : 5 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rcases card_of_type htype' with h | h <;> rw [h] <;> norm_num
  rw [← hθO] at hc ⊢
  have hcC := mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX hc
  have hAnc := not_le_thetaQuotCentralizer_of_mem_partTwoF hD.mem_partTwoF hAX hXq.1 hX3'
  have hcov := le_inf_sup_theta_of_item142 h hJ h142 hAX hX.2.2.1 hXq hX3 hcC hAnc
  have hW := map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  have hθL2 := isPGroup_theta_of_j2 h hJ
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hB3 : IsPGroup 3 (A.subgroupOf L) :=
    hA.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  obtain ⟨S, hBS⟩ := hB3.exists_le_sylow
  set P := S.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L)) with hP
  have hPS : (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = (S : Subgroup ↥L).map π := by
    rw [hP, Sylow.coe_mapSurjective]
  have hB9 := card_map_inf_eq_nine hD hJ
  have hBP : (A.subgroupOf L).map π ≤ (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [hPS]
    exact Subgroup.map_mono hBS
  have hH : Sec4.IsHeisThree (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
    (Sec4.Sporadic.rank3II_4_15 _ hJ P _ rfl _ rfl).1.1
  have hcentral : ∀ b (hb : b ∈ A ⊓ L), b ∈ Sec4.thetaQuotCentralizer X →
      π ⟨b, hb.2⟩ ∈ (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
        Subgroup.centralizer ((P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    intro b hb hbC
    have hbL : b ∈ L := hb.2
    have hb3 : b ^ 3 = 1 := hA.1.2 b hb.1
    have hbN : b ∈ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) :=
      Late.le_normalizer_inf hAX hD.le_normalizer hb.1
    have hcovb := map_inf_centralizer_eq_top inf_le_left hbN hb3 hbC hW
    have hdvd := card_dvd_card_map_of_cover hXq (isPGroup_center_of_type hXq htype') hθL2
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) hcovb
    have hle : (((X ⊓ L) ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf L).map π ≤
        Subgroup.centralizer ({π ⟨b, hbL⟩} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hy).2
    have h5 : 5 ∣ Nat.card (Subgroup.centralizer
        ({π ⟨b, hbL⟩} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
      (hX5.trans hdvd).trans (Subgroup.card_dvd_of_le hle)
    exact mem_center_of_five_dvd_card_centralizer hJ P hBP hB9
      ⟨⟨b, hbL⟩, Subgroup.mem_subgroupOf.mpr hb.1, rfl⟩ h5
  obtain ⟨d, hdB, hd1, hdC⟩ : ∃ d ∈ A ⊓ L, d ≠ 1 ∧ d ∈ Sec4.thetaQuotCentralizer X := by
    rcases htype' with he | h6
    · obtain ⟨e⟩ := he
      exact exists_ne_one_mem_thetaQuotCentralizer_of_five (inf_le_left.trans hAX) h9 e
    · exact exists_ne_one_mem_thetaQuotCentralizer_of_six hD hJ hAX h6 hcov
  have hdL : d ∈ L := hdB.2
  have hdA : d ∈ A := hdB.1
  have hdZ := hcentral d hdB hdC
  have hdS : (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) := hBS (Subgroup.mem_subgroupOf.mpr hdA)
  have hd3c : IsThreeCentralIn L d := by
    refine ⟨hdL, S, hdS, fun s hs => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdZ' : π ⟨d, hdL⟩ ∈ Subgroup.centralizer
        (((S : Subgroup ↥L).map π : Subgroup _) : Set _) := by
      rw [← hPS]
      exact hdZ.2
    exact commute_of_mk_mem_inf_centralizer S hdS hdZ' hs
  have hZ3 : Nat.card ((P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
      Subgroup.centralizer ((P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
          Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = 3 := by
    rw [← Sec14.map_subtype_center_eq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hH.1.2.2.2
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hdbar1 : π ⟨d, hdL⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ aschbacherSolvableCore 3 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have h2 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hθ.2.2.1 hmem (k := 1)
      (Subtype.ext (by simpa using hd3))
    exact hd1 (congrArg Subtype.val h2)
  have hZd : (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
      Subgroup.centralizer ((P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = Subgroup.zpowers (π ⟨d, hdL⟩) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdZ) ?_
    rw [hZ3, Nat.card_zpowers]
    have hd3' : (π ⟨d, hdL⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨d, hdL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, map_one]
    rw [orderOf_eq_prime hd3' hdbar1]
  have hBd : ∀ b ∈ A ⊓ L, b ∈ Sec4.thetaQuotCentralizer X → b ∈ Subgroup.zpowers d := by
    intro b hb hbC
    have hbZ := hcentral b hb hbC
    rw [hZd] at hbZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbZ
    have hmem : (⟨d, hdL⟩ : ↥L) ^ k * (⟨b, hb.2⟩ : ↥L)⁻¹ ∈ aschbacherSolvableCore 3 ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow]
      change (π ⟨d, hdL⟩) ^ k * (π ⟨b, hb.2⟩)⁻¹ = 1
      rw [hk, mul_inv_cancel]
    have hcomm : Commute (d ^ k) b⁻¹ :=
      (Commute.zpow_left (hD.commute hdA hb.1) k).inv_right
    have h3 : ((⟨d, hdL⟩ : ↥L) ^ k * (⟨b, hb.2⟩ : ↥L)⁻¹) ^ 3 ^ 1 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, pow_one,
        Subgroup.coe_pow, Subgroup.coe_one]
      rw [hcomm.mul_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3,
        one_zpow, one_mul, inv_pow, hA.1.2 b hb.1, inv_one]
    have h4 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hθ.2.2.1 hmem h3
    have h5 : d ^ k * b⁻¹ = 1 := by
      have := congrArg Subtype.val h4
      simpa using this
    have h6 : b = d ^ k := (mul_inv_eq_one.mp h5).symm
    rw [h6]
    exact Subgroup.zpow_mem_zpowers d k
  have hcA : c ∈ A := hD.mem_A
  have hcd : Subgroup.closure ({c, d} : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer X := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨hcA, hcC⟩
    · exact ⟨hdA, hdC⟩
  refine ⟨d, hdA, hd1, hd3c, Set.Subset.antisymm ?_ ?_⟩
  · intro a ha
    have haC := mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX ha
    have haA : a ∈ A := ha.1
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
      exact hD.commute hx.1 hcA
    have ha' : a ∈ ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
      rw [← hAc]
      exact haA
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at ha'
    obtain ⟨z, hz, b, hb, rfl⟩ := Set.mem_mul.mp ha'
    have hzC : z ∈ Sec4.thetaQuotCentralizer X :=
      (Subgroup.zpowers_le.mpr hcC) hz
    have hbC : b ∈ Sec4.thetaQuotCentralizer X := by
      have := mul_mem (inv_mem hzC) haC
      rwa [inv_mul_cancel_left] at this
    have hzcd : z ∈ Subgroup.closure ({c, d} : Set G) :=
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c {d}))) hz
    have hbcd : b ∈ Subgroup.closure ({c, d} : Set G) :=
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure
        (Set.mem_insert_of_mem c (Set.mem_singleton d)))) (hBd b hb hbC)
    exact mul_mem hzcd hbcd
  · intro a ha
    have h1 := hcd ha
    exact mem_sectionCentralizer_of_mem_thetaQuotCentralizer h1.1 h1.2

end Proof156

open Proof156

variable {G : Type} [Group G] [Finite G]

theorem step156D_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h142 : Item142AllS14) :
    Step156D A (lB A) := by
  intro Y hY htype c₀ L₀ hc₀ hL₀ hJ hcY
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := hc₀, mem_lA := hL₀ }
  exact exists_d_of_mem_sectionCentralizer h₀ hJ (h142 G A c₀ L₀ h₀) hY.prop.1 htype hcY

theorem step156DR_of
    (h142 : Item142AllS14) : Step156DR :=
  fun _ _ _ _ _ _ hR => step156D_of hR.toSec14Std h142

@[expose] def Step156ONX (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON →
      ∃ (c₀ : G) (L₀ X₁ : Subgroup G), Subgroup.zpowers c₀ ∈ omegaA A ∧ L₀ ∈ lA A c₀ ∧
        Nonempty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        X₁ ∈ scriptY0 A LB ∧ X₁ ≤ Y ∧
        (Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)) ∨
          Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6))) ∧
        c₀ ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) ∧
        (Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) ∨
          Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y)

@[expose] noncomputable def Step156ONXR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156ONX A (lB A)

theorem step156ON_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h142 : Item142AllS14)
    (hX : Step156ONX A (lB A)) : Step156ON A (lB A) := by
  intro Y hY hON
  obtain ⟨c₀, L₀, X₁, hc₀, hL₀, hJ, hX₁, hX₁Y, htype, hcX, hchoice⟩ := hX Y hY hON
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := hc₀, mem_lA := hL₀ }
  obtain ⟨d, hdA, hd1, hdL, hcent⟩ :=
    exists_d_of_mem_sectionCentralizer h₀ hJ (h142 G A c₀ L₀ h₀) hX₁.1 htype hcX
  exact ⟨c₀, L₀, d, X₁, ⟨hc₀, hL₀, hJ, hX₁, hX₁Y, htype, hdA, hd1, hdL, hcent, hchoice⟩⟩

theorem step156ONR_of
    (h142 : Item142AllS14) (hX : Step156ONXR) : Step156ONR :=
  fun G _ _ A c L hR => step156ON_of hR.toSec14Std h142 (hX G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
