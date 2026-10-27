module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJ
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormal
import CFSG.RankThree.PartTwo.Sec14.Ronan148AFrame
import CFSG.RankThree.PartTwo.Sec14.Ronan148AHJMove
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.GH74.GLS.C3.Layer1.BkS4Core
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJNine
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJSix
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJTypes
import CFSG.RankThree.PartTwo.Sec14.Ronan148VHJOver
import CFSG.RankThree.PartTwo.Sec4.Ronan148VL37
import CFSG.RankThree.PartTwo.Sec4.Ronan148VON

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
  Ronan148J
open scoped commutatorElement

section Group

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem mem_normalizer_of_isSimpleGroup_of_rank_one {C Z : Subgroup Γ} {x : Γ} (hZC : Z ≤ C)
    (hCZ : C ≤ Subgroup.normalizer (Z : Set Γ)) (hxC : ∀ c ∈ C, x * c * x⁻¹ ∈ C)
    (hxC' : ∀ c ∈ C, x⁻¹ * c * x ∈ C) (hZs : IsSimpleGroup ↥Z) (h3 : 3 ∣ Nat.card Z)
    (hno : ∀ E : Subgroup Γ, E ≤ C → Nat.card E = 9 → (∀ y ∈ E, y ^ 3 = 1) → False) :
    x ∈ Subgroup.normalizer (Z : Set Γ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z' : Subgroup Γ := Z.map (MulAut.conj x).toMonoidHom with hZ'
  have hmem : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z' := fun z hz => ⟨z, hz, rfl⟩
  have hZ'C : Z' ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact hxC z (hZC hz)
  have hCZ' : C ≤ Subgroup.normalizer (Z' : Set Γ) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hc' : x⁻¹ * c * x ∈ Subgroup.normalizer (Z : Set Γ) := hCZ (hxC' c hc)
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(x⁻¹ * c * x) * z * (x⁻¹ * c * x)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hc' z).mp hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨z, hz, hzg⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzg
      refine ⟨(x⁻¹ * c * x)⁻¹ * z * (x⁻¹ * c * x), ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc') z).mp hz
        rw [inv_inv] at this
        exact this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show g = c⁻¹ * (x * z * x⁻¹) * c by rw [hzg]; group]
        group
  haveI := hZs
  haveI : IsSimpleGroup ↥Z' :=
    MulEquiv.isSimpleGroup (Z.equivMapOfInjective _ (MulAut.conj x).injective).symm
  by_cases hne : Z = Z'
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hne.symm
  exfalso
  have hint : Z ⊓ Z' = ⊥ := CFSG.ComponentClassification.AS76b.Lemma34.inf_eq_bot_of_isSimpleGroup
    (hZC.trans hCZ') (hZ'C.trans hCZ) hne
  have hcomm : ∀ u ∈ Z, ∀ v ∈ Z', u * v = v * u := fun u hu v hv =>
    CFSG.GH74.GLS.C3.Layer1.Bk.comm_of_normal_disjoint hZC hZ'C
      (fun t ht y hy => (Subgroup.mem_normalizer_iff.mp (hCZ ht) y).mp hy)
      (fun t ht y hy => (Subgroup.mem_normalizer_iff.mp (hCZ' ht) y).mp hy) hint hu hv
  obtain ⟨u0, hu0⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 h3
  set u : Γ := (u0 : Γ) with hu
  have hu3 : u ^ 3 = 1 := by
    have h := pow_orderOf_eq_one u0
    rw [hu0] at h
    simpa using congrArg Subtype.val h
  have hu1 : u ≠ 1 := by
    intro h
    have : u0 = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu0
    norm_num at hu0
  have hvZ' : x * u * x⁻¹ ∈ Z' := hmem u u0.2
  have hv3 : (x * u * x⁻¹) ^ 3 = 1 := by rw [conj_pow, hu3, mul_one, mul_inv_cancel]
  have hvu : x * u * x⁻¹ ∉ Subgroup.zpowers u := by
    intro hv
    have h1 : x * u * x⁻¹ ∈ Z ⊓ Z' := ⟨(Subgroup.zpowers_le.mpr u0.2) hv, hvZ'⟩
    rw [hint, Subgroup.mem_bot] at h1
    apply hu1
    have h2 : u = x⁻¹ * (x * u * x⁻¹) * x := by group
    rw [h2, h1]
    group
  have huv : u * (x * u * x⁻¹) = (x * u * x⁻¹) * u := hcomm u u0.2 _ hvZ'
  refine hno (Subgroup.zpowers u ⊔ Subgroup.zpowers (x * u * x⁻¹))
    (sup_le (Subgroup.zpowers_le.mpr (hZC u0.2)) (Subgroup.zpowers_le.mpr (hZ'C hvZ')))
    (card_zpowers_sup_zpowers_eq_nine huv hu3 hu1 hv3 hvu) fun y hy => ?_
  have hUV : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers (x * u * x⁻¹), a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute u (x * u * x⁻¹) from huv).zpow_zpow k l).eq
  rw [← commProdHom_range hUV] at hy
  obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [commProdHom_apply, Commute.mul_pow (hUV a a.2 b b.2)]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
  rw [← hk, ← hl, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm,
    zpow_mul, mul_comm (l : ℤ), zpow_mul]
  simp [hu3, hv3]

end Group

variable {G : Type} [Group G] [Finite G]

section Certificates

@[expose] def Step148NormalHJHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        (((deltaZero A (lB A) Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

@[expose] def Step148HJJLeX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y)

@[expose] def Step148HJCentPoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        b ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        ∃ a ∈ A, Subgroup.zpowers a ∈ omegaA A ∧
          a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)

set_option maxHeartbeats 2000000 in
theorem hj_frame148
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hK : KHJPerfectOver)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (ih : Ind148 A (lB A) Y) {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G))) {b d : G}
    {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {Yd : Subgroup G}
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hYdJ : Yd ≤ J)
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hYB6 : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)))
    (hdYB : d ∈ YB) (hdA : d ∈ A) :
    letI := ker148_normal hY.2
    Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
    IsComponent (img148 A Y J) ∧
      img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
        img148 A Y A ⊓ img148 A Y J = img148 A Y A ∧
      Nat.card ↥(img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 ∧
      Nat.card ↥(img148 A Y A ⊓ img148 A Y J) = 9 ∧
      img148 A Y Yd = img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hdA} ∧
      Nat.card ↥(img148 A Y Yd) = 1080 ∧
      img148 A Y Yd ≤ img148 A Y (deltaZero A (lB A) Y) ∧
      img148 A Y (deltaZero A (lB A) Y) =
        img148 A Y (deltaZero A (lB A) Y) ⊓ img148 A Y J ⊔
          img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ∧
      (img148 A Y (deltaZero A (lB A) Y) ⊓ img148 A Y J = img148 A Y Yd ∨
        img148 A Y (deltaZero A (lB A) Y) ⊓ img148 A Y J = img148 A Y J) ∧
      (img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ ∨
        Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
          alternatingGroup (Fin 5))) := by
  intro hJ2
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, -, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
  obtain ⟨φ⟩ := hJ2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have hJcard : Nat.card (img148 A Y J) = 604800 := KFacts.KS14.card_eq_of_j2 ⟨φ⟩
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [hJcard]; norm_num
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAp : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hJZ' : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hCD := sup_eq_of_forall_inner hAab hA3 hF3 hJZ' hAJα
    (fun a ha => exists_inner_of_j2 φ (hAJα ha) (hA3 a ha))
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdα3 : dα ^ 3 = 1 := hA3 _ hdαA
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdnc : ∃ y ∈ img148 A Y J, dα * y ≠ y * dα := by
    by_contra hcon
    push Not at hcon
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcon x hx).symm
  have hdα1 : dα ≠ 1 := by
    intro h
    obtain ⟨y, -, hy⟩ := hdnc
    exact hy (by rw [h, one_mul, mul_one])
  have hXle := img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hdJα hdαA hdnc hCD
  obtain ⟨hYdeq, hYd6, hYdp, hYdZ, -⟩ :=
    img148_yd_facts_of_j2 hY.2 hdA hd3 hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hYdJα : img148 A Y Yd ≤ img148 A Y J := img148_mono hYdJ
  have hYdC : img148 A Y Yd ≤ Subgroup.centralizer {dα} := hYdeq ▸ inf_le_right
  have h3YB : 3 ∣ Nat.card YB := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
      HJRes2.card_of_isTripleCover_six hYB6]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hYBα : img148 A Y YB = img148 A Y Yd := by
    refine Subgroup.eq_of_le_of_card_ge (img148_mono hYBYd) ?_
    have h1 := card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      h3YB
    rw [HJRes2.card_of_isTripleCover_six hYB6] at h1
    rw [HJRes2.card_of_isTripleCover_six hYd6]
    exact h1
  have hYdb : img148 A Y Yd ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (hYBC.trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)))
    exact Set.singleton_subset_iff.mpr hbB
  have hAJYd : img148 A Y A ⊓ img148 A Y J ≤ img148 A Y Yd := by
    intro x hx
    rw [hYdeq]
    exact Subgroup.mem_inf.mpr ⟨hx.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx.1 dα hdαA)⟩
  obtain ⟨j, hjAJ, hjd⟩ : ∃ j ∈ img148 A Y A ⊓ img148 A Y J, j ∉ Subgroup.zpowers dα := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hYd6
    have hx3' : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    have hxJ : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J := hYdJα x.2
    have hxd : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) * dα = dα * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYdC x.2)
    have hAx : img148 A Y A ≤ Subgroup.centralizer {(x : ↥(Y ⊔ A) ⧸ ker148 A Y)} := by
      rw [← hCD]
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp ha.2 x hxJ).symm
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hcon a ha)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.zpow_left hxd.symm k).eq
    have hxA : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y A := by
      refine hF3 _ ?_ hx3'
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAx ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon _ ⟨hxA, hxJ⟩)
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgd : (g : ↥(Y ⊔ A) ⧸ ker148 A Y) * dα = dα * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYdC g.2)
    change (g : ↥(Y ⊔ A) ⧸ ker148 A Y) * x = x * g
    rw [← hk]
    exact (Commute.zpow_right hgd k).eq
  have hjA : j ∈ img148 A Y A := hjAJ.1
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hjYd : j ∈ img148 A Y Yd := hAJYd hjAJ
  have hjnc : ∃ y ∈ img148 A Y Yd, j * y ≠ y * j := by
    by_contra hcon
    push Not at hcon
    exact hjd (hYdZ j hjYd hcon)
  have hdj : dα * j = j * dα := hAab dα hdαA j hjA
  have h9 : Nat.card ↥(Subgroup.zpowers dα ⊔ Subgroup.zpowers j) = 9 :=
    card_zpowers_sup_zpowers_eq_nine hdj hdα3 hdα1 hj3 hjd
  have hle9 : Nat.card ↥(img148 A Y A ⊓ img148 A Y J) ≤ 9 :=
    card_le_nine_of_le_tripleCover hYd6 hYdp hAJYd (fun a ha b hb => hAab a ha.1 b hb.1)
      (fun a ha => hA3 a ha.1)
  have hdjle : Subgroup.zpowers dα ⊔ Subgroup.zpowers j ≤ img148 A Y A ⊓ img148 A Y J :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hdαA, hdJα⟩) (Subgroup.zpowers_le.mpr hjAJ)
  have hAJeq : img148 A Y A ⊓ img148 A Y J = Subgroup.zpowers dα ⊔ Subgroup.zpowers j :=
    (Subgroup.eq_of_le_of_card_ge hdjle (by rw [h9]; exact hle9)).symm
  have hAV : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ img148 A Y Yd →
      j ∈ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro V hV hjV
    rw [← hCD]
    refine sup_le (fun a ha => Subgroup.centralizer_le_normalizer _ ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp ha.2 v (hYdJα (hV hv))
    · rw [hAJeq]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_))
        (Subgroup.zpowers_le.mpr hjV)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYdC (hV hv))
  have hYdX : img148 A Y Yd ≤ img148 A Y (deltaZero A (lB A) Y) :=
    le_of_forall_commutator_le_tripleCover hYd6 hYdp hjYd hj3 hjnc fun V hV hV3 hjV =>
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hjA)).trans
        (commutator_le_img148_deltaZero_of_point h142 hS hY hc.2.1 V (hV.trans hYdb) hV3
          (hAV V hV hjV))
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZX : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      img148 A Y (deltaZero A (lB A) Y) := hZle.trans inf_le_left
  have hZC : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hUV : ∀ u ∈ img148 A Y J, ∀ v ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)),
      u * v = v * u := fun u hu v hv => (Subgroup.mem_centralizer_iff.mp (hZC hv) u hu)
  have hint : img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ hZC).trans hJZ'.le)
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  set H := img148 A Y (deltaZero A (lB A) Y) ⊓ img148 A Y J with hHdef
  have hHJ : H ≤ img148 A Y J := inf_le_right
  have hYdH : img148 A Y Yd ≤ H := le_inf hYdX hYdJα
  have hXeqH : img148 A Y (deltaZero A (lB A) Y) =
      H ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hZX)
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute hUV (hXle hx)
    have huX : u ∈ img148 A Y (deltaZero A (lB A) Y) := by
      have := (img148 A Y (deltaZero A (lB A) Y)).mul_mem hx
        ((img148 A Y (deltaZero A (lB A) Y)).inv_mem (hZX hv))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem_sup ⟨huX, hu⟩ hv
  have hHH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
  have hHp : Group.IsPerfect ↥H := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm hHH ?_
    have hHHJ : ⁅H, H⁆ ≤ img148 A Y J := hHH.trans hHJ
    have hXT : img148 A Y (deltaZero A (lB A) Y) ≤
        ⁅H, H⁆ ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
      refine img148_deltaZero_le_of_hyperplanes_of_le hA le_rfl fun E _ R hR hRE => ?_
      have hRY : R ≤ Y := hRE.trans inf_le_left
      have hRM : R ≤ Y ⊔ A := hRY.trans le_sup_left
      have hRX : img148 A Y R ≤ img148 A Y (deltaZero A (lB A) Y) :=
        img148_mono (le_deltaZero hR hRY)
      have hReq : img148 A Y R = ⁅img148 A Y R, img148 A Y A⁆ := by
        rw [← HJRes2.img148_commutator_eq hRM le_sup_right, ← hR.2]
      rw [hReq, Subgroup.commutator_le]
      intro q hq a ha
      obtain ⟨h, hh, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute (U := H)
        (V := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)))
        (fun u hu v hv => hUV u (hHJ hu) v hv) (by rw [← hXeqH]; exact hRX hq)
      obtain ⟨c', hc', u', hu', rfl⟩ := exists_mul_of_mem_sup_of_commute
        (U := img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
        (V := img148 A Y A ⊓ img148 A Y J)
        (fun u hu v hv => hAab u hu.1 v hv.1) (by rw [hCD]; exact ha)
      have hu'H : u' ∈ H := hYdH (hAJYd hu')
      set a' := c' * u' with ha'
      have hw : z * a' * z⁻¹ * a'⁻¹ ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
        have h1 : a' * z⁻¹ * a'⁻¹ ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp
            (Subgroup.inv_mem _ hz)
        have h2 := Subgroup.mul_mem _ hz h1
        simpa [mul_assoc] using h2
      have hcu : c' * u' * h⁻¹ * u'⁻¹ * c'⁻¹ = u' * h⁻¹ * u'⁻¹ := by
        have hm : u' * h⁻¹ * u'⁻¹ ∈ img148 A Y J :=
          (img148 A Y J).mul_mem ((img148 A Y J).mul_mem (hHJ hu'H)
            ((img148 A Y J).inv_mem (hHJ hh))) ((img148 A Y J).inv_mem (hHJ hu'H))
        have hcm := Subgroup.mem_centralizer_iff.mp hc'.2 _ hm
        calc c' * u' * h⁻¹ * u'⁻¹ * c'⁻¹ = c' * (u' * h⁻¹ * u'⁻¹) * c'⁻¹ := by group
          _ = (u' * h⁻¹ * u'⁻¹) * c' * c'⁻¹ := by rw [← hcm]
          _ = u' * h⁻¹ * u'⁻¹ := by group
      have hwh : (z * a' * z⁻¹ * a'⁻¹) * h = h * (z * a' * z⁻¹ * a'⁻¹) :=
        (hUV h (hHJ hh) _ hw).symm
      have hkey : ⁅h * z, a'⁆ = (z * a' * z⁻¹ * a'⁻¹) * ⁅h, u'⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc h * z * a' * (h * z)⁻¹ * a'⁻¹
            = h * (z * a' * z⁻¹ * a'⁻¹) * (a' * h⁻¹ * a'⁻¹) := by group
          _ = (z * a' * z⁻¹ * a'⁻¹) * h * (a' * h⁻¹ * a'⁻¹) := by rw [← hwh]
          _ = (z * a' * z⁻¹ * a'⁻¹) * h * (u' * h⁻¹ * u'⁻¹) := by
              rw [ha', ← hcu]; group
          _ = (z * a' * z⁻¹ * a'⁻¹) * (h * u' * h⁻¹ * u'⁻¹) := by group
      rw [hkey]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw)
        (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hh hu'H))
    intro x hx
    obtain ⟨k, hk, z, hz, hkz⟩ := exists_mul_of_mem_sup_of_commute (U := ⁅H, H⁆)
      (V := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)))
      (fun u hu v hv => hUV u (hHHJ hu) v hv) (hXT hx.1)
    have hz1 : z = 1 := by
      have hzJ : z ∈ img148 A Y J := by
        have : z = k⁻¹ * x := by rw [hkz]; group
        rw [this]
        exact (img148 A Y J).mul_mem ((img148 A Y J).inv_mem (hHHJ hk)) hx.2
      have : z ∈ img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := ⟨hzJ, hz⟩
      rwa [hint, Subgroup.mem_bot] at this
    rw [hkz, hz1, mul_one]
    exact hk
  have hHcase : H = img148 A Y Yd ∨ H = img148 A Y J := by
    set z' : ↥(img148 A Y J) := ⟨dα, hdJα⟩ with hz'
    have hz'1 : z' ≠ 1 := fun h => hdα1 (congrArg Subtype.val h)
    have hz'3 : z' ^ 3 = 1 := Subtype.ext (by simpa [hz'] using hdα3)
    have hCmap : (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))).map
        (img148 A Y J).subtype = img148 A Y Yd := by
      rw [hYdeq]
      ext g
      constructor
      · rintro ⟨g', hg', rfl⟩
        have hg'' : g' * z' = z' * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'
        exact Subgroup.mem_inf.mpr ⟨g'.2,
          Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg'')⟩
      · intro hg
        obtain ⟨hgJ, hgc⟩ := Subgroup.mem_inf.mp hg
        have hgc' : g * dα = dα * g := Subgroup.mem_centralizer_singleton_iff.mp hgc
        refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hgc')
    have hC27 : 27 ∣ Nat.card (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))) := by
      have h1 : Nat.card ((Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))).map
          (img148 A Y J).subtype) =
          Nat.card (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))) :=
        Subgroup.card_map_of_injective (img148 A Y J).subtype_injective
      rw [hCmap, HJRes2.card_of_isTripleCover_six hYd6] at h1
      rw [← h1]
      norm_num
    haveI := hHp
    have hMp : Group.IsPerfect ↥(H.subgroupOf (img148 A Y J)) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hHJ).symm.toMonoidHom) (MulEquiv.surjective _)
    have hCM : Subgroup.centralizer ({z'} : Set ↥(img148 A Y J)) ≤
        H.subgroupOf (img148 A Y J) := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      exact hYdH (hCmap ▸ ⟨g, hg, rfl⟩)
    rcases hK _ ⟨φ⟩ z' hz'1 hz'3 hC27 _ hMp hCM with h | h
    · left
      rw [← hCmap, ← h, Subgroup.map_subgroupOf_eq_of_le hHJ]
    · right
      exact le_antisymm hHJ (Subgroup.subgroupOf_eq_top.mp h)
  have hC3 : Nat.card ↥(img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 := by
    have hCJ : (img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
          (img148 A Y A ⊓ img148 A Y J) = ⊥ := by
      rw [eq_bot_iff, ← hJZ']
      exact fun x hx => ⟨hx.2.2, hx.1.2⟩
    have h1 := card_sup_eq_mul_of_commute
      (U := img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
      (V := img148 A Y A ⊓ img148 A Y J) (fun u hu v hv => hAab u hu.1 v hv.1) hCJ
    rw [hCD, hAE.2, hAJeq, h9] at h1
    omega
  have hAZC : img148 A Y A ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun x hx => ⟨hx.1, hZC hx.2⟩
  have hEZ : img148 A Y A ⊓ img148 A Y J ≤
      Subgroup.centralizer ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :
        Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hUV x hx.2 z hz).symm
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  have hZtype : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
        alternatingGroup (Fin 5)) := by
    rcases centPre148_type_of_hj h134 h48 hS hY ih hB hc hJY hAJ hJc h3Jα with
      h1 | hZ2 | hZ6 | hZ5 | h36
    · exact Or.inl h1
    · obtain ⟨ψ⟩ := hZ2
      exact (false_of_j2_of_le hAab hA3 hF3 hC3 hAZC hAN ψ).elim
    · exact (false_of_isTripleCover_of_le hAp hF3 hC3 hCD hEZ hAZC hAN hZ6).elim
    · exact Or.inr hZ5
    · exfalso
      rcases h36 with h3' | h6'
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, htype3⟩ := h3'
        rcases htype3 with hON' | hcp | ha5 | h55 | h7 | hL37'
        · obtain ⟨x, hx3, hxZ⟩ := Sec4.Ronan148V.exists_noncentral_of_isTripleCover_ON hON'
          exact false_of_centralNoncentral_of_le hAp hF3 hC3 hCD hEZ hAZC hAN
            (centralNoncentral_congr e ⟨by rw [hON'.1], x, hx3, hxZ⟩)
        · exact false_of_centralNoncentral_of_le hAp hF3 hC3 hCD hEZ hAZC hAN
            (centralNoncentral_congr e (IsCentralProductA6Covers.central_noncentral hcp))
        · exact false_of_centralNoncentral_of_le hAp hF3 hC3 hCD hEZ hAZC hAN
            (centralNoncentral_congr e (IsA6CoverTimesA5.central_noncentral ha5))
        · obtain ⟨χ⟩ := h55
          obtain ⟨h9', hexp⟩ :=
            noNine_subgroup (noNine_congr (e.symm.trans χ).symm noNine_alternating_five_sq)
          exact false_of_exp_three_of_le hAp hF3 hC3 hCD hEZ hAZC hAN h9' hexp
        · obtain ⟨χ⟩ := h7
          obtain ⟨h9', hexp⟩ :=
            noNine_subgroup (noNine_congr (e.symm.trans χ).symm noNine_alternatingGroup_seven)
          exact false_of_exp_three_of_le hAp hF3 hC3 hCD hEZ hAZC hAN h9' hexp
        · obtain ⟨hf7, ⟨χ⟩⟩ := hL37'
          haveI := hf7
          obtain ⟨h9', hexp⟩ := noNine_subgroup (noNine_congr (e.symm.trans χ).symm
            Sec4.Ronan148V.noNine_projSL_three_seven)
          exact false_of_exp_three_of_le hAp hF3 hC3 hCD hEZ hAZC hAN h9' hexp
      · obtain ⟨⟨χ⟩, -, -⟩ := h6'
        obtain ⟨V, hVZ, ⟨ψV⟩, hVN⟩ := exists_j2_factor_le_normalizer (e.symm.trans χ)
        exact false_of_j2_of_le hAab hA3 hF3 hC3 (fun x hx => hAZC ⟨hx.1, hVZ hx.2⟩)
          (fun a ha => hVN a (hAN ha)) ψV
  refine ⟨hJc, hCD, hC3, by rw [hAJeq, h9], hYdeq, HJRes2.card_of_isTripleCover_six hYd6,
    hYdX, hXeqH, hHcase, hZtype⟩

theorem step148HJJLeX_of_point
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hPt : Step148HJCentPoint) : Step148HJJLeX := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hJ2
  let := ker148_normal hY.2
  obtain ⟨hYB6, hdYB, -⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨φ⟩ := hJ2
  obtain ⟨-, hCD, -, h9, hYdeq, h1080, -, -, hHcase, -⟩ :=
    hj_frame148 h142 h134 h48 Ronan148V.khjPerfectOver_holds hS hY ih hB hYB hc hJ hAJ hYd
      hYBYd hYdJ hA6 hθ hdc hYB6 hdYB hdA ⟨φ⟩
  rcases hHcase with hHYd | hHJ
  swap
  · rw [← hHJ]
    exact inf_le_left
  exfalso
  obtain ⟨a, haA, haΩ, hac⟩ : ∃ a ∈ A, Subgroup.zpowers a ∈ omegaA A ∧
      a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
    by_cases hbJ : b ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)
    · exact ⟨b, hbA, hc.2.1, hbJ⟩
    · exact hPt G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
        hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc ⟨φ⟩ hbJ
  have hAE := img148_isE27 (Y := Y) hA
  have hA3 : ∀ x ∈ img148 A Y A, x ^ 3 = 1 := hAE.1.2
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← hdαdef, h, one_mul, mul_one]
  set E : Subgroup ↥(img148 A Y J) := (img148 A Y A ⊓ img148 A Y J).subgroupOf (img148 A Y J)
    with hE
  have hE9 : Nat.card E = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  set z' : ↥(img148 A Y J) := ⟨dα, hdJα⟩ with hz'
  have hz'E : z' ∈ E := Subgroup.mem_subgroupOf.mpr ⟨hdαA, hdJα⟩
  have hz'1 : z' ≠ 1 := fun h => hdα1 (congrArg Subtype.val h)
  have hCmap : (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))).map
      (img148 A Y J).subtype = img148 A Y Yd := by
    rw [hYdeq]
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      have hg'' : g' * z' = z' * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'
      exact Subgroup.mem_inf.mpr ⟨g'.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg'')⟩
    · intro hg
      obtain ⟨hgJ, hgc⟩ := Subgroup.mem_inf.mp hg
      have hgc' : g * dα = dα * g := Subgroup.mem_centralizer_singleton_iff.mp hgc
      refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hgc')
  have hz'27 : 27 ∣ Nat.card (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))) := by
    have h1 : Nat.card ((Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))).map
        (img148 A Y J).subtype) =
        Nat.card (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))) :=
      Subgroup.card_map_of_injective (img148 A Y J).subtype_injective
    rw [hCmap, h1080] at h1
    rw [← h1]
    norm_num
  obtain ⟨V, hV2, hEV, hVz⟩ := j2_exists_twoGroup_not_le_centralizer ⟨φ⟩ hE9 hz'E hz'1 hz'27
  set V' := V.map (img148 A Y J).subtype with hV'
  have hV'J : V' ≤ img148 A Y J := Subgroup.map_subtype_le V
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hV'3 : ¬ 3 ∣ Nat.card V' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hV'2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hAV' : img148 A Y A ≤ Subgroup.normalizer (V' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [← hCD]
    refine sup_le (fun x hx => Subgroup.centralizer_le_normalizer _ ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp hx.2 v (hV'J hv)
    · have hEmap : E.map (img148 A Y J).subtype = img148 A Y A ⊓ img148 A Y J :=
        Subgroup.map_subgroupOf_eq_of_le inf_le_right
      rw [← hEmap]
      exact (Subgroup.map_mono hEV).trans (Subgroup.le_normalizer_map _)
  have haJ := HJRes2.le_centralizer_of_mem_sectionCentralizer haA hac
  have hV'a : V' ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
    intro v hv
    refine Item148Rank.mem_img148_centralizer_of_commute148 hY.2 haA (hA.1.2 a haA) le_rfl
      (img148_mono hJY (hV'J hv)) ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (haJ (hV'J hv))).symm
  have h14 := commutator_le_img148_deltaZero_of_point h142 hS hY haΩ V' hV'a hV'3 hAV'
  have hV'd : V' ≤ Subgroup.centralizer ({dα} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine le_centralizer_of_forall_commutator hV'2 (hA3 _ hdαA) (hAV' hdαA) fun v hv => ?_
    have hmemX : v * dα * v⁻¹ * dα⁻¹ ∈ img148 A Y (deltaZero A (lB A) Y) := by
      have := h14 (Subgroup.commutator_mem_commutator hv hdαA)
      rwa [commutatorElement_def] at this
    have hvJ := hV'J hv
    have hmemJ : v * dα * v⁻¹ * dα⁻¹ ∈ img148 A Y J :=
      (img148 A Y J).mul_mem ((img148 A Y J).mul_mem ((img148 A Y J).mul_mem hvJ hdJα)
        ((img148 A Y J).inv_mem hvJ)) ((img148 A Y J).inv_mem hdJα)
    have hmemH : v * dα * v⁻¹ * dα⁻¹ ∈ img148 A Y Yd := hHYd ▸ ⟨hmemX, hmemJ⟩
    rw [hYdeq] at hmemH
    exact hmemH.2
  refine hVz fun v hv => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (hV'd ⟨v, hv, rfl⟩)

theorem step148NormalHJHJ_of_jle
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hJX : Step148HJJLeX) : Step148NormalHJHJ := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hJ2
  let := ker148_normal hY.2
  have hJXα := hJX G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
    hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hJ2
  obtain ⟨hYB6, hdYB, -⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨φ⟩ := hJ2
  obtain ⟨hJc, hCD, hC3, h9, -, -, -, hXeqH, -, hZtype⟩ :=
    hj_frame148 h142 h134 h48 Ronan148V.khjPerfectOver_holds hS hY ih hB hYB hc hJ hAJ hYd
      hYBYd hYdJ hA6 hθ hdc hYB6 hdYB hdA ⟨φ⟩
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  have hXeq : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J ⊔ Zα := by
    rw [hXeqH, inf_eq_right.mpr hJXα]
  have hAE := img148_isE27 (Y := Y) hA
  have hA3 : ∀ x ∈ img148 A Y A, x ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  obtain ⟨e, heC, he1⟩ : ∃ e ∈ img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)), e ≠ 1 := by
    have h1' : 1 < Nat.card ↥(img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) := by
      rw [hC3]
      norm_num
    obtain ⟨⟨e, he⟩, he1⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one).mp ((Subgroup.one_lt_card_iff_ne_bot _).mp h1')
    exact ⟨e, he, fun h => he1 (Subtype.ext h)⟩
  have heq : Subgroup.zpowers e = img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    zpowers_eq_of_card_three hC3 heC he1
  have he3 : e ^ 3 = 1 := hA3 e heC.1
  have hAeq : img148 A Y A = Subgroup.zpowers e ⊔ (img148 A Y A ⊓ img148 A Y J) := by
    rw [heq, hCD]
  have hAJe : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
        Subgroup.zpowers e := heq.ge
  have hJn : ∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y,
      (img148 A Y J).map (MulAut.conj x).toMonoidHom = img148 A Y J := fun x =>
    map_conj_eq_of_rank_two hJc inf_le_right h9 (fun y hy => hA3 y hy.1) he1 he3 heC.2 hAeq hF3
      hAJe x
  have hno : ∀ E : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      E ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      Nat.card E = 9 → (∀ y ∈ E, y ^ 3 = 1) → False := fun E hEC hE9 hE3 =>
    false_of_le_centralizer_of_rank_two inf_le_right he1 he3 heC.2 hAeq hF3 hAJe hEC hE9 hE3
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    rw [KFacts.KS14.card_eq_of_j2 ⟨φ⟩]
    norm_num
  have hY₁ : centPre148 A Y J ∈ scriptY A := centPre148_mem_scriptY hY hAJ
  have hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y :=
    pPrimeCoreOf_centPre148_eq_of_isComponent hY.2 hJY hJc h3J
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJne : img148 A Y J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hJs.toNontrivial
  have hlt : Nat.card (centPre148 A Y J) < Nat.card Y :=
    card_centPre148_lt hJY (Ronan148M.exists_ne_comm_of_isPerfect hJp hJne)
  have h148₁ : Item148At A (lB A) (centPre148 A Y J) hY₁ := ih _ hY₁ hlt
  letI := ker148_normal hY₁.2
  have hX1Y₁ : deltaZero A (lB A) (centPre148 A Y J) ≤ centPre148 A Y J :=
    sSup_le fun _ hQ => hQ.2
  have hN₁ := img148_le_normalizer_of_map_normal (A := A) hX1Y₁ h148₁.1
  have hY₁Z : img148 A Y (centPre148 A Y J) ≤ Subgroup.normalizer (Zα : Set _) := by
    rw [hZα, ← map_img148_compare148 hcore.le le_sup_left,
      ← map_img148_compare148 hcore.le (hX1Y₁.trans le_sup_left)]
    exact (Subgroup.map_mono hN₁).trans (Subgroup.le_normalizer_map _)
  have hXY : deltaZero A (lB A) Y ≤ Y := sSup_le fun _ hQ => hQ.2
  refine map_normal_of_img148_eq (A := A) (J := deltaZero A (lB A) Y) hXY rfl fun y hy => ?_
  set yα := QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) with hyα
  have hyY : yα ∈ img148 A Y Y := mem_img148_iff.mpr ⟨y, _, hy, rfl⟩
  have hyJ : yα ∈ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hJn yα)
  have hyZ : yα ∈ Subgroup.normalizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rcases hZtype with hZ1 | hZ5
    · rw [hZ1, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_bot]
    · obtain ⟨ψ⟩ := hZ5
      have hYn := Item148Res5.img148_normal (A := A) hY.2
      have hCn := KFacts.KS14.normalizer_le_normalizer_centralizer (img148 A Y J)
      have hconj : ∀ x ∈ img148 A Y Y, ∀ c ∈ img148 A Y (centPre148 A Y J),
          x * c * x⁻¹ ∈ img148 A Y (centPre148 A Y J) := by
        intro x hx c hc
        rw [img148_centPre148_eq] at hc ⊢
        have hxJ : x ∈ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hJn x)
        exact ⟨hYn.conj_mem c hc.1 x, (Subgroup.mem_normalizer_iff.mp (hCn hxJ) c).mp hc.2⟩
      have hZs : IsSimpleGroup ↥Zα := MulEquiv.isSimpleGroup ψ
      have h3Z : 3 ∣ Nat.card ↥Zα := by
        rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
        norm_num
      have hY₁C : img148 A Y (centPre148 A Y J) ≤
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [img148_centPre148_eq]
        exact inf_le_right
      refine mem_normalizer_of_isSimpleGroup_of_rank_one (C := img148 A Y (centPre148 A Y J))
        (img148_mono hX1Y₁) hY₁Z (hconj yα hyY) (fun c hc => ?_) hZs h3Z
        fun E hE hE9 hE3 => hno E (hE.trans hY₁C) hE9 hE3
      have := hconj yα⁻¹ (inv_mem hyY) c hc
      rwa [inv_inv] at this
  rw [hXeq, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyJ, Subgroup.mem_normalizer_iff_map_conj_eq.mp hyZ]

theorem step148NormalHJHJ_of_point
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hPt : Step148HJCentPoint) : Step148NormalHJHJ :=
  step148NormalHJHJ_of_jle h142 h134 h48 (step148HJJLeX_of_point h142 h134 h48 hPt)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
