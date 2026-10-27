module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Main
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofImg
import CFSG.RankThree.PartTwo.Sec14.Item148StepFieldTypes
import CFSG.RankThree.PartTwo.Sec15.Item15Type
import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4KF
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Lift
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Sig
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148B
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec14.Main148
  CFSG.RankThree.PartTwo.Sec14.HJRes2
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
open Res148BD4

theorem step148D4Q_of_kf (hKF : KF148D4Comm) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Item143NNHJ) : Step148D4 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP hkt he J hJ hKJ hAJ h4
  letI := ker148_normal hY.2
  obtain ⟨n, hn, hK2, hJm, hind⟩ := h4
  have hA : Late.IsE27 A := h.isE27
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) := hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hKYe : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hKY : K ≤ Y := hKYe.trans inf_le_left
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := hKYe.trans inf_le_right
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have heo : orderOf e = 3 := orderOf_eq_prime (hA3 e he) he1
  have hnHJ : ¬ AllPointsHJ A := by
    obtain ⟨heΩ, hLe, hJ2⟩ := types148D4 hkt hn hK2
    exact not_allPointsHJ148 h heΩ hLe hJ2
  have hout : Sec4.InducesOuterTheta (alpha148 A Y e he) (img148 A Y J) :=
    KFacts.InducesStdKind.inducesOuterTheta (img148 A Y J) hind (by decide)
  have hnotin : ¬ InnerOn148 (img148 A Y J) (alpha148 A Y e he) :=
    not_innerOn148_of_inducesOuterTheta hout
  have hZ : Subgroup.center ↥(img148 A Y J) = ⊥ := center_eq_bot_of_trialityD4 hJm
  have hNJ : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hin : ∀ (a : G) (ha : a ∈ A), ∃ k : ℕ,
      InnerOn148 (img148 A Y J) (alpha148 A Y a ha * alpha148 A Y e he ^ k) := fun a ha =>
    exists_innerOn_of_trialityD4 hJm (hNJ (alpha148_mem_img148 he))
      (hNJ (alpha148_mem_img148 ha)) (alpha148_pow_three hA3 he) (alpha148_pow_three hA3 ha)
      hnotin
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  have hAeq : A = Subgroup.zpowers e ⊔ (A ⊓ J) :=
    eq_zpowers_sup_inf_of_innerOn hAF hAY hJY hAJ he hZ hCJ hin
  have heJ : e ∉ J := by
    intro heJ
    apply hnotin
    refine ⟨alpha148 A Y e he, mem_img148_iff.mpr ⟨e, Subgroup.mem_sup_right he, heJ, rfl⟩,
      fun y _ => rfl⟩
  have hKO : ¬ K ≤ pPrimeCoreOf 3 Y := by
    intro hKO
    have hbot : img148 A Y K = ⊥ := Sec15.img148_eq_bot_of_le hKO
    have hc := card_mul_gcd_of_isoLThreePi_two hn hK2
    rw [hbot, Subgroup.card_bot] at hc
    simp only [one_mul] at hc
    have hq : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    have hg1 : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg2 : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h8 : 8 ≤ (2 ^ n) ^ 3 := by
      have := Nat.pow_le_pow_left hq 3
      norm_num at this
      exact this
    have h4' : 4 ≤ (2 ^ n) ^ 2 := by
      have := Nat.pow_le_pow_left hq 2
      norm_num at this
      exact this
    rcases hc with hc | hc
    · have h1 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h2 := Nat.mul_le_mul_left ((2 ^ n) ^ 3) h1
      omega
    · have h1 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h2 := Nat.mul_le_mul_left ((2 ^ n) ^ 3) h1
      omega
  obtain ⟨D, hD, heD, W, hW0, hWK, hWD, hWO, hWnot⟩ :=
    exists_signalizer148 h hYB he hKY hKe hKΔ hKO
  have hD9 : Nat.card D = 9 := by have := hD.2; rw [hA.2] at this; omega
  obtain ⟨d, hdD, hde⟩ := Sec12.exists_mem_not_mem_zpowers hD9 heo
  have hdA : d ∈ A := hD.1 hdD
  obtain ⟨k, b, hbAJ, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers (H := A ⊓ J)
    (fun x hx => hAc x (Subgroup.mem_inf.mp hx).1 e he) (hAeq ▸ hdA)
  have hbA : b ∈ A := hbAJ.1
  have hbJ : b ∈ J := hbAJ.2
  have hbD : b ∈ D := by
    have : b = (e ^ k)⁻¹ * (e ^ k * b) := by group
    rw [this]
    exact D.mul_mem (D.inv_mem (D.zpow_mem heD k)) hdD
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hde (by rw [mul_one]; exact Subgroup.zpow_mem_zpowers e k)
  have hbe : b ∉ Subgroup.zpowers e := by
    intro hb
    apply hde
    exact (Subgroup.zpowers e).mul_mem (Subgroup.zpow_mem_zpowers e k) hb
  have hDeq : Subgroup.closure ({e, b} : Set G) = D := by
    have hle : Subgroup.closure ({e, b} : Set G) ≤ D := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact heD
      · exact hbD
    have hH := isHyperplane_closure_pair148 hA he hbA he1 hbe
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have := hH.2
    rw [hA.2] at this
    omega
  obtain ⟨a, haAJ, haD⟩ : ∃ a ∈ A ⊓ J, a ∉ D := by
    by_contra hall
    push Not at hall
    have hAD : A ≤ D := by
      rw [hAeq]
      exact sup_le (Subgroup.zpowers_le.mpr heD) hall
    have := Subgroup.card_le_of_le hAD
    rw [hA.2, hD9] at this
    omega
  have haA : a ∈ A := haAJ.1
  have haJ : a ∈ J := haAJ.2
  have hWJ : W ≤ J := hWK.trans hKJ
  have hWM : W ≤ Y ⊔ A := hWJ.trans hJM
  have hWb : W ≤ Subgroup.centralizer ({b} : Set G) :=
    hWD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbD))
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := hW0.1.1.2.2
  have hWA : W = ⁅W, A⁆ := hW0.2
  have hWa : W = ⁅W, Subgroup.zpowers a⁆ := commutator_zpowers_eq148 hA hD haA haD hWD hWA
  have hCJe := img148_inf_centralizer_alpha148 hAY hJM hAJ he (hA3 e he)
  have hKCe : img148 A Y K ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} := by
    rw [hCJe]
    exact img148_mono (le_inf hKJ hKe)
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  have hKsubJ : (K.subgroupOf (J ⊓ Subgroup.centralizer {e})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hK).2.2.1
    have hle : J ⊓ Subgroup.centralizer {e} ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle)
    have heq : (K.subgroupOf (Y ⊓ Subgroup.centralizer ({e} : Set G))).comap
        (Subgroup.inclusion hle) = K.subgroupOf (J ⊓ Subgroup.centralizer {e}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hKsub : ((img148 A Y K).subgroupOf
      (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he})).IsSubnormal := by
    rw [hCJe]
    exact isSubnormal_img148 (le_inf hKJ hKe) (inf_le_left.trans hJM) hKsubJ
  have hbα : alpha148 A Y b hbA ∈ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} :=
    ⟨mem_img148_iff.mpr ⟨b, Subgroup.mem_sup_right hbA, hbJ, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (alpha148_comm hAc hbA he)⟩
  have haα : alpha148 A Y a haA ∈ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} :=
    ⟨mem_img148_iff.mpr ⟨a, Subgroup.mem_sup_right haA, haJ, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (alpha148_comm hAc haA he)⟩
  have hbo : orderOf (alpha148 A Y b hbA) = 3 := by
    refine orderOf_eq_prime (alpha148_pow_three hA3 hbA) fun h1 => hb1 ?_
    rw [alpha148_eq_mk', mk'_ker148_eq_one_iff] at h1
    exact eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h1 (k := 1)
      (by rw [pow_one]; exact hA3 b hbA)
  have hVO : img148 A Y W ≤ pPrimeCoreOf 3 (img148 A Y J ⊓
      Subgroup.centralizer {alpha148 A Y e he} ⊓ Subgroup.centralizer {alpha148 A Y b hbA}) :=
    img148_le_pPrimeCoreOf148 hAY hA3 hJY hAJ he hbA hWJ (hDeq ▸ hWD) (hDeq ▸ hWO)
  have haN : alpha148 A Y a haA ∈ Subgroup.normalizer
      (img148 A Y W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAW (alpha148_mem_img148 haA)
  have hVa : img148 A Y W = ⁅img148 A Y W, Subgroup.zpowers (alpha148 A Y a haA)⁆ := by
    rw [← img148_zpowers_eq haA, ← img148_commutator_eq hWM
      ((Subgroup.zpowers_le.mpr haA).trans le_sup_right), ← hWa]
  have hV1 : img148 A Y W ≠ ⊥ := by
    intro hbot
    apply hWnot
    intro w hw
    have : QuotientGroup.mk' (ker148 A Y) ⟨w, hWM hw⟩ ∈ img148 A Y W :=
      mem_img148_iff.mpr ⟨w, hWM hw, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact mk'_ker148_eq_one_iff.mp this
  have hmem := hKF _ (img148 A Y J) n hn hJm (alpha148 A Y e he) (alpha148_pow_three hA3 he) hout
    ⟨img148 A Y K, hKCe, hKαp, hKsub, hK2⟩ (alpha148 A Y b hbA) (alpha148 A Y a haA) hbα haα
    (alpha148_comm hAc haA hbA) hbo (alpha148_pow_three hA3 haA) (img148 A Y W) hVO haN hVa hV1
  have hmem' := mem_sup_of_alpha148_mem148 hAY hA3 hJY hAJ hbA hWb hWM hmem
  refine false_of_mem_commutator148 h422 h45 h142 h134 h48 h415 h (h143 G A c L h hnHJ) hnHJ hD hW0
    hWD hbD hb1 inf_le_right ?_ hmem'
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    (coprime_card_pPrimeCoreOf 3 Y)

theorem step148D4DataQ_of_kf (hKF : KF148D4Comm) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Item143NNHJ) : Step148D4Data := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP hkt he J hJ hKJ hAJ n hn h4
  exact (step148D4Q_of_kf hKF h422 h45 h142 h134 h48 h415 h143 G A c L h Y hY hs hYB B Q e K Le
    hP hkt he J hJ hKJ hAJ ⟨n, hn, h4⟩).elim

end

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
