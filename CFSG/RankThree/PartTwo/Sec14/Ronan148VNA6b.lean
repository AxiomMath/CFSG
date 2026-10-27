module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VNA6
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pow_four_dvd_card_of_types {W : Type} [Group W] [Finite W]
    (h : Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON ∨ IsCentralProductA6Covers W ∨
      IsA6CoverTimesA5 W) : 3 ^ 4 ∣ Nat.card W := by
  rcases h with hON | hcp | ha5
  · obtain ⟨hc, ⟨e⟩⟩ := hON
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W), hc,
      Nat.card_congr e.toEquiv]
    have h4 : 3 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
      have h := CFSG.RankThree.Native.factorization_card_ON
      have hd := Nat.ordProj_dvd (Nat.card CFSG.Blueprint.NativeSporadic.ON) 3
      rwa [h] at hd
    exact h4.mul_right 3
  · rw [card_of_isCentralProductA6Covers hcp]
    norm_num
  · obtain ⟨U, V, -, hVn, hint, hUV, hU, ⟨φ⟩⟩ := ha5
    have hN : U ≤ Subgroup.normalizer (V : Set W) := by
      rw [@Subgroup.normalizer_eq_top _ _ V hVn]
      exact le_top
    have key := card_sup_mul_card_inf hN
    rw [hUV, hint, Subgroup.card_top, Subgroup.card_bot, HJRes2.card_of_isTripleCover_six hU,
      Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at key
    rw [show Nat.card W = 64800 by omega]
    norm_num

section Certificates

set_option maxHeartbeats 2000000 in
theorem step148HJNormalInnerA6Cent2_holdsQ
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) :
    Step148HJNormalInnerA6Cent2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hYB6 hdYB hbc hXJ h3t hdA' hdZα
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hJp : Group.IsPerfect ↥(img148 A Y J) := by
    have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
    exact isPerfect_img148 hJM
  have hJc : IsComponent (img148 A Y J) := isComponent_img148_of_three_dvd hY.2 hJ h3J
  have hJcard : Nat.card (img148 A Y J) = 1080 := HJRes2.card_of_isTripleCover_six hJ6
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [hJcard]; norm_num
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAp0 : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hbJ := HJRes2.le_centralizer_of_theta hYdM heq hJθ hbA hbc.2
  have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hBJ : img148 A Y B ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hc.1]
    have hS' : ({b, d} : Set G) ⊆ (Y ⊔ A : Subgroup G) := by
      rintro g (rfl | rfl)
      · exact Subgroup.mem_sup_right hbA
      · exact Subgroup.mem_sup_right hdA
    refine img148_closure_le_centralizer hS' fun g hg => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hbJ hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hdJ hx)
  obtain ⟨hBA, -, hmax⟩ := img148_hyperplane_max (Y := Y) hA hB
  obtain ⟨j, hjA, hjJ, hjnc⟩ := exists_noncentral_mem_of_tripleCover hJ6 hJp hA3 hF3 hAJα hBJ hBA
    hmax
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hjB : j ∉ img148 A Y B := fun hjB' => by
    obtain ⟨y, hy, hjy⟩ := hjnc
    exact hjy (Subgroup.mem_centralizer_iff.mp (hBJ hjB') y hy).symm
  have hAeq : img148 A Y B ⊔ Subgroup.zpowers j = img148 A Y A := by
    rcases hmax _ le_sup_left (sup_le hBA (Subgroup.zpowers_le.mpr hjA)) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers j ≤ _) (Subgroup.mem_zpowers j)) hjB
    · exact h
  have hCD : img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
      img148 A Y A ⊓ img148 A Y J = img148 A Y A := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    calc img148 A Y A = img148 A Y B ⊔ Subgroup.zpowers j := hAeq.symm
      _ ≤ _ := sup_le_sup (le_inf hBA hBJ)
          (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hjA, hjJ⟩))
  have hCB : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = img148 A Y B := by
    rcases hmax _ (le_inf hBA hBJ) inf_le_left with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hjy⟩ := hjnc
      have hjC : j ∈ img148 A Y A ⊓
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [h]; exact hjA
      exact hjy (Subgroup.mem_centralizer_iff.mp hjC.2 y hy).symm
  have hXle := img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hjJ hjA hjnc hCD
  have h3YB : 3 ∣ Nat.card YB := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
      HJRes2.card_of_isTripleCover_six hYB6]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hYBα : img148 A Y YB = img148 A Y J := by
    refine Subgroup.eq_of_le_of_card_ge (heq ▸ img148_mono hYBYd) ?_
    have h1 := card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      h3YB
    rw [HJRes2.card_of_isTripleCover_six hYB6] at h1
    rw [hJcard]
    exact h1
  have hJb : img148 A Y J ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (hYBC.trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)))
    exact Set.singleton_subset_iff.mpr hbB
  have hAV : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ img148 A Y J →
      j ∈ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro V hV hjV
    rw [← hAeq]
    refine sup_le (fun x hx => Subgroup.centralizer_le_normalizer _ ?_)
      (Subgroup.zpowers_le.mpr hjV)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hBJ hx) w (hV hw)
  have hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) :=
    le_of_forall_commutator_le_tripleCover hJ6 hJp hjJ hj3 hjnc fun V hV hV3 hjV =>
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hjA)).trans
        (commutator_le_img148_deltaZero_of_point h142 hS hY hc.2.1 V (hV.trans hJb) hV3
          (hAV V hV hjV))
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hXeq : img148 A Y (deltaZero A (lB A) Y) =
      img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :=
    le_antisymm hXle (sup_le hJX (hZle.trans inf_le_left))
  have hZC : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hZne : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≠ ⊥ := fun h0 =>
    hXJ (by rw [hXeq, h0, sup_bot_eq])
  have hUV : ∀ u ∈ img148 A Y J, ∀ v ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)),
      u * v = v * u := fun u hu v hv => (Subgroup.mem_centralizer_iff.mp (hZC hv) u hu)
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYBJ hdYB, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA.1.2 hdA (Subgroup.one_mem A) (by rw [← hdαdef, h]; rfl)
  have hdZ : ∀ v ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)), dα * v = v * dα :=
    fun v hv => hUV dα hdJα v hv
  have hXd : img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {dα} := by
    rw [hXeq]
    refine sup_le hdJ fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hdZ x hx).symm
  have hJZd : img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.zpowers dα := by
    intro x hx
    set d' : ↥(img148 A Y J) := ⟨dα, hdJα⟩ with hd'
    have hd'Z : d' ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hdJ g.2))
    have hd'1 : d' ≠ 1 := fun h => hdα1 (congrArg Subtype.val h)
    have hcen : Subgroup.zpowers d' = Subgroup.center ↥(img148 A Y J) :=
      zpowers_eq_of_card_three hJ6.1 hd'Z hd'1
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hUV g g.2 x hx.2)
    rw [← hcen] at hxZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa [hd'] using congrArg Subtype.val hk⟩

  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  set Xα := img148 A Y (deltaZero A (lB A) Y) with hXα
  have hdZα' : dα ∈ Zα := hdZα
  have hJZ : img148 A Y J ⊓ Zα = Subgroup.zpowers dα :=
    le_antisymm hJZd (Subgroup.zpowers_le.mpr ⟨hdJα, hdZα'⟩)
  have hJNZ : img148 A Y J ≤ Subgroup.normalizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUV u hu v hv).symm
  have hcardX : Nat.card Xα * 3 = 1080 * Nat.card Zα := by
    have key := card_sup_mul_card_inf hJNZ
    rw [← hXeq, hJZ, hJcard, Nat.card_zpowers, orderOf_eq_prime (hA3 _ hdαA) hdα1] at key
    exact key
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  let := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ)
  have h4Z : 3 ^ 4 ∣ Nat.card Zα := by
    rw [← Nat.card_congr e.toEquiv]
    exact pow_four_dvd_card_of_types h3t.2
  have h6X : 3 ^ 6 ∣ Nat.card Xα := by
    obtain ⟨k, hk⟩ := h4Z
    have : Nat.card Xα = 360 * Nat.card Zα := by omega
    rw [this, hk]
    exact ⟨40 * k, by ring⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAab' : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hdec := HJRes2.deltaZero_eq_sup_of_le_centralizer hY.2 hAp hAab' hdA hd3 hXd
  set O := pPrimeCoreOf 3 (deltaZero A (lB A) Y) with hO
  set D := deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hD
  have hOY : O ≤ Y ⊔ A := ((pPrimeCoreOf_le 3 _).trans (deltaZero_le Y)).trans le_sup_left
  have hDY : D ≤ Y ⊔ A := ((deltaZero_le _).trans inf_le_left).trans le_sup_left
  have hXsup : Xα = img148 A Y O ⊔ img148 A Y D := by
    rw [hXα, hdec, img148_sup hOY hDY]
  have hDO : D ≤ Subgroup.normalizer (O : Set G) :=
    (deltaZero_mono inf_le_left).trans (le_normalizer_pPrimeCoreOf 3 _)
  have hdiv0 := card_sup_dvd_card_mul (img148_le_normalizer (A := A) (Y := Y) hDO)
  have hdiv : Nat.card ↥Xα ∣ Nat.card ↥(img148 A Y D) * Nat.card ↥(img148 A Y O) := by
    rw [hXsup, sup_comm (img148 A Y O) (img148 A Y D)]
    exact hdiv0
  have hO3 : ¬ 3 ∣ Nat.card (img148 A Y O) := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (card_img148_dvd hOY))
  have h6D : 3 ^ 6 ∣ Nat.card D := by
    have h1 := h6X.trans hdiv
    rw [mul_comm] at h1
    exact (pow_dvd_of_pow_dvd_mul_left hO3 h1).trans (card_img148_dvd hDY)
  have hDΔ : D ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
    (deltaZero_mono inf_le_right).trans (deltaZero_le_delta _)
  have hdΩ : Subgroup.zpowers d ∉ omegaA A :=
    Sec15.Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48
      (Item148HJ.sec14Std_of_isLBConfig hS hc) (Item148HJ.j2_of_isLBConfig hc) hdA hd1
      hc.2.2.2.2
  exact not_pow_six_dvd_card_deltaQ hS (h143 G A c L hS) hdA hd1 hdΩ
    (h6D.trans (Subgroup.card_dvd_of_le hDΔ))

theorem step148HJNormalInnerA6_of_closedQ
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) :
    Step148HJNormalInnerA6 :=
  step148HJNormalInnerA6_of_cent h142 h134 h48
    (step148HJNormalInnerA6Cent_of_cent2' (step148HJNormalInnerA6Cent2_holdsQ h142 h134 h48 h143))

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
