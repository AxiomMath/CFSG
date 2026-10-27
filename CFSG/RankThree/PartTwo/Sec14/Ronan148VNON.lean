module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148AInnerCenter
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VNA6b
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VONInner
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pow_five_dvd_card_of_isTripleCover_ON {X : Type}
    [Group X] [Finite X] (h : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) :
    3 ^ 5 ∣ Nat.card X := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv]
  have h4 : 3 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
    have h := CFSG.RankThree.Native.factorization_card_ON
    have hd := Nat.ordProj_dvd (Nat.card CFSG.Blueprint.NativeSporadic.ON) 3
    rwa [h] at hd
  rw [show (3 : ℕ) ^ 5 = 3 ^ 4 * 3 by norm_num]
  exact mul_dvd_mul_right h4 3

section Certificates



theorem img148_deltaZero_le_sup_of_innerON {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (hc : IsLBConfig A B b d Lb) {J Yd : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hYdJ : Yd ≤ J) (hYdt : YdType148 d Yd)
    (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) (hdYd : d ∈ Yd) :
    letI := ker148_normal hY.2
    Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON →
    img148 A Y (deltaZero A (lB A) Y) ≤
      img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
  intro hJON
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  have hJp : Group.IsPerfect ↥(img148 A Y J) := by
    have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
    exact isPerfect_img148 hJM
  have hJc : IsComponent (img148 A Y J) := isComponent_img148_of_three_dvd hY.2 hJ h3J
  obtain ⟨ψ⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model hJp hJON
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA.1.2 hdA (Subgroup.one_mem A) (by rw [← hdαdef, h]; rfl)
  have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hdC : ∀ x ∈ img148 A Y J, dα * x = x * dα := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hdJ hx)).symm
  obtain ⟨⟨j, hjAJ, hjnc⟩, hCD⟩ := exists_noncentral_and_sup_eq_of_ON hAab hA3 hF3 hAE.2 hAJα ψ
    hJON.1 hdαA hdJα hdα1 hdC
  exact img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hjAJ.2 hjAJ.1 hjnc hCD

theorem false_of_le_img148_of_innerON (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A (lB A) Y) {B Lb : Subgroup G}
    {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {J Yd : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hYdJ : Yd ≤ J)
    (hYdt : YdType148 d Yd) (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hdYd : d ∈ Yd) :
    letI := ker148_normal hY.2
    Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON →
    img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
    img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) → False := by
  intro hJON hXJ hJX
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  have hJc : IsComponent (img148 A Y J) := isComponent_img148_of_three_dvd hY.2 hJ h3J
  have h5J : 3 ^ 5 ∣ Nat.card (img148 A Y J) := pow_five_dvd_card_of_isTripleCover_ON hJON
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := (dvd_pow_self 3 (by norm_num)).trans h5J
  have hAE := img148_isE27 (Y := Y) hA
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA.1.2 hdA (Subgroup.one_mem A) (by rw [← hdαdef, h]; rfl)
  have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hXle := img148_deltaZero_le_sup_of_innerON hS hY hB hc hJ hAJ hYdJ hYdt hdc hdYd hJON
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  set Xα := img148 A Y (deltaZero A (lB A) Y) with hXα
  have hXeq : Xα = img148 A Y J ⊔ Zα := le_antisymm hXle (sup_le hJX (hZle.trans inf_le_left))
  have hZC : Zα ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hUV : ∀ u ∈ img148 A Y J, ∀ v ∈ Zα, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp (hZC hv) u hu)
  have hdZ : ∀ v ∈ Zα, dα * v = v * dα := fun v hv => hUV dα hdJα v hv
  have hXd : Xα ≤ Subgroup.centralizer {dα} := by
    rw [hXeq]
    refine sup_le hdJ fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hdZ x hx).symm
  have hJZd : img148 A Y J ⊓ Zα ≤ Subgroup.zpowers dα := by
    intro x hx
    set d' : ↥(img148 A Y J) := ⟨dα, hdJα⟩ with hd'
    have hd'Z : d' ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hdJ g.2))
    have hd'1 : d' ≠ 1 := fun h => hdα1 (congrArg Subtype.val h)
    have hcen : Subgroup.zpowers d' = Subgroup.center ↥(img148 A Y J) :=
      zpowers_eq_of_card_three hJON.1 hd'Z hd'1
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hUV g g.2 x hx.2)
    rw [← hcen] at hxZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa [hd'] using congrArg Subtype.val hk⟩
  have hJZ3 : Nat.card ↥(img148 A Y J ⊓ Zα) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hJZd
    rw [Nat.card_zpowers, orderOf_eq_prime (hA3 _ hdαA) hdα1] at h
    exact h
  have hJNZ : img148 A Y J ≤ Subgroup.normalizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUV u hu v hv).symm
  have hcardX : Nat.card Xα * Nat.card ↥(img148 A Y J ⊓ Zα) =
      Nat.card (img148 A Y J) * Nat.card Zα := by
    have key := card_sup_mul_card_inf hJNZ
    rw [← hXeq] at key
    exact key
  have h6false : ¬ 3 ^ 6 ∣ Nat.card Xα := fun h6X => by
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
  have h9false : 9 ∣ Nat.card Zα → False := by
    intro h9
    apply h6false
    have h1 : 3 ^ 7 ∣ Nat.card Xα * Nat.card ↥(img148 A Y J ⊓ Zα) := by
      rw [hcardX, show (3 : ℕ) ^ 7 = 3 ^ 5 * 9 by norm_num]
      exact mul_dvd_mul h5J h9
    have h3p := (Nat.dvd_prime Nat.prime_three).mp hJZ3
    rcases h3p with h1' | h3'
    · rw [h1', mul_one] at h1
      exact (pow_dvd_pow 3 (by norm_num)).trans h1
    · rw [h3', show (3 : ℕ) ^ 7 = 3 ^ 6 * 3 by norm_num] at h1
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
  rcases centPre148_type_of_hj h134 h48 hS hY ih hB hc hJY hAJ hJc h3Jα with
    h1 | hZ2 | hZ6 | hZ5 | h36
  ·
    have h1' : Zα = ⊥ := h1
    exact hXJ (by rw [hXeq, h1', sup_bot_eq])
  · obtain ⟨ψZ⟩ := hZ2
    apply h9false
    rw [Nat.card_congr ψZ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  · apply h9false
    rw [HJRes2.card_of_isTripleCover_six hZ6]
    norm_num
  ·
    obtain ⟨φZ⟩ := hZ5
    have hZc : Subgroup.center ↥Zα = ⊥ := by
      have hmap := Subgroup.map_center_eq φZ
      rw [center_alternatingGroup_five_eq_bot] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ φZ.injective).mp hmap
    have hint : img148 A Y J ⊓ Zα = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : ↥Zα) ∈ Subgroup.center ↥Zα := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hUV x hx.1 g g.2).symm
      rw [hZc, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    apply h6false
    rw [hint, Subgroup.card_bot, mul_one, Nat.card_congr φZ.toEquiv,
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at hcardX
    rw [hcardX, show (3 : ℕ) ^ 6 = 3 ^ 5 * 3 by norm_num]
    exact mul_dvd_mul h5J (by norm_num)
  · obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
    letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ)
    have hce : Nat.card ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J)))
        = Nat.card Zα := Nat.card_congr e.toEquiv
    apply h9false
    rcases h36 with h3' | h6'
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, htype3⟩ := h3'
      rcases htype3 with hON | hcp | ha5 | h55 | h7 | hL37
      · rw [← hce]
        exact Nat.dvd_trans (by norm_num : (9 : ℕ) ∣ 3 ^ 4) (pow_four_dvd_card_of_types (Or.inl hON))
      · rw [← hce]
        exact Nat.dvd_trans (by norm_num : (9 : ℕ) ∣ 3 ^ 4)
          (pow_four_dvd_card_of_types (Or.inr (Or.inl hcp)))
      · rw [← hce]
        exact Nat.dvd_trans (by norm_num : (9 : ℕ) ∣ 3 ^ 4)
          (pow_four_dvd_card_of_types (Or.inr (Or.inr ha5)))
      · obtain ⟨χ⟩ := h55
        rw [← hce, Nat.card_congr χ.toEquiv, Nat.card_prod,
          KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
        norm_num
      · obtain ⟨χ⟩ := h7
        rw [← hce, Nat.card_congr χ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
        norm_num
      · obtain ⟨_, ⟨χ⟩⟩ := hL37
        rw [← hce, Nat.card_congr χ.toEquiv, Sec15.card_projSL_three_seven]
        norm_num
    · obtain ⟨⟨χ⟩, -, -⟩ := h6'
      rw [← hce, Nat.card_congr χ.toEquiv, Nat.card_prod,
        KFacts.KS14.card_alternatingGroup_five_seven_ten.1, KFacts.KS14.card_nativeJ2]
      norm_num

@[expose] def Step148HJNormalInnerONCent3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
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
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON → d ∈ Yd →
        img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
        ¬ img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) →
        img148 A Y (deltaZero A (lB A) Y) ≤
          img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) →
        ((Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) Y))
              CFSG.Blueprint.NativeSporadic.ON ∨
            IsCentralProductA6Covers ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
            IsA6CoverTimesA5 ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
            Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
              alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
            Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 7)) ∨
            (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))) ∨
          Case148Two A (lB A) Y)

theorem step148HJNormalInnerONCent2_of_cent3 (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) (hR : Step148HJNormalInnerONCent3) :
    Ronan148A.Step148HJNormalInnerONCent2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ
  let := ker148_normal hY.2
  by_cases hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y)
  · exact (false_of_le_img148_of_innerON h134 h48 h143 hS hY ih hB hc hJ hAJ hYdJ hYdt hdc hdYd
      hJON hXJ hJX).elim
  · exact hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ hJX
      (img148_deltaZero_le_sup_of_innerON hS hY hB hc hJ hAJ hYdJ hYdt hdc hdYd hJON)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
