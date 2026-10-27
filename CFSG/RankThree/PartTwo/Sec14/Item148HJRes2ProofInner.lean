module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofOuter
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes2

theorem card_theta_quot_le_card_range {K H : Subgroup G} (hHK : H ≤ K) (hHp : Group.IsPerfect H)
    (hHq : IsQuasisimple (↥H ⧸ aschbacherSolvableCore 3 ↥H)) (h3H : 3 ∣ Nat.card H) :
    Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H) ≤
      Nat.card ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)).comp
        (Subgroup.inclusion hHK)).range := by
  set ι := (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)).comp (Subgroup.inclusion hHK)
    with hι
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hker3 : ¬ 3 ∣ Nat.card ι.ker := by
    intro h3
    apply hθ3
    refine h3.trans ?_
    have hle : ι.ker.map (Subgroup.inclusion hHK) ≤ aschbacherSolvableCore 3 ↥K := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : ι y = 1 := hy
      rw [hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
      exact hy'
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK)]
    exact Subgroup.card_dvd_of_le hle
  have hrp : Group.IsPerfect ι.range :=
    Group.IsPerfect.ofSurjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective
  have hker' : ι.rangeRestrict.ker = ι.ker := MonoidHom.ker_rangeRestrict ι
  rcases Res148.ker_le_theta_or_subsingleton ι.rangeRestrict ι.rangeRestrict_surjective hrp hHq
      (by rw [hker']; exact hker3) with hle | hsub
  · rw [hker'] at hle
    have e1 : Nat.card ↥H = Nat.card ι.range * Nat.card ι.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ι.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv]
    have e2 : Nat.card ↥H = Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H) *
        Nat.card (aschbacherSolvableCore 3 ↥H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hk : Nat.card ι.ker ≤ Nat.card (aschbacherSolvableCore 3 ↥H) :=
      Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card (aschbacherSolvableCore 3 ↥H) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H) * Nat.card (aschbacherSolvableCore 3 ↥H)
        = Nat.card ι.range * Nat.card ι.ker := by rw [← e1, ← e2]
      _ ≤ Nat.card ι.range * Nat.card (aschbacherSolvableCore 3 ↥H) := Nat.mul_le_mul_left _ hk
  · exfalso
    apply hker3
    have htop : ι.ker = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have := Subsingleton.elim (ι.rangeRestrict y) 1
      exact congrArg Subtype.val this
    rw [htop, Subgroup.card_top]
    exact h3H

theorem forall_mem_theta_of_card_le {K H : Subgroup G} {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hHK : H ≤ K) (hHp : Group.IsPerfect H)
    (hHq : IsQuasisimple (↥H ⧸ aschbacherSolvableCore 3 ↥H)) (h3H : 3 ∣ Nat.card H)
    (hcard : Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) ≤
      Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H))
    (hbH : ∀ y ∈ H, b * y = y * b) :
    ∀ y ∈ K, b * y * b⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  set θ := aschbacherSolvableCore 3 ↥K with hθ
  set ι := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hHK) with hι
  have h1 := card_theta_quot_le_card_range hHK hHp hHq h3H
  have htop : ι.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) (hcard.trans h1))
  set σ := GroupTheory.thetaQuotientConj 3 K ⟨b, hbK⟩ with hσ
  have hσ1 : σ = 1 := by
    ext q
    have hq : q ∈ ι.range := htop ▸ Subgroup.mem_top q
    obtain ⟨y, rfl⟩ := hq
    rw [MulAut.one_apply, hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hσ,
      GroupTheory.thetaQuotientConj_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
    change b * (y : G) * b⁻¹ = y
    rw [hbH y y.2, mul_inv_cancel_right]
  intro y hy
  exact (GroupTheory.thetaQuotientConj_eq_one_iff 3 K ⟨b, hbK⟩).mp hσ1 y hy

theorem card_of_isTripleCover_six {X : Type*} [Group X]
    (h : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr e.toEquiv, hc, KFacts.KS14.card_alternatingGroup_six]

theorem card_of_isTripleCover_ON {X : Type*} [Group X]
    (h : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) :
    Nat.card X = 3 * 460815505920 := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr e.toEquiv, hc, CFSG.Sporadic.ON.card_ON_eq]

theorem a5_facts {Y B YB Yd : Subgroup G} {b : G} (hbB : b ∈ B)
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    (hYBYd : YB ≤ Yd) (hbYd : b ∈ Subgroup.normalizer (Yd : Set G))
    (hA5 : Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* alternatingGroup (Fin 5))) :
    Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)) ∧
      ∀ y ∈ Yd, b * y * b⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Yd := by
  have h3YB : 3 ∣ Nat.card YB := by
    rcases htype with hA6' | hA5'
    · exact three_dvd_card_of_ydType148 (d := b) (Or.inr (Or.inl hA6'))
    · exact three_dvd_card_of_ydType148 (d := b) (Or.inl hA5')
  have hYBp : Group.IsPerfect YB := isPerfect_of_mem_thetaComponentsIn hYB
  have hYBq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hbH : ∀ y ∈ YB, b * y = y * b := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hYBC hy).2 b hbB
  have h60 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 60 := by
    obtain ⟨φ⟩ := hA5
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have hle := card_theta_quot_le_card_range hYBYd hYBp hYBq h3YB
  have hrange : Nat.card ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Yd)).comp
      (Subgroup.inclusion hYBYd)).range ≤ 60 :=
    h60 ▸ Subgroup.card_le_card_group _
  have hYB5 : Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)) := by
    rcases htype with hA6' | hA5'
    · exfalso
      have := card_of_isTripleCover_six hA6'
      omega
    · exact hA5'
  refine ⟨hYB5, forall_mem_theta_of_card_le hbYd hYBYd hYBp hYBq h3YB ?_ hbH⟩
  obtain ⟨φ⟩ := hYB5
  rw [h60, Nat.card_congr φ.toEquiv]
  exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1.ge

end HJRes2

open HJRes2 HJRes148 Main148

section Certificates

@[expose] def Step148HJNormalInnerA6 : Prop :=
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
        Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJNormalInnerON : Prop :=
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
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJA5Inner2 : Prop :=
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
        Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)) →
        b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

theorem step148HJNormalInner_of_res2
    (hA6 : Step148HJNormalInnerA6)
    (hON : Step148HJNormalInnerON) : Step148HJNormalInner := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJt
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨η⟩ := hη
  rcases hJt with hJ6 | hJON
  · have hYd6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)
        (alternatingGroup (Fin 6)) := KFacts.KS14.isTripleCover_congr η.symm hJ6
    obtain ⟨h1, h2, h3⟩ := outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hYd6
    by_cases hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J
    · exact Or.inl (case148Two_of_img148_eq_b hS hY hB hc hXJ
        (fun hb => le_centralizer_of_theta hYdM heq hJθ hb h3.2) (Or.inl hJ6))
    exact hA6 G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd
      hYd hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ hJ6 h1 h2 h3 hXJ
  · have hcard : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 3 * 460815505920 := by
      rw [Nat.card_congr η.toEquiv]
      exact card_of_isTripleCover_ON hJON
    have hdYd : d ∈ Yd := by
      rcases hYdt with ⟨⟨φ⟩⟩ | hA6' | ⟨hdYd, -⟩
      · exfalso
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at hcard
        omega
      · exfalso
        rw [card_of_isTripleCover_six hA6'] at hcard
        omega
      · exact hdYd
    by_cases hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J
    · exact Or.inr (Or.inl (case148Three_of_img148_eq_d hS hY hB hc hXJ
        (fun hd => le_centralizer_of_mem_sectionCentralizer hd hdc) hJON))
    exact hON G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd
      hYd hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ hJON hdYd hXJ

theorem step148HJA5Inner_of_inner2
    (h : Step148HJA5Inner2) : Step148HJA5Inner := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, -, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨η⟩ := hη
  obtain ⟨φ⟩ := hJ5
  obtain ⟨h1, h2⟩ := a5_facts hbB hYB htype hYBYd (hAYd (hB.1 hbB)) ⟨η.trans φ⟩
  by_cases hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J
  · exact Or.inl (case148Two_of_img148_eq_b hS hY hB hc hXJ
      (fun hb => le_centralizer_of_theta hYdM heq hJθ hb h2) (Or.inr (Or.inl ⟨φ⟩)))
  exact h G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ ⟨φ⟩ h1 ⟨hB.1 hbB, h2⟩ hXJ

end Certificates

end CFSG.RankThree.PartTwo.Sec14
