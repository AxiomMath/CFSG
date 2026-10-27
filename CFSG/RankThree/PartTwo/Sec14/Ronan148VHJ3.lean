module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJ2
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VHJOver
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VON
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VL37
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJNine
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJSix
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open scoped commutatorElement

section Certificates


@[expose] def Step148HJHJCent3 : Prop :=
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
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → ∀ _hAJ : A ≤ Subgroup.normalizer (J : Set G),
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        (img148 A Y (deltaZero A (lB A) Y) = img148 A Y J → ∀ a ∈ A,
          Subgroup.zpowers a ∈ omegaA A →
          (∃ La ∈ lA A a,
            Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2)) →
          a ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) →
        (img148 A Y (deltaZero A (lB A) Y) = img148 A Y J →
          ∃ a ∈ A, Subgroup.zpowers a ∈ omegaA A ∧
            a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) ∧
        (img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) →
          Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
            alternatingGroup (Fin 5)) →
          (omegaA A).ncard = 6)

theorem step148HJHJCent_of_cent3
    (hON : ∀ (W : Type) [Group W], Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON →
      ∃ x : W, x ^ 3 = 1 ∧ x ∉ Subgroup.center W)
    (hL37 : ∀ _ : Fact (Nat.Prime 7),
      NoNine3 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))
    (hR : Step148HJHJCent3) : Step148HJHJCent := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl
  let := ker148_normal hY.2
  obtain ⟨hres2, hres3⟩ := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc
    hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl
  refine ⟨?_, hres2, hres3⟩
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  obtain ⟨hC3, hCD⟩ := card_inf_centralizer_eq_three_of_j2 hS hY hJ hAJ hYd hYdJ hA6 hθ hdA hdYd
    hdc hJ2
  obtain ⟨φ⟩ := hJ2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, -⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by
    rw [KFacts.KS14.card_eq_of_j2 ⟨φ⟩]
    norm_num
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAp : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZC : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  have hAZC : img148 A Y A ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun x hx => ⟨hx.1, hZC hx.2⟩
  have hEZ : img148 A Y A ⊓ img148 A Y J ≤
      Subgroup.centralizer ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :
        Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx.2).symm
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  refine ⟨fun h3' => ?_, fun h6' => ?_⟩
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htype3⟩ := h3'
    rcases htype3 with hON' | hcp | ha5 | h55 | h7 | hL37'
    · obtain ⟨x, hx3, hxZ⟩ := hON _ hON'
      exact false_of_centralNoncentral_of_le hAp hF3 hC3 hCD hEZ hAZC hAN
        (centralNoncentral_congr e ⟨by rw [hON'.1], x, hx3, hxZ⟩)
    · exact false_of_centralNoncentral_of_le hAp hF3 hC3 hCD hEZ hAZC hAN
        (centralNoncentral_congr e (IsCentralProductA6Covers.central_noncentral hcp))
    · exact false_of_centralNoncentral_of_le hAp hF3 hC3 hCD hEZ hAZC hAN
        (centralNoncentral_congr e (IsA6CoverTimesA5.central_noncentral ha5))
    · obtain ⟨χ⟩ := h55
      obtain ⟨h9, hexp⟩ :=
        noNine_subgroup (noNine_congr (e.symm.trans χ).symm noNine_alternating_five_sq)
      exact false_of_exp_three_of_le hAp hF3 hC3 hCD hEZ hAZC hAN h9 hexp
    · obtain ⟨χ⟩ := h7
      obtain ⟨h9, hexp⟩ :=
        noNine_subgroup (noNine_congr (e.symm.trans χ).symm noNine_alternatingGroup_seven)
      exact false_of_exp_three_of_le hAp hF3 hC3 hCD hEZ hAZC hAN h9 hexp
    · obtain ⟨hf7, ⟨χ⟩⟩ := hL37'
      obtain ⟨h9, hexp⟩ :=
        noNine_subgroup (noNine_congr (e.symm.trans χ).symm (hL37 hf7))
      exact false_of_exp_three_of_le hAp hF3 hC3 hCD hEZ hAZC hAN h9 hexp
  ·
    obtain ⟨⟨χ⟩, -, -⟩ := h6'
    obtain ⟨V, hVZ, ⟨ψV⟩, hVN⟩ := exists_j2_factor_le_normalizer (e.symm.trans χ)
    exact false_of_j2_of_le hAab hA3 hF3 hC3 (fun x hx => hAZC ⟨hx.1, hVZ hx.2⟩)
      (fun a ha => hVN a (hAN ha)) ψV

theorem step148HJHJOuter2_of_cent3
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hK : KHJPerfectOver)
    (hON : ∀ (W : Type) [Group W], Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON →
      ∃ x : W, x ^ 3 = 1 ∧ x ∉ Subgroup.center W)
    (hL37 : ∀ _ : Fact (Nat.Prime 7),
      NoNine3 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))
    (hR : Step148HJHJCent3) : Step148HJHJOuter2 :=
  step148HJHJOuter2_of_cent h142 h134 h48 hK (step148HJHJCent_of_cent3 hON hL37 hR)

theorem step148HJHJOuter2_of_cent3'
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJHJCent3) :
    Step148HJHJOuter2 :=
  step148HJHJOuter2_of_cent3 h142 h134 h48 khjPerfectOver_holds
    (fun _ _ h => Sec4.Ronan148V.exists_noncentral_of_isTripleCover_ON h)
    (fun _ => Sec4.Ronan148V.noNine_projSL_three_seven) hR

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
