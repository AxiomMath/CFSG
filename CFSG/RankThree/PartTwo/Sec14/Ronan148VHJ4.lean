module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VHJ3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VDeltaSec
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open CFSG.RankThree.PartTwo.Sec4.Ronan148V (IsSec)
open scoped commutatorElement

theorem isSec_congr_left {S S' X : Type*} [Group S] [Group S'] [Group X] (e : S ≃* S')
    (h : IsSec S X) : IsSec S' X := by
  obtain ⟨H, f, hf⟩ := h
  exact ⟨H, e.toMonoidHom.comp f, e.surjective.comp hf⟩

section Certificates

@[expose] def Step148HJHJCent4 : Prop :=
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
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) →
          Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
            alternatingGroup (Fin 5)) →
          (omegaA A).ncard = 6

theorem step148HJHJCent3_of_cent4Q
    (h143 : Ronan148Q.Item143QS14) (hR : Step148HJHJCent4) : Step148HJHJCent3 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl
  let := ker148_normal hY.2
  refine ⟨fun hXJ => ?_, hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
    hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl⟩
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨hC3, -⟩ := card_inf_centralizer_eq_three_of_j2 hS hY hJ hAJ hYd hYdJ hA6 hθ hdA hdYd
    hdc hJ2
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (fun h0 : (img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = ⊥ => by
    rw [h0, Subgroup.card_bot] at hC3
    omega)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨e, heM, heA, hex⟩ := mem_img148_iff.mp hx.1
  have hxe : alpha148 A Y e heA = x := hex
  have he1 : e ≠ 1 := by
    rintro rfl
    apply hx1'
    rw [← hxe]
    rfl
  have he3 : e ^ 3 = 1 := hA.1.2 e heA
  have hxC : img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y e heA} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, hxe]
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy)
  have heJ : e ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) :=
    HJRes148.mem_sectionCentralizer_of_le_centralizer hJM heA hxC
  refine ⟨e, heA, ?_, heJ⟩
  by_contra heΩ
  have hXd : img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {alpha148 A Y e heA} :=
    hXJ ▸ hxC
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAab' : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hdec := HJRes2.deltaZero_eq_sup_of_le_centralizer hY.2 hAp hAab' heA he3 hXd
  set O := pPrimeCoreOf 3 (deltaZero A (lB A) Y) with hO
  set D := deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({e} : Set G)) with hD
  have hOY : O ≤ Y ⊔ A := ((pPrimeCoreOf_le 3 _).trans (deltaZero_le Y)).trans le_sup_left
  have hDY : D ≤ Y ⊔ A := ((deltaZero_le _).trans inf_le_left).trans le_sup_left
  have hXsup : img148 A Y (deltaZero A (lB A) Y) = img148 A Y O ⊔ img148 A Y D := by
    rw [hdec, img148_sup hOY hDY]
  obtain ⟨φ⟩ := hJ2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hXs : IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) Y)) := by
    rw [hXJ]
    exact MulEquiv.isSimpleGroup φ
  have hOX : img148 A Y O ≤ img148 A Y (deltaZero A (lB A) Y) :=
    img148_mono (pPrimeCoreOf_le 3 _)
  have hXNO : img148 A Y (deltaZero A (lB A) Y) ≤
      Subgroup.normalizer (img148 A Y O : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 _)
  have hO3 : ¬ 3 ∣ Nat.card (img148 A Y O) := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (card_img148_dvd hOY))
  have hObot : img148 A Y O = ⊥ := by
    have hn : ((img148 A Y O).subgroupOf (img148 A Y (deltaZero A (lB A) Y))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr hXNO
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((img148 A Y O).subgroupOf (img148 A Y (deltaZero A (lB A) Y))) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact h.eq_bot_of_le hOX
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      apply hO3
      have h1 := Subgroup.card_dvd_of_le h
      rw [hXJ, KFacts.KS14.card_eq_of_j2 ⟨φ⟩] at h1
      exact (show 3 ∣ 604800 by norm_num).trans h1
  have hXD : img148 A Y (deltaZero A (lB A) Y) = img148 A Y D := by
    rw [hXsup, hObot, bot_sup_eq]
  have hsecD' : IsSec CFSG.Blueprint.NativeSporadic.J2 ↥(D.subgroupOf (Y ⊔ A)) := by
    let g : ↥(D.subgroupOf (Y ⊔ A)) →* ↥(img148 A Y D) :=
      (QuotientGroup.mk' (ker148 A Y)).subgroupMap (D.subgroupOf (Y ⊔ A))
    have hg : Function.Surjective g :=
      (QuotientGroup.mk' (ker148 A Y)).subgroupMap_surjective (D.subgroupOf (Y ⊔ A))
    obtain ⟨ψ⟩ : Nonempty (↥(img148 A Y D) ≃* CFSG.Blueprint.NativeSporadic.J2) := by
      rw [← hXD, hXJ]
      exact ⟨φ⟩
    exact isSec_congr_left ψ (Sec4.Ronan148V.isSec_of_surjective g hg)
  have hsecD : IsSec CFSG.Blueprint.NativeSporadic.J2 ↥D :=
    hsecD'.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDY)
  have hDΔ : D ≤ delta A (lB A) (Subgroup.centralizer ({e} : Set G)) :=
    (deltaZero_mono inf_le_right).trans (deltaZero_le_delta _)
  have hsecΔ : IsSec CFSG.Blueprint.NativeSporadic.J2
      ↥(delta A (lB A) (Subgroup.centralizer ({e} : Set G))) :=
    Sec4.Ronan148V.IsSec.of_subgroup
      (hsecD.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDΔ).symm)
  exact not_isSec_j2_deltaQ hS (h143 G A c L hS) heA he1 heΩ hsecΔ

theorem step148HJHJOuter2_of_cent4Q
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14)
    (hR : Step148HJHJCent4) : Step148HJHJOuter2 :=
  step148HJHJOuter2_of_cent3' h142 h134 h48 (step148HJHJCent3_of_cent4Q h143 hR)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
