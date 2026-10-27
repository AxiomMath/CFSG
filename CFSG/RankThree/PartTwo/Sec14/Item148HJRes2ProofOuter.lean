module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofA6
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofON
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofImg
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes2

open Main148


theorem outer_facts {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B : Subgroup G}
    (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    {Y YB Yd : Subgroup G} (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6))) :
    Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∧
      d ∈ YB ∧ b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) := by
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨hbB, -, -, -, hCB⟩ := lbConfig_points hB hA.2 hc
  have hb : b ∈ A := hB.1 hbB
  obtain ⟨hYBt, hbc⟩ := isTripleCover_yb_of_isTripleCover hbB (hA.1.2 b hb) hCB hYB htype hYd
    hYBYd (hAYd hb) hA6
  exact ⟨hYBt, mem_yb_of_isTripleCover h hB hc hYB hYBt hle, hb, hbc⟩

end HJRes2

open HJRes2 HJRes148 Main148

section Certificates


theorem step148HJNormalOuterON_holds :
    Step148HJNormalOuterON := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hON
  exfalso
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hA.1.2 d hd
  obtain ⟨-, hdYB, -⟩ := outer_facts h hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))
  have h3J : 3 ∣ Nat.card J := h3Yd.trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨hJq, -⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hKle, -, hKp, -, -⟩ := ydAlpha_facts hY.2 hd hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have hdα : alpha148 A Y d hd ∈ img148 A Y Yd :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hd, hdYd, rfl⟩
  set X := img148 A Y J with hX
  set g : ↥X := ⟨alpha148 A Y d hd, (hKle hdα).1⟩ with hg
  set K := (img148 A Y Yd).subgroupOf X with hK
  have hKX : img148 A Y Yd ≤ X := hKle.trans inf_le_left
  refine not_mem_of_isPerfect_of_isTripleCover hJq.1 hON (g := g) ?_ ?_ (K := K) ?_ ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hg, ← alpha148_pow hd 3]
    simp only [hd3, Subgroup.coe_one]
    rw [alpha148_eq_mk']
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.one_mem _)
  · intro hgc
    apply hdc
    refine mem_sectionCentralizer_of_le_centralizer hJM hd fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp hgc ⟨x, hx⟩
    exact congrArg Subtype.val this
  · have e : ↥K ≃* ↥(img148 A Y Yd) := Subgroup.subgroupOfEquivOfLe hKX
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : (k : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ Subgroup.centralizer {alpha148 A Y d hd} :=
      (hKle (Subgroup.mem_subgroupOf.mp hk)).2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hk')
  · exact Subgroup.mem_subgroupOf.mpr hdα

@[expose] def Step148HJM24Outer2 : Prop :=
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
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJHJOuter2 : Prop :=
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
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

theorem step148HJM24Outer2_of_outer (h : Step148HJM24Outer) : Step148HJM24Outer2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc _ _ _ hM
  exact h G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hM

theorem step148HJHJOuter2_of_outer (h : Step148HJHJOuter) : Step148HJHJOuter2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc _ _ _ hH _
  exact h G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hH

theorem step148HJM24Outer_of_outer2
    (h : Step148HJM24Outer2) :
    Step148HJM24Outer := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hM
  obtain ⟨h1, h2, h3⟩ := outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  exact h G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc h1 h2 h3 hM

theorem step148HJHJOuter_of_outer2
    (h : Step148HJHJOuter2) :
    Step148HJHJOuter := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hH
  let := ker148_normal hY.2
  obtain ⟨h1, h2, h3⟩ := outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  by_cases hXb : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J ∧ ∃ a ∈ A,
      Subgroup.zpowers a ∈ omegaA A ∧ (∃ La ∈ lA A a,
        Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2)) ∧
      a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)
  · obtain ⟨hXJ, a, ha, haΩ, ⟨La, hLa, hLa2⟩, hac⟩ := hXb
    exact Or.inl (case148Two_of_img148_eq_point hS hY ha haΩ hLa hLa2 hXJ
      (le_centralizer_of_mem_sectionCentralizer ha hac) hH)
  exact h G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc h1 h2 h3 hH fun hXJ a ha haΩ hLa hac =>
      hXb ⟨hXJ, a, ha, haΩ, hLa, hac⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec14
