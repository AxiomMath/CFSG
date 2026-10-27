module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JA5
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JCore
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148

variable {G : Type} [Group G] [Finite G]

theorem j2_of_mem_lA_of_isLBConfig
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {c₁ : G} (hc₁ : Subgroup.zpowers c₁ ∈ omegaA A) {L₁ : Subgroup G} (hL₁ : L₁ ∈ lA A c₁) :
    Nonempty (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁ ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hall := allPointsHJ_of_isLBConfig h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415
    (KFacts.KS14.center_nativeJ2_eq_bot h415) hS hc hB
  obtain ⟨L', hL', hJ'⟩ := hall c₁ hc₁
  have hD' : Sec13Data G A c₁ L' :=
    { hS.toSec13Data with zpowers_mem_omegaA := hc₁, mem_lA := hL' }
  have hsing := lA_eq_singleton_of_j2_point hD' hJ'
  rw [hsing, Set.mem_singleton_iff] at hL₁
  rw [hL₁]
  exact hJ'

section Certificates


@[expose] def Step148HJA5Cent : Prop :=
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
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → ∀ hAJ : A ≤ Subgroup.normalizer (J : Set G),
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)) →
        b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        img148 A Y (deltaZero A (lB A) Y) =
          img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) →
        img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≠ ⊥ →
        (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
          ¬ Case148Three A (lB A) (centPre148 A Y J) ∧
            ¬ Case148Six A (lB A) (centPre148 A Y J)) ∧
          (Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
              CFSG.Blueprint.NativeSporadic.J2) → (omegaA A).ncard = 6)

theorem step148HJA5Type_of_cent
    (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJA5Cent) : Step148HJA5Type := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne
  let := ker148_normal hY.2
  obtain ⟨hno, h6⟩ := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
    hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  obtain ⟨φ⟩ := hJ5
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, -⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h60 : Nat.card (img148 A Y J) = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [h60]; norm_num
  have hne : img148 A Y J ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h60
    omega
  have hnc := exists_ne_comm_of_isPerfect hJc.1.1 hne
  obtain ⟨-, hcases⟩ := item148At_centPre148 (LB := lB A) hY ih hJY hAJ hnc
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  have hpt := fun {c₁ : G} (hc₁ : Subgroup.zpowers c₁ ∈ omegaA A) {L₁ : Subgroup G}
      (hL₁ : L₁ ∈ lA A c₁) => j2_of_mem_lA_of_isLBConfig h134 h48 hS hB hc hc₁ hL₁
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6' | h7
  ·
    exfalso
    apply hZne
    have hcore := pPrimeCoreOf_centPre148_eq_of_isComponent hY.2 hJY hJc h3Jα
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
    have h := h1 hgD
    rwa [hcore] at h
  ·
    obtain ⟨c₁, hc₁, -, L₁, hL₁, hcase⟩ := h2
    obtain ⟨ψ⟩ := hpt hc₁ hL₁
    rcases hcase with hχ | ⟨hL, -⟩ | ⟨p, f, e', hp, -, -, hπ, -⟩ | ⟨-, hiv⟩
    ·
      obtain ⟨χ⟩ := hχ
      have hZJ : Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
          CFSG.Blueprint.NativeSporadic.J2) := ⟨e.symm.trans (χ.trans ψ)⟩
      exact Or.inr (Or.inr ⟨hZJ, h6 hZJ⟩)
    ·
      exfalso
      rcases hL with hμ | ⟨_, hμ⟩ | ⟨_, hμ⟩
      · obtain ⟨μ⟩ := hμ
        exact KFacts.KS14.ks17J2NotList.2.2.false (ψ.symm.trans μ)
      · obtain ⟨μ⟩ := hμ
        exact KFacts.KS14.not_isLThreeEpsAt_j2 5 2 (Or.inl ⟨ψ.symm.trans μ⟩)
      · obtain ⟨μ⟩ := hμ
        exact KFacts.KS14.not_isLThreeEpsAt_j2 5 1 (Or.inr ⟨by norm_num, ⟨ψ.symm.trans μ⟩⟩)
    ·
      exact absurd hπ (Sec15.Proof1514.not_isoLThreePi_of_j2 ψ)
    ·
      rcases hiv with h6c | hχ
      · exact Or.inr (Or.inl (KFacts.KS14.isTripleCover_congr e h6c))
      · obtain ⟨χ⟩ := hχ
        exact Or.inl ⟨e.symm.trans χ⟩
  · exact absurd h3 hno.1
  ·
    exfalso
    obtain ⟨-, ⟨c₁, L₁, hc₁, hL₁, hμ⟩, -⟩ := h4
    obtain ⟨μ⟩ := hμ
    obtain ⟨ψ⟩ := hpt hc₁ hL₁
    exact KFacts.KS14.ks17J2NotList.2.1.false (ψ.symm.trans μ)
  ·
    exfalso
    obtain ⟨c₁, -, L₁, n, m, hc₁, hL₁, -, -, -, -, -, -, hε, -⟩ := h5
    obtain ⟨ψ⟩ := hpt hc₁ hL₁
    rcases hε with hμ | ⟨h2, hμ⟩
    · obtain ⟨μ⟩ := hμ
      exact KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (Or.inl ⟨ψ.symm.trans μ⟩)
    · obtain ⟨μ⟩ := hμ
      exact KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (Or.inr ⟨h2, ⟨ψ.symm.trans μ⟩⟩)
  · exact absurd h6' hno.2
  ·
    exfalso
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, -, hL₁, -, -, -, -,
      -, -, -, -, -, -, -, -, hπ₁, -⟩ := h7
    obtain ⟨ψ⟩ := hpt ha₁ hL₁
    exact Sec15.Proof1514.not_isoLThreePi_of_j2 ψ hπ₁

theorem step148HJA5Inner2_of_cent
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJA5Cent) :
    Step148HJA5Inner2 :=
  step148HJA5Inner2_of_type h142 h134 h48 (step148HJA5Type_of_cent h134 h48 hR)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
