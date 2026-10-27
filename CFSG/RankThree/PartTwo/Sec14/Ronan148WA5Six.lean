module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Three
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VOmega6b
import CFSG.RankThree.PartTwo.Sec14.Ronan148VNA6b
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem img148_pPrimeCoreOf_eq_bot {A Y X : Subgroup G} [(ker148 A Y).Normal]
    (hNN : NoNormal3 ↥(img148 A Y X)) : img148 A Y (pPrimeCoreOf 3 X) = ⊥ := by
  have hOZ : img148 A Y (pPrimeCoreOf 3 X) ≤ img148 A Y X := img148_mono (pPrimeCoreOf_le 3 _)
  have hON : img148 A Y X ≤
      Subgroup.normalizer (img148 A Y (pPrimeCoreOf 3 X) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 X)
  have hO3 : ¬ 3 ∣ Nat.card (img148 A Y (pPrimeCoreOf 3 X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_img148
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)))
  have hNorm : ((img148 A Y (pPrimeCoreOf 3 X)).subgroupOf (img148 A Y X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOZ).mpr hON
  have hc3 : ¬ 3 ∣ Nat.card ((img148 A Y (pPrimeCoreOf 3 X)).subgroupOf (img148 A Y X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOZ).toEquiv]
  have h0 := hNN _ hNorm hc3
  rw [Subgroup.subgroupOf_eq_bot] at h0
  have h1 := disjoint_iff.mp h0
  rwa [inf_eq_left.mpr hOZ] at h1

section Certificates

theorem exists_point_of_j2_centPre148
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A (lB A) Y) {B Lb : Subgroup G}
    {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    letI := ker148_normal hY.2
    IsComponent (img148 A Y J) → 3 ∣ Nat.card (img148 A Y J) →
    Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
      CFSG.Blueprint.NativeSporadic.J2) →
    ∃ c₂ : G, Subgroup.zpowers c₂ ∈ omegaA A ∧
      deltaZero A (lB A) (centPre148 A Y J) =
        pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J)) ⊔
          deltaZero A (lB A)
            (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₂ : Set G)) := by
  intro hJc h3Jα hZ2
  let := ker148_normal hY.2
  letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ)
  have hne : img148 A Y J ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h3Jα
    omega
  have hnc := exists_ne_comm_of_isPerfect hJc.1.1 hne
  obtain ⟨-, hcases⟩ := item148At_centPre148 (LB := lB A) hY ih hJY hAJ hnc
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  obtain ⟨ψ2⟩ := hZ2
  have hJ2 : Nat.card ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) =
      604800 := by
    rw [Nat.card_congr (e.trans ψ2).toEquiv]
    exact KFacts.KS14.card_nativeJ2
  have hpt := fun {c₁ : G} (hc₁ : Subgroup.zpowers c₁ ∈ omegaA A) {L₁ : Subgroup G}
      (hL₁ : L₁ ∈ lA A c₁) => j2_of_mem_lA_of_isLBConfig h134 h48 hS hB hc hc₁ hL₁
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6' | h7
  ·
    exfalso
    have hbot : img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
      rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
      exact h1 hgD
    rw [hbot, Subgroup.card_bot] at hJ2
    omega
  ·
    obtain ⟨c₂, hc₂, heq, -⟩ := h2
    exact ⟨c₂, hc₂, heq⟩
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | hcp | ha5 | hAA | hA7 | ⟨_, h37⟩
    · have h81 := Ronan148V.pow_four_dvd_card_of_types (Or.inl hON)
      rw [hJ2] at h81
      norm_num at h81
    · have h81 := Ronan148V.pow_four_dvd_card_of_types (Or.inr (Or.inl hcp))
      rw [hJ2] at h81
      norm_num at h81
    · have h81 := Ronan148V.pow_four_dvd_card_of_types (Or.inr (Or.inr ha5))
      rw [hJ2] at h81
      norm_num at h81
    · obtain ⟨μ⟩ := hAA
      rw [Nat.card_congr μ.toEquiv, Nat.card_prod,
        KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at hJ2
      norm_num at hJ2
    · obtain ⟨μ⟩ := hA7
      rw [Nat.card_congr μ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at hJ2
      norm_num at hJ2
    · obtain ⟨μ⟩ := h37
      rw [Nat.card_congr μ.toEquiv, Sec15.card_projSL_three_seven] at hJ2
      norm_num at hJ2
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
  ·
    exfalso
    obtain ⟨hμ, -, -⟩ := h6'
    obtain ⟨μ⟩ := hμ
    rw [Nat.card_congr μ.toEquiv, Nat.card_prod,
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1, KFacts.KS14.card_nativeJ2] at hJ2
    norm_num at hJ2
  ·
    exfalso
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, -, hL₁, -, -, -, -,
      -, -, -, -, -, -, -, -, hπ₁, -⟩ := h7
    obtain ⟨ψ⟩ := hpt ha₁ hL₁
    exact Sec15.Proof1514.not_isoLThreePi_of_j2 ψ hπ₁

@[expose] def Step148HJA5J2Twelve : Prop :=
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
        Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
          CFSG.Blueprint.NativeSporadic.J2) →
        img148 A Y A ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = img148 A Y B →
        27 ∣ Nat.card ↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ⊓
          Subgroup.centralizer
            (img148 A Y (Subgroup.zpowers d) : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) →
        img148 A Y J ≤ Subgroup.centralizer
          (img148 A Y (Subgroup.zpowers d) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        (omegaA A).ncard ≠ 12

theorem step148HJA5J2Six_of_twelve
    (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJA5J2Twelve) : Step148HJA5J2Six := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne hZ2
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  obtain ⟨φ⟩ := hJ5
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h60 : Nat.card (img148 A Y J) = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [h60]; norm_num
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
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
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hjJ, hj1, hj3, hjC⟩ := exists_pow_eq_one_mem_centralizer hAp hAJα h3Jα
  have hjA : j ∈ img148 A Y A := hF3 j hjC hj3
  have hjZ : ∃ y ∈ img148 A Y J, j * y ≠ y * j := by
    by_contra hcon
    push Not at hcon
    apply hj1
    have hz : (⟨j, hjJ⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon g g.2).symm
    rw [hJZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨hBA, -, hmax⟩ := img148_hyperplane_max (Y := Y) hA hB
  have hCB : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = img148 A Y B := by
    rcases hmax _ (le_inf hBA hBJ) inf_le_left with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hjy⟩ := hjZ
      have hjC' : j ∈ img148 A Y A ⊓
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [h]; exact hjA
      exact hjy (Subgroup.mem_centralizer_iff.mp hjC'.2 y hy).symm
  have hB9 : Nat.card (img148 A Y B) = 9 := by
    rw [card_img148_of_le hA.1.2 hB.1]
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZC : Zα ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((Zα : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  have hAZB : img148 A Y A ⊓ Zα ≤ img148 A Y B := fun x hx => hCB ▸ ⟨hx.1, hZC hx.2⟩
  obtain ⟨ψ⟩ := hZ2
  have hAZ : img148 A Y A ⊓ Zα = img148 A Y B := by
    have hj3' : Nat.card (Subgroup.zpowers j) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hj3 hj1
    rcases card_le_of_le_isE27 hAE (inf_le_left : img148 A Y A ⊓ Zα ≤ img148 A Y A) with
      h | h | h | h
    · exfalso
      refine false_of_j2_of_le hAab hA3 hF3 hj3' ?_ hAN ψ
      rw [Subgroup.eq_bot_of_card_eq _ h]
      exact bot_le
    · exact (false_of_j2_of_le hAab hA3 hF3 h le_rfl hAN ψ).elim
    · exact Subgroup.eq_of_le_of_card_ge hAZB (by rw [h, hB9])
    · exfalso
      have := Subgroup.card_le_of_le hAZB
      rw [h, hB9] at this
      omega
  have hdαZ : alpha148 A Y d hdA ∈ Zα := by
    have h : alpha148 A Y d hdA ∈ img148 A Y A ⊓ Zα := by
      rw [hAZ]
      exact mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
    exact h.2
  have hbαZ : alpha148 A Y b hbA ∈ Zα := by
    have h : alpha148 A Y b hbA ∈ img148 A Y A ⊓ Zα := by
      rw [hAZ]
      exact mem_img148_iff.mpr ⟨b, Subgroup.mem_sup_right hbA, hbB, rfl⟩
    exact h.2
  have hbd : b ∉ Subgroup.zpowers d := by
    intro hb
    have hle' : B ≤ Subgroup.zpowers d := by
      rw [hc.1, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hb
      · exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle'
    rw [Nat.card_zpowers, orderOf_eq_prime (hA.1.2 d hdA) hd1] at h1
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  obtain ⟨c₂, hc₂Ω, hform⟩ :=
    exists_point_of_j2_centPre148 h134 h48 hS hY ih hB hc hJY hAJ hJc h3Jα ⟨ψ⟩
  have hc₂A : c₂ ∈ A := (zpowers_mem_omegaA_iff.mp hc₂Ω).1
  have hc₂3 : Nat.card (Subgroup.zpowers c₂) = 3 := (zpowers_mem_omegaA_iff.mp hc₂Ω).2.1
  have hZs : IsSimpleGroup ↥Zα := isSimpleGroup_of_mulEquiv_j2 ψ
  have h3Z : 3 ∣ Nat.card Zα := by
    rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  have hX₁M : deltaZero A (lB A) (centPre148 A Y J) ≤ Y ⊔ A :=
    (deltaZero_le _).trans (centPre148_le.trans le_sup_left)
  have hO₁M : pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J)) ≤ Y ⊔ A :=
    (pPrimeCoreOf_le 3 _).trans hX₁M
  have hD₂M : deltaZero A (lB A)
      (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₂ : Set G)) ≤ Y ⊔ A :=
    (deltaZero_mono inf_le_left).trans hX₁M
  have hsup : Zα = img148 A Y (pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J))) ⊔
      img148 A Y (deltaZero A (lB A)
        (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₂ : Set G))) := by
    have h1 := congrArg (img148 A Y) hform
    rwa [img148_sup hO₁M hD₂M] at h1
  rw [img148_pPrimeCoreOf_eq_bot (noNormal3_of_isSimpleGroup h3Z), bot_sup_eq] at hsup
  have hZN : Zα ≤ Subgroup.normalizer
      (img148 A Y (Subgroup.zpowers c₂) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hsup]
    exact img148_le_normalizer ((deltaZero_le _).trans inf_le_right)
  have hc₂Z : alpha148 A Y c₂ hc₂A ∉ Zα := by
    intro hcZ
    have hNZ : img148 A Y (Subgroup.zpowers c₂) ≤ Zα :=
      (img148_zpowers_le hc₂A).trans (Subgroup.zpowers_le.mpr hcZ)
    have hN : ((img148 A Y (Subgroup.zpowers c₂)).subgroupOf Zα).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNZ).mpr hZN
    have hcard : Nat.card ((img148 A Y (Subgroup.zpowers c₂)).subgroupOf Zα) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNZ).toEquiv,
        card_img148_of_le hA.1.2 (Subgroup.zpowers_le.mpr hc₂A), hc₂3]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((img148 A Y (Subgroup.zpowers c₂)).subgroupOf Zα) with h | h
    · rw [h, Subgroup.card_bot] at hcard
      omega
    · rw [h, Subgroup.card_top, Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeJ2] at hcard
      omega
  have hW := HJRes148.normalizer_le_normalizer_zpowers_d h134 h48 hS hB hc
  have hcen : Subgroup.centralizer
      (img148 A Y (Subgroup.zpowers d) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
        Subgroup.centralizer {alpha148 A Y d hdA} := by
    have himg : img148 A Y (Subgroup.zpowers d) = Subgroup.zpowers (alpha148 A Y d hdA) :=
      le_antisymm (img148_zpowers_le hdA) (Subgroup.zpowers_le.mpr
        (mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, Subgroup.mem_zpowers d, rfl⟩))
    rw [himg, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h27 := Ronan148V.dvd_card_centralizer_of_normalizer_le hS hY.2 ⟨ψ⟩ hAN hdA hbA hdαZ hd1
    hbαZ hbd hW
  have hJd : img148 A Y J ≤ Subgroup.centralizer
      (img148 A Y (Subgroup.zpowers d) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hcen]
    exact hdJ
  have h12 := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη ⟨φ⟩ hYB5 hbc hXeq hZne ⟨ψ⟩ hAZ (by rwa [hcen]) hJd hZC
  rcases Ronan148V.ncard_omegaA_eq_six_or_twelve_of_j2_factor' h134 h48 hS hB hc hY.2 ⟨ψ⟩ hAN hdA
      hbA hc₂A hdαZ hd1 hW hc.2.1 hbαZ hbd hc₂Ω hc₂Z with h | h
  · exact h
  · exact absurd h h12

theorem step148HJA5Cent2_of_twelve
    (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14)
    (hR : Step148HJA5J2Twelve) : Step148HJA5Cent2 :=
  step148HJA5Cent2_of_j2Six h134 h48 h143 (step148HJA5J2Six_of_twelve h134 h48 hR)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
