module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VHJ4
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VOmega6
import CFSG.RankThree.PartTwo.Sec14.Ronan148VA5Inner
import CFSG.RankThree.PartTwo.Sec14.Ronan148VA5Norm
import CFSG.RankThree.PartTwo.Sec14.Ronan148VNA6b
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_le_simple {Q : Type*} [Group Q] [Finite Q] {Z N : Subgroup Q}
    (hs : IsSimpleGroup ↥Z) (hNZ : N ≤ Z) (hZN : Z ≤ Subgroup.normalizer (N : Set Q))
    (h3Z : 3 ∣ Nat.card Z) (h3N : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  haveI : (N.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNZ).mpr hZN
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Z) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNZ
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd (h3Z.trans (Subgroup.card_dvd_of_le h)) h3N

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem alpha148_mem_of_a5_point {Jq Zq : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x)
    (hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1)
    (hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A)
    (hC3 : Nat.card ↥(img148 A Y A ⊓
      Subgroup.centralizer (Jq : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3)
    (hCD : img148 A Y A ⊓ Subgroup.centralizer (Jq : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
      img148 A Y A ⊓ Jq = img148 A Y A)
    (hJZ : Jq ⊓ Subgroup.centralizer (Jq : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥)
    (hZJ : Zq ≤ Subgroup.centralizer (Jq : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAN : img148 A Y A ≤ Subgroup.normalizer (Zq : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (ψ : ↥Zq ≃* alternatingGroup (Fin 5)) {x : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hx : x ∈ img148 A Y A)
    (hN : Zq ≤ Subgroup.normalizer (Subgroup.zpowers x : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    x ∈ Jq := by
  have hne : img148 A Y A ⊓ Subgroup.centralizer (Jq : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hC3
    omega
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he1' : (e : ↥(Y ⊔ A) ⧸ ker148 A Y) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hC : img148 A Y A ⊓ Subgroup.centralizer (Jq : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.zpowers (e : ↥(Y ⊔ A) ⧸ ker148 A Y) :=
    (zpowers_eq_of_card_three hC3 e.2 he1').symm
  have heZ : (e : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ Zq :=
    mem_of_inner_a5 hAab hA3 hF3 hC hCD hZJ hAN ψ
  have he3 : (e : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := hA3 _ e.2.1
  have hnorm : img148 A Y A ⊓ Jq ≤ Subgroup.normalizer
      (Subgroup.zpowers (e : ↥(Y ⊔ A) ⧸ ker148 A Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers (e : ↥(Y ⊔ A) ⧸ ker148 A Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (hAab _ e.2.1 _ hy.1) k).eq
  rw [← hCD, hC] at hx
  obtain ⟨n, hn, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hnorm hx
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hJZ' : ∀ u ∈ Jq, ∀ v ∈ Zq, u * v = v * u := fun u hu v hv =>
    Subgroup.mem_centralizer_iff.mp (hZJ hv) u hu
  have hint : Jq ⊓ Zq = ⊥ := by
    rw [eq_bot_iff, ← hJZ]
    exact fun z hz => ⟨hz.1, hZJ hz.2⟩
  have hl := zpow_eq_one_of_normalizer_a5 hJZ' hint ψ heZ he3 hy.2 hN
  rw [hl, one_mul]
  exact hy.2

end Quot

section Certificates


theorem exists_point_of_a5_centPre148
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A (lB A) Y) {B Lb : Subgroup G}
    {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    letI := ker148_normal hY.2
    IsComponent (img148 A Y J) → 3 ∣ Nat.card (img148 A Y J) →
    Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
      alternatingGroup (Fin 5)) →
    ∃ c₁ : G, Subgroup.zpowers c₁ ∈ omegaA A ∧
      deltaZero A (lB A) (centPre148 A Y J) =
        pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J)) ⊔
          deltaZero A (lB A)
            (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G)) := by
  intro hJc h3Jα hZ5
  let := ker148_normal hY.2
  letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ)
  have hne : img148 A Y J ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h3Jα
    omega
  have hnc := exists_ne_comm_of_isPerfect hJc.1.1 hne
  obtain ⟨-, hcases⟩ := item148At_centPre148 (LB := lB A) hY ih hJY hAJ hnc
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  obtain ⟨ψ5⟩ := hZ5
  have h60 : Nat.card ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) =
      60 := by
    rw [Nat.card_congr (e.trans ψ5).toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
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
    rw [hbot, Subgroup.card_bot] at h60
    omega
  ·
    obtain ⟨c₁, hc₁, heq, -⟩ := h2
    exact ⟨c₁, hc₁, heq⟩
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | hcp | ha5 | hAA | hA7 | ⟨_, h37⟩
    · have h81 := pow_four_dvd_card_of_types (Or.inl hON)
      rw [h60] at h81
      norm_num at h81
    · have h81 := pow_four_dvd_card_of_types (Or.inr (Or.inl hcp))
      rw [h60] at h81
      norm_num at h81
    · have h81 := pow_four_dvd_card_of_types (Or.inr (Or.inr ha5))
      rw [h60] at h81
      norm_num at h81
    · obtain ⟨μ⟩ := hAA
      rw [Nat.card_congr μ.toEquiv, Nat.card_prod,
        KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at h60
      norm_num at h60
    · obtain ⟨μ⟩ := hA7
      rw [Nat.card_congr μ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h60
      norm_num at h60
    · obtain ⟨μ⟩ := h37
      rw [Nat.card_congr μ.toEquiv, Sec15.card_projSL_three_seven] at h60
      norm_num at h60
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
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1, KFacts.KS14.card_nativeJ2] at h60
    norm_num at h60
  ·
    exfalso
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, -, hL₁, -, -, -, -,
      -, -, -, -, -, -, -, -, hπ₁, -⟩ := h7
    obtain ⟨ψ⟩ := hpt ha₁ hL₁
    exact Sec15.Proof1514.not_isoLThreePi_of_j2 ψ hπ₁

@[expose] def Step148HJHJCent5 : Prop :=
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
          (omegaA A).ncard ≠ 12

theorem step148HJHJCent4_of_cent5
    (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJHJCent5) : Step148HJHJCent4 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl hJX hZ5
  let := ker148_normal hY.2
  have h12 := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd
    hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl hJX hZ5
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  have hbΩ : Subgroup.zpowers b ∈ omegaA A := hc.2.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hdYd : d ∈ Yd := hYBYd hdYB
  obtain ⟨φ⟩ := hJ2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZc⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h3J : 3 ∣ Nat.card (img148 A Y J) := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAq3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hJZ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZc, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  obtain ⟨hC3, hCD⟩ :=
    card_inf_centralizer_eq_three_of_j2 hS hY hJ hAJ hYd hYdJ hA6 hθ hdA hdYd hdc ⟨φ⟩
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdα3 : dα ^ 3 = 1 := hAq3 _ hdαA
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← hdαdef, h, one_mul, mul_one]
  obtain ⟨hYdeq, hYd6, -, hYdZ, hYdθ⟩ :=
    img148_yd_facts_of_j2 hY.2 hdA (hA3 d hdA) hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have h27 : 27 ∣ Nat.card ↥(img148 A Y J ⊓ Subgroup.centralizer {dα}) := by
    rw [← hYdeq, HJRes2.card_of_isTripleCover_six hYd6]
    norm_num
  obtain ⟨c₁, hc₁Ω, hc₁eq⟩ :=
    exists_point_of_a5_centPre148 h134 h48 hS hY ih hB hc hJY hAJ hJc h3J hZ5
  have hc₁A : c₁ ∈ A := (zpowers_mem_omegaA_iff.mp hc₁Ω).1
  have hY1 : centPre148 A Y J ∈ scriptY A := centPre148_mem_scriptY hY hAJ
  have hAN1 : A ≤ Subgroup.normalizer (deltaZero A (lB A) (centPre148 A Y J) : Set G) :=
    fun a ha => mem_normalizer_deltaZero (isNaturalFamily_lB A) (Subgroup.le_normalizer ha)
      (hY1.2 ha)
  have hAZ : img148 A Y A ≤ Subgroup.normalizer
      (img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAN1
  have hZJ : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_deltaZero_centPre148_le.trans inf_le_right
  obtain ⟨ψ5⟩ := hZ5
  have hZs : IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup_five
    exact MulEquiv.isSimpleGroup ψ5
  have h3Z : 3 ∣ Nat.card ↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) := by
    rw [Nat.card_congr ψ5.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num
  have hD1 : deltaZero A (lB A) (centPre148 A Y J) ≤ centPre148 A Y J := sSup_le fun _ hQ => hQ.2
  have hD1M : deltaZero A (lB A) (centPre148 A Y J) ≤ Y ⊔ A :=
    hD1.trans (centPre148_le.trans le_sup_left)
  have hO : img148 A Y (pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J))) = ⊥ := by
    refine eq_bot_of_le_simple hZs (img148_mono (pPrimeCoreOf_le 3 _))
      (img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 _)) h3Z ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_img148 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 _)))
  have hzc : img148 A Y (Subgroup.zpowers c₁) = Subgroup.zpowers (alpha148 A Y c₁ hc₁A) :=
    le_antisymm (img148_zpowers_le hc₁A) (Subgroup.zpowers_le.mpr
      (mem_img148_iff.mpr ⟨c₁, Subgroup.mem_sup_right hc₁A, Subgroup.mem_zpowers c₁, rfl⟩))
  have hZc₁ : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤ Subgroup.normalizer
      (Subgroup.zpowers (alpha148 A Y c₁ hc₁A) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have hD2 : deltaZero A (lB A)
        (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G)) ≤
          centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G) :=
      sSup_le fun _ hQ => hQ.2
    have hOM : pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J)) ≤ Y ⊔ A :=
      (pPrimeCoreOf_le 3 _).trans hD1M
    have hD2M : deltaZero A (lB A)
        (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G)) ≤ Y ⊔ A :=
      hD2.trans (inf_le_left.trans (centPre148_le.trans le_sup_left))
    calc img148 A Y (deltaZero A (lB A) (centPre148 A Y J))
        = img148 A Y (pPrimeCoreOf 3 (deltaZero A (lB A) (centPre148 A Y J)) ⊔
            deltaZero A (lB A)
              (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G))) := by
          rw [← hc₁eq]
      _ = img148 A Y (deltaZero A (lB A)
            (centPre148 A Y J ⊓ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G))) := by
          rw [img148_sup hOM hD2M, hO, bot_sup_eq]
      _ ≤ Subgroup.normalizer
            (img148 A Y (Subgroup.zpowers c₁) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
          img148_le_normalizer (hD2.trans inf_le_right)
      _ = Subgroup.normalizer
            (Subgroup.zpowers (alpha148 A Y c₁ hc₁A) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
          rw [hzc]
  have hc₁J : alpha148 A Y c₁ hc₁A ∈ img148 A Y J :=
    alpha148_mem_of_a5_point hAab hAq3 hF3 hC3 hCD hJZ hZJ hAZ ψ5 (alpha148_mem_img148 hc₁A)
      hZc₁
  have hdΩ : Subgroup.zpowers d ∉ omegaA A :=
    Sec15.Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48
      (Item148HJ.sec14Std_of_isLBConfig hS hc) (Item148HJ.j2_of_isLBConfig hc) hdA hd1
      hc.2.2.2.2
  have hc₁d : c₁ ∉ Subgroup.zpowers d := by
    intro h
    apply hdΩ
    have hle : Subgroup.zpowers c₁ ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr h
    have hc3 : Nat.card (Subgroup.zpowers c₁) = 3 := (zpowers_mem_omegaA_iff.mp hc₁Ω).2.1
    have hd3' : Nat.card (Subgroup.zpowers d) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hA3 d hdA) hd1]
    have heq : Subgroup.zpowers c₁ = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc3, hd3'])
    rw [← heq]
    exact hc₁Ω
  have hbJ : alpha148 A Y b hbA ∉ img148 A Y J := by
    intro hbJ
    have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
    have hbC := HJRes2.le_centralizer_of_theta hYdM rfl hYdθ hbA hbc.2
    have hbYd : alpha148 A Y b hbA ∈ img148 A Y Yd := by
      rw [hYdeq]
      exact ⟨hbJ, Subgroup.mem_centralizer_singleton_iff.mpr
        (hAab _ (alpha148_mem_img148 hbA) _ hdαA)⟩
    have hbd : alpha148 A Y b hbA ∈ Subgroup.zpowers dα :=
      hYdZ _ hbYd fun h hh => (Subgroup.mem_centralizer_singleton_iff.mp (hbC hh)).symm
    have hbd' : b ∈ Subgroup.zpowers d := by
      rcases inner_a5_mem_zpowers hdα3 hbd with h1 | h1 | h1
      · exact absurd (alpha148_injective hA3 hbA A.one_mem (h1.trans alpha148_one'.symm)) hb1
      · rw [alpha148_injective hA3 hbA hdA h1]
        exact Subgroup.mem_zpowers d
      · rw [alpha148_injective hA3 hbA (A.inv_mem hdA) (h1.trans (alpha148_inv hdA).symm)]
        exact inv_mem (Subgroup.mem_zpowers d)
    have hB9 : Nat.card B = 9 := by
      have := hB.2
      rw [hA.2] at this
      omega
    have hBle : B ≤ Subgroup.zpowers d := by
      rw [hc.1, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hbd'
      · exact Subgroup.mem_zpowers _
    have hcard := Subgroup.card_le_of_le hBle
    rw [hB9, Nat.card_zpowers, orderOf_eq_prime (hA3 d hdA) hd1] at hcard
    omega
  rcases ncard_omegaA_eq_six_or_twelve_of_j2_factor h134 h48 hS hB hc hY.2
      (P := img148 A Y J) ⟨φ⟩ (img148_le_normalizer hAJ) hdA hc₁A hbA hdJα hd1 h27 hc₁Ω hc₁J
      hc₁d hbΩ hbJ with h | h
  · exact h
  · exact absurd h h12

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
