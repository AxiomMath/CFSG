module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Main148

omit [Finite G] in
theorem centralizer_closure_pair148 (b d : G) :
    Subgroup.centralizer ((Subgroup.closure {b, d} : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem lbConfig_points {A B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (hA : Nat.card A = 27) (hc : IsLBConfig A B b d Lb) :
    b ∈ B ∧ d ∈ B ∧ b ≠ 1 ∧ d ≠ 1 ∧
      Subgroup.centralizer (B : Set G) =
        Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
  obtain ⟨hBcl, hbΩ, -, -, -⟩ := hc
  have hbB : b ∈ B := hBcl ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hBcl ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hb1 : b ≠ 1 := by
    rintro rfl
    have h3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  have hd1 : d ≠ 1 := by
    rintro rfl
    have hle : B ≤ Subgroup.zpowers b := by
      rw [hBcl, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_zpowers x
      · exact Subgroup.one_mem _
    have h3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
    have h9 : Nat.card B = 9 := by have := hB.2; omega
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [h9, h3] at hdvd
    omega
  refine ⟨hbB, hdB, hb1, hd1, ?_⟩
  rw [hBcl]
  exact centralizer_closure_pair148 b d

theorem exists_yd_j148 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb) :
    ∃ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd ∧
      A ≤ Subgroup.normalizer (Yd : Set G) ∧
      ∃ J ∈ thetaComponentsIn Y, Yd ≤ J ∧ A ≤ Subgroup.normalizer (J : Set G) := by
  have hA : Late.IsE27 A := h.isE27
  have hAc : IsMulCommutative A := hA.1.1
  have hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n := ⟨3, le_rfl, by rw [hA.2]; norm_num⟩
  obtain ⟨hbB, hdB, hb1, hd1, hCB⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAc.is_comm.comm ⟨x, hx⟩ ⟨d, hdA⟩))
  have hYBle := le_of_mem_thetaComponentsIn hYB
  have hYBY : YB ≤ Y := hYBle.trans inf_le_left
  have hYB1 : YB ≠ ⊥ := by
    have : Nontrivial (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) :=
      CFSG.LocalCores.isQuasisimple_nontrivial (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
    have : Nontrivial ↥YB :=
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥YB)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot YB).mp this
  have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hY1 | hYt
    · exact hYB1 (le_bot_iff.mp (hY1 ▸ hYBY))
    · exact hY.1 hYt
  have hM4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  set M₁ := (Y ⊔ A) ⊓ Subgroup.centralizer ({d} : Set G) with hM₁
  have hM₁4 : SectionFourHyp ↥M₁ :=
    h.toTheoremFourHyp.sectionFourHyp (fun ht => hMtop (top_le_iff.mp (ht ▸ inf_le_left)))
  have hAM₁ : A ≤ M₁ := le_inf le_sup_right hAd
  have hle : Y ⊓ Subgroup.centralizer (B : Set G) ≤ M₁ ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [hCB]
    exact le_inf (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans inf_le_right))
      (inf_le_right.trans inf_le_left)
  have hYBM : YB ∈ thetaComponentsIn (M₁ ⊓ Subgroup.centralizer ({b} : Set G)) := by
    have hnorm : ((Y ⊓ Subgroup.centralizer (B : Set G)).subgroupOf
        (M₁ ⊓ Subgroup.centralizer ({b} : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
      intro m hm
      have hmM : m ∈ Y ⊔ A := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hm).1).1
      have hmB : m ∈ Subgroup.centralizer (B : Set G) := by
        rw [hCB]
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hm).2,
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hm).1).2⟩
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hMN hmM, Subgroup.le_normalizer hmB⟩
    refine Sec6.mem_thetaComponentsIn_of (hYBle.trans hle) (isPerfect_of_mem_thetaComponentsIn hYB)
      ?_ (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
    exact isSubnormal_subgroupOf_trans148 hYBle hle (mem_thetaComponentsIn_iff.mp hYB).2.2.1
      hnorm.isSubnormal
  obtain ⟨Yd, hYdM, hYBYd⟩ :=
    Sec6.exists_le_mem_thetaComponentsIn h48 hM₁4 hAM₁ hA.1 hAn hbA hb1 hYBM
  have hAYd : A ≤ Subgroup.normalizer (Yd : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM₁4 hAM₁ hA.1 hAn Yd hYdM
  have hYdM₁ : Yd ≤ M₁ := le_of_mem_thetaComponentsIn hYdM
  have hYdY : Yd ≤ Y := le_of_isPerfect_of_le_sup hAc hY.2
    (isPerfect_of_mem_thetaComponentsIn hYdM) (hYdM₁.trans inf_le_left)
  have hYdC : Yd ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) :=
    le_inf hYdY (hYdM₁.trans inf_le_right)
  have hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)) :=
    mem_thetaComponentsIn_iff.mpr ⟨hYdC, PartOne.subgroupOf_mem_thetaComponents_of_le
      Nat.prime_three hYdC (inf_le_inf_right _ le_sup_left) (mem_thetaComponentsIn_iff.mp hYdM).2⟩
  obtain ⟨J, hJM, hYdJ⟩ :=
    Sec6.exists_le_mem_thetaComponentsIn h48 hM4 le_sup_right hA.1 hAn hdA hd1 hYdM
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM4 le_sup_right hA.1 hAn J hJM
  have hJY : J ≤ Y := le_of_isPerfect_of_le_sup hAc hY.2
    (isPerfect_of_mem_thetaComponentsIn hJM) (le_of_mem_thetaComponentsIn hJM)
  have hJ : J ∈ thetaComponentsIn Y := mem_thetaComponentsIn_iff.mpr
    ⟨hJY, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hJY le_sup_left
      (mem_thetaComponentsIn_iff.mp hJM).2⟩
  exact ⟨Yd, hYd, hYBYd, hAYd, J, hJ, hYdJ, hAJ⟩

end Main148

open Main148

section Certificates

@[expose] def Step148HJType : Prop :=
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
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd →
        A ≤ Subgroup.normalizer (Yd : Set G) →
      ∀ J ∈ thetaComponentsIn Y, Yd ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      letI := ker148_normal hY.2
      (Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) ∨
        (Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y)

theorem step148HJComp_of_type (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hT : Step148HJType) : Step148HJComp := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle
  let := ker148_normal hY.2
  obtain ⟨Yd, hYd, hYBYd, hAYd, J, hJ, hYdJ, hAJ⟩ := exists_yd_j148 h45 h48 h hY hB hYB hc
  rcases hT G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd J hJ
      hYdJ hAJ with ht | hcase
  · exact Or.inl ⟨J, hJ, hYBYd.trans hYdJ, hAJ, ht⟩
  · exact Or.inr hcase

theorem step148HJ_of_type (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hT : Step148HJType)
    (hM : Step148HJM24) (hN : Step148HJNormal) (hH : Step148HJHJ) (h5 : Step148HJA5) :
    Step148HJ :=
  step148HJ_of (step148HJComp_of_type h45 h48 hT) hM hN hH h5

end Certificates

end CFSG.RankThree.PartTwo.Sec14
