module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_le_of_le_normalizer {Y A : Subgroup G} (hAc : IsMulCommutative A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) : ⁅Y ⊔ A, Y ⊔ A⁆ ≤ Y := by
  have hm : ∀ g ∈ Y ⊔ A, ∃ y ∈ Y, ∃ a ∈ A, g = y * a := by
    intro g hg
    have hg' : g ∈ ((Y : Set G) * (A : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY]
      exact hg
    obtain ⟨y, hy, a, ha, rfl⟩ := hg'
    exact ⟨y, hy, a, ha, rfl⟩
  have hconj : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hAY ha) y).mp hy
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨y₁, hy₁, a₁, ha₁, rfl⟩ := hm g₁ hg₁
  obtain ⟨y₂, hy₂, a₂, ha₂, rfl⟩ := hm g₂ hg₂
  have hc : Commute a₁ a₂ := congrArg Subtype.val (hAc.is_comm.comm ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
  have key : ⁅y₁ * a₁, y₂ * a₂⁆ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ := by
    rw [commutatorElement_def]
    calc y₁ * a₁ * (y₂ * a₂) * (y₁ * a₁)⁻¹ * (y₂ * a₂)⁻¹
        = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₁ * (a₂ * a₁⁻¹)) * y₁⁻¹ * a₂⁻¹ * y₂⁻¹ := by group
      _ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₁ * (a₁⁻¹ * a₂)) * y₁⁻¹ * a₂⁻¹ * y₂⁻¹ := by
        rw [hc.inv_left.eq]
      _ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ := by group
  rw [key]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ (hconj a₁ ha₁ y₂ hy₂))
    (hconj a₂ ha₂ _ (Y.inv_mem hy₁))) (Y.inv_mem hy₂)

omit [Finite G] in
theorem isSubnormal_subgroupOf_trans148 {E Y X : Subgroup G} (hEY : E ≤ Y) (hYX : Y ≤ X)
    (hE : (E.subgroupOf Y).IsSubnormal) (hY : (Y.subgroupOf X).IsSubnormal) :
    (E.subgroupOf X).IsSubnormal := by
  let ι : ↥(Y.subgroupOf X) →* ↥Y := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
  have hcomap : (E.subgroupOf Y).comap ι = (E.subgroupOf X).subgroupOf (Y.subgroupOf X) := by
    ext g
    exact Iff.rfl
  have h1 : ((E.subgroupOf X).subgroupOf (Y.subgroupOf X)).IsSubnormal := by
    rw [← hcomap]
    exact hE.comap ι
  exact Subgroup.IsSubnormal.trans (fun x hx => hEY hx) h1 hY

omit [Finite G] in
theorem le_of_isPerfect_of_le_sup {Y A J : Subgroup G} (hAc : IsMulCommutative A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hJ : Group.IsPerfect J) (hJM : J ≤ Y ⊔ A) :
    J ≤ Y := by
  rw [← (Subgroup.isPerfect_iff).mp hJ]
  exact (Subgroup.commutator_mono hJM hJM).trans (commutator_sup_le_of_le_normalizer hAc hAY)

theorem step148Lift_of_lift429
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h429 : Step148Lift429) : Step148Lift := by
  intro G _ _ A c L h Y hY hs e he he1 K hK hAK hsec htype
  have hA : Late.IsE27 A := h.isE27
  have hAc : IsMulCommutative A := hA.1.1
  have hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n := ⟨3, le_rfl, by rw [hA.2]; norm_num⟩
  have hKYC := le_of_mem_thetaComponentsIn hK
  have hKY : K ≤ Y := hKYC.trans inf_le_left
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hK1 : K ≠ ⊥ := by
    have : Nontrivial (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have : Nontrivial ↥K := (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this
  have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hY1 | hYt
    · exact hK1 (le_bot_iff.mp (hY1 ▸ hKY))
    · exact hY.1 hYt
  have hM4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  have hYCM : Y ⊓ Subgroup.centralizer ({e} : Set G) ≤
      (Y ⊔ A) ⊓ Subgroup.centralizer ({e} : Set G) := inf_le_inf_right _ le_sup_left
  have hKM : K ∈ thetaComponentsIn ((Y ⊔ A) ⊓ Subgroup.centralizer ({e} : Set G)) := by
    have hnorm : ((Y ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf
        ((Y ⊔ A) ⊓ Subgroup.centralizer ({e} : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYCM]
      intro m hm
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMN (Subgroup.mem_inf.mp hm).1, Subgroup.le_normalizer (Subgroup.mem_inf.mp hm).2⟩
    refine Sec6.mem_thetaComponentsIn_of (hKYC.trans hYCM) hKp ?_ hKq
    exact isSubnormal_subgroupOf_trans148 hKYC hYCM
      (mem_thetaComponentsIn_iff.mp hK).2.2.1 hnorm.isSubnormal
  obtain ⟨J, hJM, hKJ⟩ := Sec6.exists_le_mem_thetaComponentsIn h48 hM4
    (le_sup_right : A ≤ Y ⊔ A) hA.1 hAn he he1 hKM
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM4 le_sup_right hA.1 hAn J hJM
  have hJY : J ≤ Y := le_of_isPerfect_of_le_sup hAc hY.2
    (isPerfect_of_mem_thetaComponentsIn hJM) (le_of_mem_thetaComponentsIn hJM)
  have hJ : J ∈ thetaComponentsIn Y := mem_thetaComponentsIn_iff.mpr
    ⟨hJY, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hJY le_sup_left
      (mem_thetaComponentsIn_iff.mp hJM).2⟩
  exact ⟨J, hJ, hKJ, hAJ, h429 G A c L h Y hY hs e he he1 K hK hAK hsec htype J hJ hKJ hAJ⟩

end CFSG.RankThree.PartTwo.Sec14
