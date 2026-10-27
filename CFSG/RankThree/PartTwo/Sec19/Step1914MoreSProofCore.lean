module

public import CFSG.RankThree.PartTwo.Sec19.Statements
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_le {F B : Subgroup G} (hF : IsMulCommutative F) (hBF : B ≤ F) :
    F ≤ Subgroup.normalizer (B : Set G) := by
  refine le_trans (fun f hf => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    (Subgroup.centralizer_le_normalizer (B : Set G))
  exact congrArg Subtype.val (hF.is_comm.comm ⟨x, hBF hx⟩ ⟨f, hf⟩)

theorem le_M_of_nine_le {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {F : Subgroup G} (hF : IsE27 F) (h9 : 9 ≤ Nat.card (F ⊓ E : Subgroup G)) : F ≤ M := by
  have h2 : 2 ≤ CFSG.Open.pRank 3 (F ⊓ E : Subgroup G) :=
    Late.two_le_pRank_of_elemAbelian (Late.isElemAbelian_of_le hF.1 inf_le_left) h9
  exact ((le_normalizer_of_le hF.1.1 inf_le_left).trans
    (normalizer_le_gamma inf_le_right h2)).trans hctx.mem_scriptM.2

theorem mem_partTwoE_of_nine_le {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {F : Subgroup G} (hF : IsE27 F) (h9 : 9 ≤ Nat.card (F ⊓ E : Subgroup G)) :
    F ∈ partTwoE G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := hctx.mem_scriptM.1
  refine ⟨hF.1, hF.2, CFSG.Open.pCoreOf 2 M, pCoreOf_ne_bot_of_isMaximalTwoLocal hM,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, ?_⟩
  rw [normalizer_pCoreOf_of_isMaximalTwoLocal hM]
  exact le_M_of_nine_le hctx hF h9

theorem eq_of_mem_scriptM {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {F M' : Subgroup G} (hF : IsE27 F) (hFM : F ≤ M)
    (hM' : M' ∈ scriptM (gamma 2 F : Set G)) : M' = M :=
  rank3II_19_2 hctx.hyp191 hF (isE27_of_mem_partTwoE hctx.mem_partTwoT.1) hM' hctx.mem_scriptM
    hFM

theorem ctx1912_of_mem_partTwoT {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {F M' : Subgroup G} (hFT : F ∈ partTwoT G) (hFc : F ≤ Subgroup.centralizer ({c} : Set G))
    (hFA : IsPGroup 3 (F ⊔ A : Subgroup G)) (hM' : M' ∈ scriptM (gamma 2 F : Set G)) :
    Ctx1912 G A c L F M' :=
  { hctx.toSec19Std with
    mem_partTwoE := hctx.mem_partTwoE
    not_mem_partTwoT := hctx.not_mem_partTwoT
    zpowers_mem_omegaA := hctx.zpowers_mem_omegaA
    mem_lA := hctx.mem_lA
    mem_partTwoT := hFT
    le_centralizer := hFc
    mem_scriptM := hM'
    isPGroup_sup := hFA
    hypS := hctx.hypS
    chosen136 := hctx.chosen136 }

theorem theta_le_gamma {E L : Subgroup G} (hE : IsE27 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) :
    (aschbacherSolvableCore 3 L).map L.subtype ≤ gamma 2 E := by
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hEab : CFSG.IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hE.1.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hE.1.2 x x.2) }
  refine PartOne.Vanish.le_of_forall_hyperplane_inf_centralizer_le Nat.prime_three hEab
    (by rw [hE.2]; norm_num) ?_ ?_ ?_
  · exact hEN.trans
      (GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 L)
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hθ.2.2.1
  · intro D hDE hD9
    refine inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (normalizer_le_gamma hDE ?_))
    exact Late.two_le_pRank_of_elemAbelian (Late.isElemAbelian_of_le hE.1 hDE)
      (by rw [hD9]; norm_num)

theorem le_of_normalizer_sup_eq_top {L B₁ B₂ X : Subgroup G} (hB₁L : B₁ ≤ L) (hB₂L : B₂ ≤ L)
    (hB₁ : IsPGroup 3 B₁) (hB₂ : IsPGroup 3 B₂)
    (hgen : Subgroup.normalizer (((B₁.subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :
          Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set (L ⧸ aschbacherSolvableCore 3 L)) ⊔
      Subgroup.normalizer (((B₂.subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :
          Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set (L ⧸ aschbacherSolvableCore 3 L)) = ⊤)
    (hθ : (aschbacherSolvableCore 3 L).map L.subtype ≤ X)
    (h₁ : Subgroup.normalizer (B₁ : Set G) ≤ X) (h₂ : Subgroup.normalizer (B₂ : Set G) ≤ X) :
    L ≤ X := by
  have hN : ∀ {B : Subgroup G}, B ≤ L → Subgroup.normalizer (B : Set G) ≤ X →
      ∀ n : L, n ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup L) : Set L) → (n : G) ∈ X := by
    intro B hBL hBX n hn
    apply hBX
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hBL hx⟩).mp
        (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hx
      have hxL : x ∈ L := by
        have h1 : (n : G) * x * (n : G)⁻¹ ∈ L := hBL hx
        have h2 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem n.2) h1) n.2
        simpa [mul_assoc] using h2
      have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hxL⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp h1
  have hB₁' : IsPGroup 3 (B₁.subgroupOf L) := hB₁.comap_subtype
  have hB₂' : IsPGroup 3 (B₂.subgroupOf L) := hB₂.comap_subtype
  have hY : (X.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) = ⊤ := by
    rw [eq_top_iff, ← hgen, sup_le_iff, normalizer_map_mk_eq hB₁', normalizer_map_mk_eq hB₂']
    exact ⟨Subgroup.map_mono fun n hn => Subgroup.mem_subgroupOf.mpr (hN hB₁L h₁ n hn),
      Subgroup.map_mono fun n hn => Subgroup.mem_subgroupOf.mpr (hN hB₂L h₂ n hn)⟩
  intro x hx
  have hxY : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (⟨x, hx⟩ : L) ∈
      (X.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
    hY ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hxY
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  have h1 : y⁻¹ * ⟨x, hx⟩ ∈ aschbacherSolvableCore 3 L := QuotientGroup.eq.mp hyx
  have h2 : ((y⁻¹ * ⟨x, hx⟩ : L) : G) ∈ X := hθ ⟨_, h1, rfl⟩
  have h3 : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : L) : G) := by simp
  rw [h3]
  exact X.mul_mem hy h2

end CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProof
