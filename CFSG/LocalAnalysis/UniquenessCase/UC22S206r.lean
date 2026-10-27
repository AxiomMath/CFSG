module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206l
public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
import CFSG.LocalAnalysis.UniquenessCase.UC22S206q
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.RankThree.PerfectCover
open CFSG.Quasithin.H13.A7Blk (ptCore)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G]

theorem uc22s206r_isCatalogGroup [Finite G] (D : Data G) {C : Subgroup (Bar2 D.M)}
    (hC : IsComponentOf C ⊤) : CFSG.Open.IsCatalogGroup (↥C ⧸ Subgroup.center ↥C) := by
  haveI := D.standing.simple
  have hM : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hB : CFSG.Open.IsKGroup (Bar2 D.M) := (D.standing.kProper.isKGroup D.M hM).quotient _
  haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2
  exact hB.isCatalogGroup_of_surjective C
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥C hC.2.2)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

theorem uc22s206r_calC [Finite G] (D : Data G) {C : Subgroup (Bar2 D.M)}
    (hC : IsComponentOf C ⊤) : ∃ A ∈ calC D.M, Nonempty (Bar2 A ≃* ↥C) := by
  obtain ⟨A, -, hAs, hAp, hAq, he, -⟩ := PartTwo.s15_Three_core_of_component hC
  exact ⟨A, ⟨hAs, hAp, hAq⟩, he⟩

theorem uc22s206r_pRank_le [Finite G] (D : Data G) (h82 : F08.R82 D) (hk : D.k = 2)
    {A : Subgroup G} (hA : A ∈ calC D.M) : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 A)) ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSE : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := fun h => by
    have h1 : D.k = 1 := by
      show CFSG.LocalAnalysis.RankThreeUC.kParam D.M = 1
      rw [CFSG.LocalAnalysis.RankThreeUC.kParam, if_pos h]
    omega
  have hA3 : CFSG.Open.pRank 3 A ≤ 2 := by
    by_contra h
    push Not at h
    exact hSE (h82 A ⟨hA.1, hA.2.1, h, Or.inl ⟨⟨hA.2.2.1⟩, hA.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hA.2.2⟩⟩)
  have hO : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥A) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥A)).exists_card_eq
    rw [hn]
    intro hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) A.subtype A.subtype_injective ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact (CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥A) hO).le.trans (h2.trans hA3)

theorem uc22s206r_center_alt8 {W : Type} [Group W] [Finite W] (hW : commutator W = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center W))) (hA : IsAlt (W ⧸ Subgroup.center W) 8) :
    Subgroup.center W = ⊥ := by
  haveI : Group.IsPerfect W := Group.isPerfect_def.mpr hW
  obtain ⟨e⟩ : Nonempty (W ⧸ Subgroup.center W ≃* alternatingGroup (Fin 8)) := hA
  set η : W →* alternatingGroup (Fin (6 + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center W))
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center W := uc22p20r_ker_comp e
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 6) (by norm_num) η hηs
    hker.le (by rw [hker]; exact hodd)
  rw [hker] at h1
  exact Subgroup.card_eq_one.mp h1

theorem uc22s206r_center_psl52 (hN : uc22p20rNativeGriess) {W : Type} [Group W] [Finite W]
    (hW : commutator W = ⊤) (hL : LieModel (W ⧸ Subgroup.center W) .PSL 5 2 1) :
    Subgroup.center W = ⊥ := by
  haveI : Group.IsPerfect W := Group.isPerfect_def.mpr hW
  obtain ⟨-, ⟨eM⟩⟩ := hN (W ⧸ Subgroup.center W) .PSL 5 2 1 hL
  have hM : Nat.card (hopfMultiplier (W ⧸ Subgroup.center W)) = 1 := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess (W ⧸ Subgroup.center W)).toEquiv,
      Nat.card_congr eM.toEquiv]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
    change Nat.gcd 5 (2 ^ 1 - 1) * 1 * (1 * 1) = 1
    norm_num
  have hdvd := uc22p20r_card_center_dvd_hopf (MulEquiv.refl (W ⧸ Subgroup.center W))
  rw [hM, Nat.dvd_one] at hdvd
  exact Subgroup.card_eq_one.mp hdvd

theorem uc22s206r_center_m24
    {W : Type} [Group W] [Finite W] (hW : commutator W = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center W))) (hS : IsSpor (W ⧸ Subgroup.center W) .M24) :
    Subgroup.center W = ⊥ := by
  haveI : Group.IsPerfect W := Group.isPerfect_def.mpr hW
  obtain ⟨e⟩ : Nonempty (W ⧸ Subgroup.center W ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    hS
  set π : W →* CFSG.Blueprint.NativeSporadic.Carrier .M24 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center W))
  have hker : π.ker = Subgroup.center W := uc22p20r_ker_comp e
  have hodd' : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
  have h : π.ker = ⊥ := CFSG.SectionRank.M24_perfect_odd_cover_trivial π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le hodd'
  rwa [hker] at h

theorem uc22s206r_center_j4
    {W : Type} [Group W] [Finite W] (hW : commutator W = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center W))) (hS : IsSpor (W ⧸ Subgroup.center W) .J4) :
    Subgroup.center W = ⊥ := by
  haveI : Group.IsPerfect W := Group.isPerfect_def.mpr hW
  obtain ⟨e⟩ : Nonempty (W ⧸ Subgroup.center W ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    hS
  set π : W →* CFSG.Blueprint.NativeSporadic.Carrier .J4 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center W))
  have hker : π.ker = Subgroup.center W := uc22p20r_ker_comp e
  have hodd' : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
  have h : π.ker = ⊥ := CFSG.SectionRank.J4_perfect_odd_cover_trivial
    CFSG.RankThree.OddKernel.j4OrderHyp π (e.surjective.comp (QuotientGroup.mk'_surjective _))
    hker.le hodd'
  rwa [hker] at h

theorem uc22s206r_mulEquiv_of_top {S X : Type} [Group S] [IsSimpleGroup S] [Group X]
    [Nontrivial X] {R : Subgroup S} (hR : R = ⊤) (e : Bar2 R ≃* X) : Nonempty (S ≃* X) := by
  subst hR
  set f : S →* X := e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥(⊤ : Subgroup S))).comp
    (Subgroup.topEquiv (G := S)).symm.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := S)).symm.surjective)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp h, hf⟩⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨s, rfl⟩ := hf x
    exact hx (MonoidHom.mem_ker.mp (by rw [h]; exact mem_top s))

theorem uc22s206r_cases_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsAlt X 8 ∨ LieModel X .PSL 5 2 1 ∨ IsSpor X .M24 ∨ IsSpor X .J4) :
    IsAlt Y 8 ∨ LieModel Y .PSL 5 2 1 ∨ IsSpor Y .M24 ∨ IsSpor Y .J4 := by
  rcases h with h | h | h | h
  · obtain ⟨f⟩ : Nonempty (X ≃* alternatingGroup (Fin 8)) := h
    exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · obtain ⟨f⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
    exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))
  · obtain ⟨f⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) := h
    exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans f⟩))

theorem uc22s206r_list880_of {X : Type} [Group X]
    (h : IsAlt X 8 ∨ LieModel X .PSL 5 2 1 ∨ IsSpor X .M24 ∨ IsSpor X .J4) : F08.List880 X := by
  unfold F08.List880 F08.IsMathieu
  rcases h with h | h | h | h
  · iterate 10 right
    exact Or.inl h
  · iterate 11 right
    exact Or.inl h
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · iterate 4 right
    exact Or.inl h

theorem uc22s206r_list880
    [Finite G] (D : Data G)
    (hK331 : InS3.K331) (hN : uc22p20rNativeGriess) (h82 : F08.R82 D) (hk : D.k = 2)
    {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} {C : Subgroup (Bar2 D.M)}
    (hC : IsComponentOf C ⊤) (ψ : ↥(ptCore α i) →* ↥C ⧸ Subgroup.center ↥C) (hψ : ψ.range ≠ ⊥)
    {TS : Subgroup (↥C ⧸ Subgroup.center ↥C)} (hTS : CFSG.ABGLocalTools.IsSylowOf 2 TS ⊤)
    (hTSn : TS ≤ normalizer (ψ.range : Set (↥C ⧸ Subgroup.center ↥C))) :
    ∃ A ∈ calC D.M, F08.List880 (Bar2 A) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2
  obtain ⟨A, hA, ⟨e₁⟩⟩ := uc22s206r_calC D hC
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e₁]
    exact uc22s206r_pRank_le D h82 hk hA
  obtain ⟨e₈⟩ := uc22s206l_nonempty_range α hα hker ψ hψ
  have hcase : IsAlt (↥C ⧸ Subgroup.center ↥C) 8 ∨
      LieModel (↥C ⧸ Subgroup.center ↥C) .PSL 5 2 1 ∨ IsSpor (↥C ⧸ Subgroup.center ↥C) .M24 ∨
      IsSpor (↥C ⧸ Subgroup.center ↥C) .J4 := by
    rcases hK331 (↥C ⧸ Subgroup.center ↥C) hC.2.2.2 (uc22s206r_isCatalogGroup D hC)
      (uc22s206q_pRank α hα hker ψ hψ h3) TS hTS ψ.range ⟨e₈⟩ hTSn with hR | h | h | h
    · obtain ⟨-, -, -, ha1, -⟩ := uc22s206p_rel
      haveI : Nontrivial (alternatingGroup (Fin 8)) := ⟨⟨uc22s206pA0, 1, ha1⟩⟩
      exact Or.inl (uc22s206r_mulEquiv_of_top hR e₈)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hodd : Odd (Nat.card (Subgroup.center ↥C)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₁).toEquiv]
    exact uc22p20p_odd_center_bar2 ↥A
  have hZ : Subgroup.center ↥C = ⊥ := by
    rcases hcase with h | h | h | h
    · exact uc22s206r_center_alt8 hC.2.2.1 hodd h
    · exact uc22s206r_center_psl52 hN hC.2.2.1 h
    · exact uc22s206r_center_m24 hC.2.2.1 hodd h
    · exact uc22s206r_center_j4 hC.2.2.1 hodd h
  let eC : ↥C ⧸ Subgroup.center ↥C ≃* ↥C :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨A, hA, uc22s206r_list880_of (uc22s206r_cases_congr (e₁.trans eC.symm).symm hcase)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
