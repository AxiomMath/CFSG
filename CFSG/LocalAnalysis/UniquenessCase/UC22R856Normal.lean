module

public import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73Y
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xA858
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterRu
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63LieOut
public import CFSG.LocalAnalysis.UniquenessCase.UC22R856NormalFour
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedMain
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSmallInputHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldNoThreeCoverHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xA859
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChain
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62OneControl
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAShared
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerActionOut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarCyclic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Cov
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R856Normal

open CFSG.Open Subgroup
open PartOne.Section8
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem r857_of_data
    {D : Data G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) : R857 D := by
  have hGA := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  exact r857_of_tables hSg h614 UCK.K332Route.k33_holds hGA
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group
    (exceptionalCoverSmallPrimes_of_griess hGA)
    eight60FieldNoThreeCover_holds eight60FieldSmallInput_holds

theorem fusion_of_cex856
    {D : Data G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h63 : UC6.R6_3 D)
    {L Q P : Subgroup G} (hc : Cex856 D L Q P) :
    List857 (Bar2 L) ∧ ¬ List857Clause1 (Bar2 L) ∧ P ≤ normalizer (L : Set G) ∧
      ControlsFusionIn D.M P := by
  have h857 := r857_of_data hSg h614
  have hPL : P ≤ normalizer (L : Set G) := r859_of_r858 (r858_of_r857 hSg h857) L Q P hc
  have hlist : List857 (Bar2 L) := (h857 L Q P hc).1
  have hno : ¬ List857Clause1 (Bar2 L) := by
    intro hcl
    have hΩ := (h857 L Q P hc).2.1 hcl
    rw [inf_eq_left.mpr hPL] at hΩ
    exact hc.false_of_omegaOne_le_center hSg h614 hΩ
  have h61 := h61_of_list857
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.outerFixedE9_holds
    hc.mem hc.rank hlist hno hc.sylowQ hc.sylowP hc.le hPL
  refine ⟨hlist, hno, hPL, fun A hAP g hg => ?_⟩
  exact exists_mem_conj_forall_of_centralizer_transport h63 hc.mem.1.le hc.sylowQ
    hc.le hc.sylowP hc.rank.ge hc.gamma hPL h61 hAP hg

theorem stronglyEmbedded_of_normal_extraspecial
    {D : Data G} (h63 : UC6.R6_3 D)
    (hM3 : ¬ IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 D.M ≤ 3) {L Q : Subgroup G}
    (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G)) (hQ : IsSylowOf 3 Q L)
    (hΓ : rankThreeGamma 1 3 Q ≤ D.M) (hQext : IsExtraspecialExpP 3 1 ↥Q)
    (hZ : center (Bar2 L) = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer (Bar2 L))) :
    IsStronglyPEmbedded 3 D.M := by
  classical
  by_cases hsp : IsStronglyPEmbedded 3 D.M
  · exact hsp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hQP⟩ := exists_sylow_three_ge_of_le hL.1.le hQ
  have hPNL : P ≤ normalizer (L : Set G) := hP.le.trans hML
  have hQeq : Q = P ⊓ L :=
    (hQ.eq_of_le (le_inf hQP hQ.le) inf_le_right (hP.isPGroup.to_le inf_le_left)).symm
  have hQPn : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hQ hQP hP.isPGroup hPNL
  have hPQ : P ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hQP hQ.le hQeq hQPn hQ hP.isPGroup hPNL le_rfl
      (inner_action_of_not_three_dvd_outer hOut hP.isPGroup hPNL)
  have hcyc : IsCyclic (centralizerBar P L) :=
    isCyclic_centralizerBar_of_pRank hQext hQP hQ.le hP.isPGroup
      ((CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hP.le).trans (hM3 hsp))
      ((IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (pCoreOf 2 L) hQ.isPGroup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot)
      (inf_centralizerBar_le_pCore_of_center_bar2 hZ) hQPn
  exact isStronglyPEmbedded_of_eight73Y_of_extraspecial UCK.k35w_holds
    stronglyEmbeddedCentralFree_holds h63 Nat.prime_three (by norm_num) hL hML (by simp [hZ]) hP
    hQ hQP hQext hPQ hcyc hΓ

private theorem sylow_extraspecial_of_cubic {N X : Type} [Group N] [Group X] [Finite X]
    (e : X ≃* N) {n : ℕ} (hn : Nat.card N = n) (hn0 : n ≠ 0) (h27 : 3 ^ 3 ∣ n)
    (h81 : ¬ 3 ^ (3 + 1) ∣ n) {x y : N} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (S : Sylow 3 X) :
    IsExtraspecialExpP 3 1 ↥(S : Subgroup X) := by
  have : Finite N := Finite.of_equiv X e.toEquiv
  have hfac : (Nat.card N).factorization 3 = 3 := by
    rw [hn]
    exact CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
      Nat.prime_three hn0 ⟨h27, h81⟩
  exact isExtraspecialExpP_sylow_of_ex27 hx hy hzx hzy hz hfac e S

theorem sylow_isExtraspecialExpP_nine
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 3 3 1 ∨ CFSG.Blueprint.LieModel Y .PSU 3 3 1 ∨
      CFSG.Blueprint.LieModel Y .Tits 0 2 1 ∨ IsSpor Y .J2 ∨ IsSpor Y .He ∨ IsSpor Y .Ru ∨
      IsSpor Y .J4 ∨ IsSpor Y .M12 ∨ IsSpor Y .M24)
    (S : Sylow 3 Y) : IsExtraspecialExpP 3 1 ↥(S : Subgroup Y) := by
  rcases hY with h | h | h | h | h | h | h | h | h
  · exact sylowIsExtraspecialOfTypes_holds Y (Or.inl h) S
  · exact sylow_isExtraspecialExpP_of_u33 h S
  · exact sylowIsExtraspecialOfTypes_holds Y (Or.inr h) S
  · obtain ⟨e⟩ := h
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
    exact sylow_extraspecial_of_cubic e CFSG.Sporadic.J2.card_J2 (by norm_num) (by norm_num)
      (by norm_num) hx hy hz hzx hzy S
  · obtain ⟨e⟩ := h
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    exact sylow_extraspecial_of_cubic e CFSG.Sporadic.He.card_He (by norm_num) (by norm_num)
      (by norm_num) hx hy hz hzx hzy S
  · obtain ⟨e⟩ := h
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    exact sylow_extraspecial_of_cubic e CFSG.Sporadic.Ru.card_Ru (by norm_num) (by norm_num)
      (by norm_num) hx hy hz hzx hzy S
  · obtain ⟨e⟩ := h
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact sylow_extraspecial_of_cubic e CFSG.Sporadic.J4.card_J4 (by norm_num) (by norm_num)
      (by norm_num) hx hy hz hzx hzy S
  · obtain ⟨e⟩ := h
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
    exact sylow_extraspecial_of_cubic e CFSG.Sporadic.Mathieu.card_M12 (by norm_num)
      (by norm_num) (by norm_num) hx hy hz hzx hzy S
  · obtain ⟨e⟩ := h
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
    exact sylow_extraspecial_of_cubic e CFSG.Sporadic.Mathieu.card_M24 (by norm_num)
      (by norm_num) (by norm_num) hx hy hz hzx hzy S

theorem center_eq_bot_nine
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 3 3 1 ∨ CFSG.Blueprint.LieModel Y .PSU 3 3 1 ∨
      CFSG.Blueprint.LieModel Y .Tits 0 2 1 ∨ IsSpor Y .J2 ∨ IsSpor Y .He ∨ IsSpor Y .Ru ∨
      IsSpor Y .J4 ∨ IsSpor Y .M12 ∨ IsSpor Y .M24)
    (hq : CFSG.Open.IsQuasisimple Y) : center Y = ⊥ := by
  have hI : IsSimpleGroup Y := by
    rcases hY with h | h | h | h | h | h | h | h | h
    · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
    · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
    · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
    · obtain ⟨e⟩ := h
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
        CFSG.Sporadic.J2.isSimpleGroup_J2
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
        CFSG.Sporadic.He.fam_he_simplicity.2.2
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
        CFSG.Sporadic.Ru.fam_ru_simplicity.2.2
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
        CFSG.Sporadic.J4.fam_j4_simplicity.2.2
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M12) :=
        CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
        CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      exact e.isSimpleGroup
  exact @P22w.center_eq_bot_of_isSimpleGroup Y _ hI hq

theorem not_three_dvd_card_outer_nine
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 3 3 1 ∨ CFSG.Blueprint.LieModel Y .PSU 3 3 1 ∨
      CFSG.Blueprint.LieModel Y .Tits 0 2 1 ∨ IsSpor Y .J2 ∨ IsSpor Y .He ∨ IsSpor Y .Ru ∨
      IsSpor Y .J4 ∨ IsSpor Y .M12 ∨ IsSpor Y .M24) :
    ¬ 3 ∣ Nat.card (Outer Y) := by
  rcases hY with h | h | h | h | h | h | h | h | h
  · exact not_three_dvd_card_outer_of_lieModel_psl3 h
  · exact not_three_dvd_card_outer_of_lieModel_psu3 h
  · have hR : CFSG.Blueprint.ReeTitsModel Y .Tits 2 1 := (h.reeTitsModel (by decide)).2
    exact CFSG.HardMathSupport.Dickson.Sec6.I923.not_three_dvd_card_outer_tits hR
  · exact not_three_dvd_card_outer_of_isSpor_J2 h
  · obtain ⟨e⟩ := h
    rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
    intro hdiv
    have hle : Nat.card (Outer CFSG.Blueprint.NativeSporadic.He) ≤ 2 :=
      CFSG.Sporadic.Schreier.AT_He_Schreier.1
    exact (by omega : ¬ 3 ≤ Nat.card (Outer CFSG.Blueprint.NativeSporadic.He))
      (Nat.le_of_dvd Nat.card_pos hdiv)
  · exact not_three_dvd_card_outer_of_isSpor_Ru h
  · exact not_three_dvd_card_outer_of_isSpor_J4 h
  · exact not_three_dvd_card_outer_of_isSpor_m12 h
  · exact not_three_dvd_card_outer_of_isSpor_m24 h

theorem false_of_normal_nine_types
    {D : Data G} (h63 : UC6.R6_3 D)
    (hM3 : ¬ IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 D.M ≤ 3) {L Q P : Subgroup G}
    (hc : Cex856 D L Q P) (hML : D.M ≤ normalizer (L : Set G))
    (hX : CFSG.Blueprint.LieModel (Bar2 L) .PSL 3 3 1 ∨
      CFSG.Blueprint.LieModel (Bar2 L) .PSU 3 3 1 ∨ CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨
      IsSpor (Bar2 L) .J2 ∨ IsSpor (Bar2 L) .He ∨ IsSpor (Bar2 L) .Ru ∨
      IsSpor (Bar2 L) .J4 ∨ IsSpor (Bar2 L) .M12 ∨ IsSpor (Bar2 L) .M24) : False :=
  hc.notStrong (stronglyEmbedded_of_normal_extraspecial h63 hM3 hc.mem hML hc.sylowQ hc.gamma
    (isExtraspecialExpP_of_isSylowOf_bar hc.sylowQ (sylow_isExtraspecialExpP_nine hX))
    (center_eq_bot_nine hX hc.mem.2.2) (not_three_dvd_card_outer_nine hX))

theorem stronglyEmbedded_of_normal_g2_of_not_nine
    {D : Data G} (h63 : UC6.R6_3 D)
    (hM3 : ¬ IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 D.M ≤ 3) {L Q : Subgroup G}
    (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G)) (hQ : IsSylowOf 3 Q L)
    (hΓ : rankThreeGamma 1 3 Q ≤ D.M) {p f : ℕ}
    (hG2 : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 p f) (hp3 : p ≠ 3)
    (h9 : ¬ 9 ∣ (p ^ f) ^ 2 - 1) : IsStronglyPEmbedded 3 D.M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := hG2.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hc.2
  have hq : 3 ≤ Nat.card K := hKcard ▸ hc.1.2.2.2
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hc.1.1).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hf3 : ¬ 3 ∣ f := fun hf =>
    h9 (CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.nine_dvd_sq_sub_one
      (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hc.1.1).mp hd).symm) hf)
  have hQext : IsExtraspecialExpP 3 1 Q :=
    isExtraspecialExpP_of_isSylowOf_bar hQ (fun R => by
      let R' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R
      have hR' : (R' : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) =
          (R : Subgroup (Bar2 L)).map e.toMonoidHom := by simp [R']
      have er : (R : Subgroup (Bar2 L)) ≃*
          (R' : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := by
        rw [hR']
        exact e.subgroupMap (R : Subgroup (Bar2 L))
      exact isExtraspecialExpP_of_mulEquiv er
        (R856NormalFour.sylow_isExtraspecialExpP_of_g2_of_not_nine hK3 hq (hKcard ▸ h9) R'))
  have hZ : center (Bar2 L) = ⊥ := by
    have hz : center (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    have hmap := Subgroup.map_center_eq e
    rw [hz] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hOut : ¬ 3 ∣ Nat.card (Outer (Bar2 L)) := by
    have hdvd := card_outer_adjointGroup_G2_dvd hc.1.1 hc.1.2.1 hKcard hq
    rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
    intro h
    exact (Nat.prime_three.not_dvd_mul (by norm_num) hf3) (h.trans hdvd)
  exact stronglyEmbedded_of_normal_extraspecial h63 hM3 hL hML hQ hΓ hQext hZ hOut

theorem false_of_normal_triple_cover_of_rank_le_two
    {D : Data G} {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X)
    (hML : D.M ≤ normalizer (L : Set G)) (hcover : List857Clause2 (Bar2 L))
    (hM3 : CFSG.Open.pRank 3 D.M ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := hX.cex
  have hQext := isExtraspecialExpP_of_isSylowOf_bar hc.sylowQ
    (fun Qb => threeCoverSylowExtraspecial_holds _ hcover Qb)
  have hQL : Q ≤ L := hc.sylowQ.le
  have hPNL : P ≤ normalizer (L : Set G) := hc.sylowP.le.trans hML
  have hQeq : Q = P ⊓ L :=
    (hc.sylowQ.eq_of_le (le_inf hc.le hQL) inf_le_right
      (hc.sylowP.isPGroup.to_le inf_le_left)).symm
  have hQn : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hc.sylowQ hc.le hc.sylowP.isPGroup hPNL
  have hPQ : P ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hc.le hQL hQeq hQn hc.sylowQ hc.sylowP.isPGroup
      hPNL le_rfl (inner_action_of_not_three_dvd_outer
        (not_three_dvd_card_outer_of_cover hcover) hc.sylowP.isPGroup hPNL)
  have hcomm : ∀ q ∈ Q, ∀ c ∈ centralizerBar P L, q * c = c * q :=
    fun q hq c hcc => commute_of_mem_centralizerBar Nat.prime_three (by norm_num)
      hc.sylowP.isPGroup hQL hc.le hq hcc
  have hQexp : ∀ q ∈ Q, q ^ 3 = 1 := by
    intro q hq
    have hexp := Monoid.pow_exponent_eq_one (⟨q, hq⟩ : Q)
    rw [hQext.2.1] at hexp
    exact congrArg Subtype.val hexp
  obtain ⟨E, hEQ, hEel, hEcard⟩ := CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq
    (p := 3) (by norm_num) hc.sylowQ.isPGroup hc.not_isCyclic_sylowQ
  have hXQ : X ≤ Q := by
    intro x hx
    have hxp : x ^ 3 = 1 := by
      have hx3 := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
      rw [hX.card] at hx3
      exact congrArg Subtype.val hx3
    exact uc22s213_mem_of_pow_three_eq_one hM3 (hQL.trans hc.mem.1.le)
      ((centralizerBar_le P L).trans hc.sylowP.le)
      ((centralizerBar_le P L).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hc.le).mp hQn))
      hcomm hQexp hEQ hEel hEcard (hPQ (hX.le hx)) hxp
  exact hX.not_le_sylowQ hXQ

end CFSG.LocalAnalysis.UniquenessCase.UC22.R856Normal
