module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
public import CFSG.Timmesfeld.Bridge.RootClosureRankOne
public import CFSG.CGT.PushingUpLit.Glue.CStarBridge
public import CFSG.Goldschmidt.Steps.G37Wrappers
public import CFSG.GroupTheory.LiftPermutes
public import CFSG.GroupTheory.QuasisimpleTwoQuotient
public import CFSG.GroupTheory.PermutesConjSup
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev Mbar9 (D : Data G) : Type := CFSG.Quasithin.OTwoQuot D.M

abbrev K1Nine (D : Data G) (L : Subgroup G) : Subgroup (Mbar9 D) :=
  CFSG.Quasithin.imageOTwoQuot D.M L

abbrev Tbar9 (D : Data G) : Subgroup (Mbar9 D) :=
  CFSG.Quasithin.imageOTwoQuot D.M D.T

theorem isComponent_K1 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) : CFSG.IsComponent (K1Nine D L) :=
  CFSG.Quasithin.C2Push.isComponent_imageOTwoQuot_of_isSubnormal hL.1
    (s15_Three_qs_of_open hL.2.2)

theorem nonempty_bar2_mulEquiv_K1 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(K1Nine D L)) :=
  CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hL.1

theorem isSylowOf_Tbar {D : Data G} :
    CFSG.ABGLocalTools.IsSylowOf 2 (Tbar9 D) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hidx : (D.T.subgroupOf D.M).index = D.T.relIndex D.M := by
    have h1 := Subgroup.index_mul_card (H := D.T.subgroupOf D.M)
    have h2 := Subgroup.relIndex_mul_card (H := D.T) (K := D.M)
    have hc : Nat.card (D.T.subgroupOf D.M) = Nat.card D.T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
    rw [hc] at h1
    rw [inf_eq_left.2 hTM] at h2
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥D.T)) (h1.trans h2.symm)
  have hsub : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf D.M) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hT2.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right, hidx]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.2
  have hmap := s16c7_isSylowOf_map hsub (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M))
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap

theorem isSylowOf_inf_K1 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Tbar9 D ⊓ K1Nine D L) (K1Nine D L) := by
  refine uc22p22r_fo_sylow_inf (isSylowOf_Tbar (D := D)) ?_
  exact CFSG.Quasithin.A3.subnormal_top_iff.mpr (isComponent_K1 hL).2

abbrev S1Nine (D : Data G) (L : Subgroup G) : Subgroup (Mbar9 D) :=
  Tbar9 D ⊓ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))

theorem S1_inf_K1 {D : Data G} (L : Subgroup G) :
    S1Nine D L ⊓ K1Nine D L = Tbar9 D ⊓ K1Nine D L := by
  rw [S1Nine, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer)]

theorem isSylowOf_S1_inf_K1 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S1Nine D L ⊓ K1Nine D L) (K1Nine D L) := by
  rw [S1_inf_K1]
  exact isSylowOf_inf_K1 hL

theorem lie_three_of_q {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (hq3 : q = 3) :
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ LieModel (BarInf L) t n 3 1 := by
  obtain ⟨-, -, t, n, f, hadm, hq, hlie⟩ := hC.lie
  have h3 : r ^ f = 3 := hq ▸ hq3
  obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.1 h3
  exact ⟨t, n, hadm, hlie⟩

theorem odd_card_center_K1Nine {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    Odd (Nat.card (Subgroup.center ↥(K1Nine D L))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK1sub : (K1Nine D L).IsSubnormal := (isComponent_K1 hL).2
  have hK1Open : CFSG.Open.IsSubnormal (K1Nine D L) ⊤ :=
    CFSG.Quasithin.A3.subnormal_top_iff.mpr hK1sub
  have hpCore_bot : CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Mbar9 D)) = ⊥ := by
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq]
    exact CFSG.Quasithin.pCore_two_quot_eq_bot D.M
  refine CFSG.Timmesfeld.Bridge.RootClosure.odd_card_center
    (K := ↥(K1Nine D L)) (fun N hN hN2 => ?_)
  let N' : Subgroup (Mbar9 D) := N.map (K1Nine D L).subtype
  have hN'le : N' ≤ K1Nine D L := Subgroup.map_subtype_le N
  have hN'2 : IsPGroup 2 N' := hN2.map _
  have hEq : N'.subgroupOf (K1Nine D L) = N := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hN'subK : (N'.subgroupOf (K1Nine D L)).IsSubnormal := by
    rw [hEq]
    exact hN.isSubnormal
  have hN'sub : N'.IsSubnormal :=
    Subgroup.IsSubnormal.trans hN'le hN'subK hK1sub
  have hN'Open : CFSG.Open.IsSubnormal N' ⊤ :=
    CFSG.Quasithin.A3.subnormal_top_iff.mpr hN'sub
  have hle : N' ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Mbar9 D)) := by
    refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) le_rfl
      (Subgroup.le_normalizer) hN'2).trans
      (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hN'Open)
  rw [hpCore_bot] at hle
  have hN'bot : N' = ⊥ := le_bot_iff.mp hle
  have hNbot : N = ⊥ := by
    exact Subgroup.map_injective (f := (K1Nine D L).subtype) Subtype.val_injective
      (by simpa [N'] using hN'bot)
  exact hNbot

theorem commute_of_ne_conj_K1Nine {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    ∀ (t : Mbar9 D), t ∈ Tbar9 D →
      (K1Nine D L).map (MulAut.conj t).toMonoidHom ≠ K1Nine D L →
      ∀ x ∈ K1Nine D L,
        ∀ y ∈ (K1Nine D L).map (MulAut.conj t).toMonoidHom, Commute x y := by
  intro t ht hne x hx y hy
  have hK : CFSG.IsComponent (K1Nine D L) := isComponent_K1 hL
  have hK' : CFSG.IsComponent ((K1Nine D L).map (MulAut.conj t).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  exact (CFSG.StandardType.ggCommute_of_isComponent_ne hK hK' hne hy hx).symm

theorem exists_permutes_three_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hK : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
      CFSG.Open.IsQuasisimple ↥K → Odd (Nat.card (Subgroup.center ↥K)) →
      Nonempty (↥K ≃* Bar2 L) →
      Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
      (∃ n : ℕ, K.index = 2 ^ n) →
      ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
        ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
          ¬ IsCyclic ↥E ∧ Permutes E S) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hZ := odd_card_center_K1Nine hL
  have hS : IsPGroup 2 (S1Nine D L) :=
    (isSylowOf_Tbar (D := D)).isPGroup.to_le inf_le_left
  have hSK : S1Nine D L ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := inf_le_right
  have hSyl := isSylowOf_S1_inf_K1 hL
  let hCnorm := CFSG.GroupTheory.twoQuotientC_normal hSK
  letI : (CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L)).Normal := hCnorm
  let Y := CFSG.GroupTheory.twoQuotientY (K1Nine D L) (S1Nine D L) hCnorm
  let KY := CFSG.GroupTheory.twoQuotientKY (K1Nine D L) (S1Nine D L) hCnorm
  let SY := CFSG.GroupTheory.twoQuotientSY (K1Nine D L) (S1Nine D L) hCnorm
  have hKYn : KY.Normal := CFSG.GroupTheory.twoQuotientKY_normal hSK
  have hKYe : Nonempty (↥KY ≃* Bar2 L) := by
    obtain ⟨e⟩ := CFSG.GroupTheory.twoQuotientK_nonempty_equiv_K hZ hS hSK
    obtain ⟨e2⟩ := nonempty_bar2_mulEquiv_K1 hL
    exact ⟨e.trans e2.symm⟩
  obtain ⟨eK⟩ := CFSG.GroupTheory.twoQuotientK_nonempty_equiv_K hZ hS hSK
  have hKYq : CFSG.Open.IsQuasisimple ↥KY :=
    CFSG.Goldschmidt.G37.open_isQuasisimple_of_mulEquiv eK.symm
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (isComponent_K1 hL).1)
  have hKYodd : Odd (Nat.card (Subgroup.center ↥KY)) := by
    rw [Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
    exact hZ
  have hcent : Subgroup.centralizer (KY : Set Y) =
      (Subgroup.center ↥KY).map KY.subtype :=
    CFSG.GroupTheory.twoQuotient_centralizer_eq_center hZ hS hSK hSyl
  have hidx : ∃ n, KY.index = 2 ^ n := CFSG.GroupTheory.twoQuotientKY_index_eq_pow hS hSK
  have hSY : CFSG.Quasithin.IsSylowIn 2 SY ⊤ :=
    CFSG.GroupTheory.twoQuotientSY_isSylowIn hS hSK hSyl
  obtain ⟨EY, hEYle, hEYne, hEYp, hEYexp, hEYnc, hEYperm⟩ :=
    hK Y KY hKYn hKYq hKYodd hKYe hcent hidx SY hSY
  obtain ⟨E, hEK, ⟨eE⟩, hEp, hEperm⟩ :=
    CFSG.GroupTheory.twoQuotient_lift_pgroup_permutes (K := K1Nine D L) (S := S1Nine D L)
      hZ hS hSK Nat.prime_three (by norm_num) hEYle hEYp hEYperm
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥EY = 1 := by
      rw [← Nat.card_congr eE.toEquiv, hbot, Subgroup.card_bot]
    exact hEYne (Subgroup.eq_bot_of_card_eq _ hcard)
  have hEncyc : ¬ IsCyclic ↥E := by
    intro hcyc
    exact hEYnc (isCyclic_of_surjective eE eE.surjective)
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have h1 : eE ⟨x, hx⟩ ^ 3 = 1 :=
      Subtype.ext (by simpa using hEYexp _ (eE ⟨x, hx⟩).2)
    have h2 : eE (⟨x, hx⟩ ^ 3) = eE 1 := by
      rw [map_pow, map_one]
      exact h1
    have h3 : (⟨x, hx⟩ : ↥E) ^ 3 = 1 := eE.injective h2
    simpa using congrArg (fun z : ↥E => (z : Mbar9 D)) h3
  obtain ⟨Xbar, hEXbar, hXbarT, hXbarExp, hXbarP⟩ :=
    CFSG.GroupTheory.exists_permutes_sup_conj (H := Mbar9 D) (K := K1Nine D L)
      (T := Tbar9 D) (A := E) hEK (commute_of_ne_conj_K1Nine hL) (by
        show (E : Set (Mbar9 D)) * (S1Nine D L : Set (Mbar9 D)) =
          (S1Nine D L : Set (Mbar9 D)) * (E : Set (Mbar9 D))
        exact hEperm)
  have hXbarNe : Xbar ≠ ⊥ := by
    intro hbot
    have hEbot : E ≤ (⊥ : Subgroup (Mbar9 D)) := hbot ▸ hEXbar
    exact hEne (le_bot_iff.mp hEbot)
  have hXbarNcyc : ¬ IsCyclic ↥Xbar := by
    intro hcyc
    letI := hcyc
    exact hEncyc (isCyclic_of_injective (Subgroup.inclusion hEXbar)
      (Subgroup.inclusion_injective hEXbar))
  have hTsub2 : IsPGroup 2 (D.T.subgroupOf D.M) :=
    D.sylowM.isPGroup.comap_subtype (K := D.M)
  have hker : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)).ker ≤ D.T.subgroupOf D.M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx1 : (QuotientGroup.mk x : Mbar9 D) = 1 := hx
    exact s16c7_pCoreOf_le_of_isSylowOf D.sylowM
      ((mk_eq_one_iff_mem_pCoreOf x).mp hx1)
  have hSmap : (D.T.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) =
      Tbar9 D := rfl
  obtain ⟨P, hP3, hPmap, ⟨eP⟩, hPperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3)
      (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M))
      (QuotientGroup.mk'_surjective _) hTsub2 hker (by norm_num : (3 : ℕ) ≠ 2)
      (hXbarP 3 hEp) (by rw [hSmap]; exact hXbarT)
  refine ⟨P.map D.M.subtype, Subgroup.map_subtype_le P, ?_, hP3.map D.M.subtype, ?_, ?_, ?_⟩
  · intro hbot
    have hPbot : P = ⊥ := by
      refine Subgroup.map_injective (f := D.M.subtype) Subtype.val_injective ?_
      simpa using hbot
    have hcard : Nat.card Xbar = 1 := by
      have h := Nat.card_congr eP.toEquiv
      rw [hPbot, Subgroup.card_bot] at h
      exact h.symm
    exact hXbarNe ((Subgroup.card_eq_one).mp hcard)
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy3 : (⟨y, hy⟩ : ↥P) ^ 3 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hXbarExp 3 hEexp _ (eP ⟨y, hy⟩).2)
    simpa using congrArg (fun z : ↥P => ((z : ↥D.M) : G)) hy3
  · intro hcyc
    have hPcyc : IsCyclic ↥P := by
      let e := Subgroup.equivMapOfInjective P D.M.subtype Subtype.val_injective
      letI := hcyc
      exact isCyclic_of_surjective e.symm e.symm.surjective
    letI := hPcyc
    exact hXbarNcyc (isCyclic_of_surjective eP eP.surjective)
  ·
    have hDT : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) = (D.T : Set G) :=
      congrArg (fun H : Subgroup G => (H : Set G)) (Subgroup.map_subgroupOf_eq_of_le hTM)
    have hXcoe : (P.map D.M.subtype : Set G) = D.M.subtype '' (P : Set ↥D.M) := rfl
    have hScoe : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) =
        D.M.subtype '' (D.T.subgroupOf D.M : Set ↥D.M) := rfl
    show ((P.map D.M.subtype : Subgroup G) : Set G) * (D.T : Set G) =
      (D.T : Set G) * ((P.map D.M.subtype : Subgroup G) : Set G)
    rw [hXcoe, ← hDT, hScoe, ← Set.image_mul, ← Set.image_mul, hPperm]

theorem exists_permutes_three_subgroup (hKp : Inputs1719.K_GF3_permutability)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h17_8 : R17_8At D V₀ V L r q hC) (hq3 : q = 3) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  obtain ⟨t, n, hadm, hlie⟩ := lie_three_of_q hC hq3
  obtain ⟨e1⟩ := uc22p21k_barInf_equiv_of_calC hC.memL
  refine exists_permutes_three_of_calC hC.memL fun Y _ _ K hKn hKq _ ⟨e⟩ hcent hidx S hS => ?_
  let eZ : (↥K ⧸ Subgroup.center ↥K) ≃* (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact hKp Y K hKn hKq ⟨t, n, hadm, LieModel.of_mulEquiv (e1.trans eZ.symm) hlie⟩
    ⟨fun h => h17_8.1 (LieModel.of_mulEquiv e h), fun h => h17_8.2 (LieModel.of_mulEquiv e h)⟩
    hcent hidx S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
