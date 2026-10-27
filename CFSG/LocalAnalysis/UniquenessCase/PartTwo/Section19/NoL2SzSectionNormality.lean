module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72ReeMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Rows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Socle
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

private theorem nlszn_card_dvd_card_mulAut {Q : Type} [Group Q] {K : Subgroup Q} [K.Normal]
    (hKC : centralizer (K : Set Q) = ⊥) : Nat.card Q ∣ Nat.card (MulAut ↥K) := by
  refine Subgroup.card_dvd_of_injective (MulAut.conjNormal : Q →* MulAut ↥K) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hKC]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Q)) (MonoidHom.mem_ker.mp hg)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

private theorem nlszn_eq_of_isSimpleGroup {X : Type} [Group X] {A B : Subgroup X}
    [hAn : A.Normal] [hBn : B.Normal] (hAs : IsSimpleGroup ↥A) (hBs : IsSimpleGroup ↥B)
    (hBC : centralizer (B : Set X) = ⊥) : A = B := by
  have := hAs
  refine eq_of_le_of_normal_of_isSimpleGroup ?_ hAs hBs
  have : ((A ⊓ B).subgroupOf A).Normal := (Subgroup.normal_inf_normal A B).subgroupOf A
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ B).subgroupOf A) with hbot | htop
  · exfalso
    have hAB : A ⊓ B = ⊥ := by
      have h := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
      rwa [inf_eq_left.mpr inf_le_left] at h
    apply (Subgroup.nontrivial_iff_ne_bot A).1 inferInstance
    rw [eq_bot_iff, ← hBC]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.commute_of_normal_of_disjoint A B hAn hBn (disjoint_iff.mpr hAB) a b ha
      hb).symm.eq
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

private theorem nlszn_pPrimeCore_eq_bot {Q : Type} [Group Q] {p : ℕ} (hp : p.Prime)
    {K Y : Subgroup Q} [hKn : K.Normal] (hKY : K ≤ Y) (hKs : IsSimpleGroup ↥K)
    (hKC : centralizer (K : Set Q) = ⊥) (hpK : p ∣ Nat.card K) :
    CFSG.pPrimeCore p ↥Y = ⊥ := by
  have := hKs
  refine sSup_eq_bot.mpr ?_
  rintro O ⟨hOn, hOp⟩
  let K' : Subgroup ↥Y := K.subgroupOf Y
  have hK'n : K'.Normal := hKn.subgroupOf Y
  have : IsSimpleGroup ↥K' := (Subgroup.subgroupOfEquivOfLe hKY).isSimpleGroup
  have hOK : O ⊓ K' = ⊥ := by
    have : ((O ⊓ K').subgroupOf K').Normal := (Subgroup.normal_inf_normal O K').subgroupOf K'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O ⊓ K').subgroupOf K') with hbot | htop
    · have h := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
      rwa [inf_eq_left.mpr inf_le_right] at h
    · exfalso
      have hK'O : K' ≤ O := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left
      have hKK' : Nat.card K = Nat.card K' :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv).symm
      have hdvd : p ∣ Nat.card O :=
        (hpK.trans (dvd_of_eq hKK')).trans (Subgroup.card_dvd_of_le hK'O)
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hOp hdvd)
  rw [eq_bot_iff]
  intro x hx
  have hxC : (x : Q) ∈ centralizer (K : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (⟨k, hKY hk⟩ : ↥Y) ∈ K' := Subgroup.mem_subgroupOf.mpr hk
    have hc := Subgroup.commute_of_normal_of_disjoint O K' hOn hK'n (disjoint_iff.mpr hOK) x _
      hx hk'
    exact (congrArg Subtype.val hc.eq).symm
  rw [hKC, Subgroup.mem_bot] at hxC
  exact Subgroup.mem_bot.mpr (Subtype.ext hxC)

private theorem nlszn_normal_of_card {Q : Type} [Group Q] [Finite Q] {K Y : Subgroup Q}
    [hKn : K.Normal] (hKY : K ≤ Y) (hK : Nat.card K = 504) (hQ : Nat.card Q ∣ 1512) :
    Y.Normal := by
  have hidx : K.relIndex Y * Y.index ∣ 3 := by
    rw [Subgroup.relIndex_mul_index hKY]
    rw [← Subgroup.card_mul_index K, hK] at hQ
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) (hQ.trans (by norm_num))
  rcases (Nat.dvd_prime Nat.prime_three).mp (dvd_of_mul_right_dvd hidx) with h1 | h3
  · rw [le_antisymm (Subgroup.relIndex_eq_one.mp h1) hKY]
    exact hKn
  · rw [h3] at hidx
    have h31 : 3 * Y.index ∣ 3 * 1 := by rwa [mul_one]
    have h1 : Y.index = 1 := Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h31)
    rw [Subgroup.index_eq_one.mp h1]
    infer_instance

private theorem nlszn_normal_of_isSimpleGroup {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup Q} (hFY : genFittingFStar Q ≤ Y)
    (hO : CFSG.pPrimeCore p Q = ⊥) {N : Subgroup Q} (hN : IsStronglyPEmbedded p N)
    (hYs : IsSimpleGroup ↥Y) : Y.Normal := by
  obtain ⟨hKs, -, hKn, -⟩ := kf7_setup hp hp2 hO (L := ⊤) inferInstance le_top hN
  rw [← @eq_of_le_of_normal_of_isSimpleGroup _ _ _ _ hKn hFY hKs hYs]
  exact hKn

private theorem nlszn_nonempty_mulEquiv {Q S : Type} [Group Q] [Group S] [Finite S]
    [IsSimpleGroup S] (hSnab : ∃ a b : S, a * b ≠ b * a) {K Y : Subgroup Q} [hKn : K.Normal]
    (hKY : K ≤ Y) (hKs : IsSimpleGroup ↥K) (eY : ↥Y ≃* MulAut S) : Nonempty (↥K ≃* S) := by
  have := hKs
  have : IsSimpleGroup ↥(K.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hKY).isSimpleGroup
  have hK'eq : (K.subgroupOf Y).map eY.toMonoidHom = CFSG.Fischer.innerAut S := by
    change _ = (MulAut.conj : S →* MulAut S).range
    exact eq_inner_of_normal_simple_subgroup_mulAut hSnab
      ((hKn.subgroupOf Y).map eY.toMonoidHom eY.surjective)
      (eY.subgroupMap (K.subgroupOf Y)).symm.isSimpleGroup
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hSnab
      have ha : a ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  exact ⟨((Subgroup.subgroupOfEquivOfLe hKY).symm.trans (eY.subgroupMap (K.subgroupOf Y))).trans
    ((MulEquiv.subgroupCongr hK'eq).trans (CFSG.Fischer.innerAutEquiv hZ).symm)⟩

private theorem nlszn_normal_of_isAutSz {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup Q} (hFY : genFittingFStar Q ≤ Y)
    (hO : CFSG.pPrimeCore p Q = ⊥) {N : Subgroup Q} (hN : IsStronglyPEmbedded p N)
    (hY : F07.IsAutSz ↥Y 5) : Y.Normal := by
  obtain ⟨S, hSgrp, hSz, ⟨eY⟩⟩ := hY
  let : Group S := hSgrp
  have : Finite S := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hSz
  have : IsSimpleGroup S := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  obtain ⟨hKs, -, hKn, hKC, -⟩ := kf7_setup hp hp2 hO (L := ⊤) inferInstance le_top hN
  have := hKn
  obtain ⟨eK⟩ := nlszn_nonempty_mulEquiv
    (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz) hFY hKs eY
  have hdvd : Nat.card Q ∣ Nat.card Y := by
    have h := nlszn_card_dvd_card_mulAut hKC
    rwa [Nat.card_congr (MulAut.congr eK).toEquiv, ← Nat.card_congr eY.toEquiv] at h
  rw [Subgroup.eq_top_of_card_eq Y (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card Y) hdvd)]
  infer_instance

private theorem nlszn_normal_of_isReeType
    {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q} (hFY : genFittingFStar Q ≤ Y)
    (hO : CFSG.pPrimeCore 3 Q = ⊥) (hRee : F07.IsReeType ↥Y 1) {N : Subgroup Q}
    (hN : IsStronglyPEmbedded 3 N) : Y.Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKs, -, hKn, hKC, P, -, hPN, hPK, -, -, hne⟩ :=
    kf7_setup Nat.prime_three (by norm_num) hO (L := ⊤) inferInstance le_top hN
  have := hKn
  have h3PK : 3 ∣ Nat.card (P ⊓ genFittingFStar Q : Subgroup Q) := by
    rcases (P.isPGroup'.to_inf_left (K := genFittingFStar Q)).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hPK
    · exact h
  have hYO : CFSG.pPrimeCore 3 ↥Y = ⊥ := nlszn_pPrimeCore_eq_bot Nat.prime_three hFY hKs hKC
    (h3PK.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hYN : ¬ Y ≤ N := fun h => hne (Subgroup.subgroupOf_eq_top.mpr (hFY.trans h))
  have hN' : IsStronglyPEmbedded 3 ((Y ⊓ N).subgroupOf Y) := hN.subgroupOf hYN
    (h3PK.trans (Subgroup.card_dvd_of_le (le_inf (inf_le_right.trans hFY) (inf_le_left.trans hPN))))
  obtain ⟨e⟩ := kf7_reeType_one_recognition hYO (L := ⊤) inferInstance le_top
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.isReeType_of_mulEquiv
      Subgroup.topEquiv.symm hRee) hN'
  obtain ⟨hFs, -, hFn, hFC, -⟩ :=
    kf7_setup Nat.prime_three (by norm_num) hYO (L := ⊤) inferInstance le_top hN'
  have := hFn
  have : ((genFittingFStar Q).subgroupOf Y).Normal := hKn.subgroupOf Y
  have hKF := nlszn_eq_of_isSimpleGroup
    (@MulEquiv.isSimpleGroup _ _ _ _ hKs (Subgroup.subgroupOfEquivOfLe hFY)) hFs hFC
  let eK : ↥(genFittingFStar Q) ≃* CFSG.Quasithin.F6.L28Res.G8 :=
    (Subgroup.subgroupOfEquivOfLe hFY).symm.trans ((MulEquiv.subgroupCongr hKF).trans e)
  refine nlszn_normal_of_card hFY ?_ ?_
  · rw [Nat.card_congr eK.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]
  · have h := nlszn_card_dvd_card_mulAut hKC
    rwa [Nat.card_congr (MulAut.congr eK).toEquiv, CFSG.Quasithin.F6.L28Res.card_mulAut] at h

theorem normal_of_r72Shape_of_isStronglyPEmbedded
    {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup Q} (hFY : genFittingFStar Q ≤ Y)
    (hO : CFSG.pPrimeCore p Q = ⊥) (hY : R72Shape p ↥Y) {N : Subgroup Q}
    (hN : IsStronglyPEmbedded p N) : Y.Normal := by
  have hs := nlszn_normal_of_isSimpleGroup hp hp2 hFY hO hN
  rcases hY with ⟨_, hPSL⟩ | ⟨_, hPSU⟩ | ⟨hp3, hRee | hM11 | hL3⟩ |
    ⟨-, hAutSz | hTits | hMcL | hAlt⟩ | ⟨-, hJ4⟩
  · exact hs (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hPSL)
  · exact hs (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hPSU)
  · subst hp3
    exact nlszn_normal_of_isReeType hFY hO hRee hN
  · obtain ⟨e⟩ := hM11
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
      CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    exact hs e.isSimpleGroup
  · exact hs (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3)
  · exact nlszn_normal_of_isAutSz hp hp2 hFY hO hN hAutSz
  · exact hs (CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.simple_of_lieModel hTits).1
  · obtain ⟨e⟩ := hMcL
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
      CFSG.Sporadic.McL.isSimpleGroup_McL
    exact hs e.isSimpleGroup
  · have : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
    exact hs hAlt.some.isSimpleGroup
  · obtain ⟨e⟩ := hJ4
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
      CFSG.Sporadic.J4.isSimpleGroup_J4
    exact hs e.isSimpleGroup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
