module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Common
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Struct
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.Models.Blueprint
import CFSG.CGT.Foote82.T66.BranchAGen
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.GroupTheory.PrimeCorefreeQuasisimple
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.CGT.Foote82.D1Steps
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
import CFSG.GroupTheory.ComponentCovering
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.ClassicalInvolution.RouteD.GapsPerfect
import CFSG.HardMathSupport.Malle.E27Lie.Cross.PerfectQuotient
import CFSG.GroupTheory.Fitting.LayerContainment
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSL3 IsSU3)

@[expose] def R875Ex {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H →
    ∃ K : Subgroup G, IsComponentOf K H ∧ 3 ∣ Nat.card K ∧
      ¬ X ≤ Subgroup.centralizer (K : Set G)

@[expose] def R875Le {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → ∀ K : Subgroup G, IsComponentOf K H →
    3 ∣ Nat.card K → ¬ X ≤ Subgroup.centralizer (K : Set G) → X ≤ K

@[expose] def R875NotLe {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → ∀ K : Subgroup G, IsComponentOf K H → X ≤ K →
    ¬ K ≤ D.M

@[expose] def R875QNorm {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → ∀ Q : Subgroup G,
    IsSylowOf 3 Q (H ⊓ D.M) → IsSylowOf 3 (Q ⊓ X) X → Q ≤ Subgroup.normalizer (X : Set G)

theorem r875_of_parts {G : Type} [Group G] [Finite G] {D : Data G} (hEx : R875Ex D)
    (hLe : R875Le D) (hNotLe : R875NotLe D) : R875 D := by
  intro L X H hmin
  obtain ⟨K, hK, h3, hc⟩ := hEx L X H hmin
  have hXK := hLe L X H hmin K hK h3 hc
  exact ⟨K, hK, hXK, hNotLe L X H hmin K hK hXK⟩

private theorem r875c_subnormal_of_hyp869 {G : Type} [Group G] [Finite G] {D : Data G} {L X : Subgroup G}
    (h : Hyp869 D L X) : IsSubnormal L D.M := by
  rcases h.1 with hL | ⟨hLM, hn, -⟩
  · exact hL.1
  · exact IsSubnormal.step hLM ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hn)
      (IsSubnormal.refl D.M)

private theorem r875c_le_M_of_hyp869 {G : Type} [Group G] [Finite G] {D : Data G} {L X : Subgroup G}
    (h : Hyp869 D L X) : L ≤ D.M := IsSubnormal.le (r875c_subnormal_of_hyp869 h)

private theorem r875c_subnormal_inf {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (h : Hyp869 D L X) : IsSubnormal (L ⊓ H) (H ⊓ D.M) := by
  have hsub := IsSubnormal.inf (r875c_subnormal_of_hyp869 h) H
  rw [inf_comm D.M H] at hsub
  exact hsub

private theorem r875c_pCoreOf_inf_eq_bot {G : Type} [Group G] [Finite G] {D : Data G}
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) (hO2 : R875O2HM D) :
    pCoreOf 2 L ⊓ H = ⊥ := by
  have hsub : IsSubnormal (L ⊓ H) (H ⊓ D.M) := r875c_subnormal_inf hmin.hyp
  have hS : pCoreOf 2 L ⊓ H ≤ pCoreOf 2 (L ⊓ H) := by
    refine CFSG.CGT.Foote82.le_pCoreOf_of_normalizes ?_ ?_ ?_
    · exact le_inf (inf_le_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L))
        inf_le_right
    · refine (inf_le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      · exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
      · exact Subgroup.le_normalizer
    · exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hstep : pCoreOf 2 (L ⊓ H) ≤ pCoreOf 2 (H ⊓ D.M) :=
    CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hsub
  rw [hO2 L X H hmin] at hstep
  exact le_bot_iff.mp (hS.trans hstep)

private theorem r875c_inf_eq_X {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) (hbot : pCoreOf 2 L ⊓ H = ⊥) : L ⊓ H = X := by
  refine le_antisymm ?_ (le_inf hmin.hyp.2.1 hmin.mem.2)
  intro l hl
  have hle : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hmin.hyp.2.1.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right X (pCoreOf 2 L) hle
  have hl' : l ∈ (↑(X ⊔ pCoreOf 2 L) : Set G) := by
    rw [hmin.hyp.2.2.1]
    exact hl.1
  rw [hcoe, Set.mem_mul] at hl'
  obtain ⟨x, hx, o, ho, hxo⟩ := hl'
  have ho_eq : o = x⁻¹ * l := by rw [← hxo]; group
  have hoH : o ∈ H := by
    rw [ho_eq]
    exact H.mul_mem (H.inv_mem (hmin.mem.2 hx)) hl.2
  have hoS : o ∈ pCoreOf 2 L ⊓ H := ⟨ho, hoH⟩
  rw [hbot] at hoS
  have ho1 : o = 1 := Subgroup.mem_bot.mp hoS
  rw [← hxo, ho1, mul_one]
  exact hx

theorem r875Comp_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (h873 : R873 D)
    (hO2 : R875O2HM D) : R875Comp D := by
  intro L X H hmin
  have hXL : X ≤ L := hmin.hyp.2.1
  have hXH : X ≤ H := hmin.mem.2
  have hLM : L ≤ D.M := r875c_le_M_of_hyp869 hmin.hyp
  have hbot : pCoreOf 2 L ⊓ H = ⊥ := r875c_pCoreOf_inf_eq_bot hmin hO2
  have heq : L ⊓ H = X := r875c_inf_eq_X hmin hbot
  have hsub : IsSubnormal (L ⊓ H) (H ⊓ D.M) := r875c_subnormal_inf hmin.hyp
  exact ⟨le_inf hXH (hXL.trans hLM), heq ▸ hsub, (h873 L X H hmin).1.elim (·.1) (·.1)⟩

private theorem r875ex_subgroupOf_centralizer_map {G : Type} [Group G] {X H : Subgroup G}
    (_hXH : X ≤ H) {K : Subgroup ↥H}
    (h : X ≤ Subgroup.centralizer ((K.map H.subtype : Subgroup G) : Set G)) :
    X.subgroupOf H ≤ Subgroup.centralizer (K : Set ↥H) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hkK : (k : G) ∈ K.map H.subtype := ⟨k, hk, rfl⟩
  have hc := (Subgroup.mem_centralizer_iff.mp (h hxX)) (k : G) hkK
  exact Subtype.ext hc

private theorem r875ex_component_le_pPrimeCore {G : Type} [Group G] [Finite G] {K H : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K H) (hcop : Nat.Coprime 3 (Nat.card K)) :
    K ≤ (CFSG.pPrimeCore 3 ↥H).map H.subtype := by
  have hKH : K ≤ H := hK.1
  have hcomp : CFSG.IsComponent (K.subgroupOf H) :=
    CFSG.CGT.Foote82.BranchAAux.isComponent_subgroupOf hK
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    CFSG.natCard_subgroupOf_eq K H hKH
  have hcop' : Nat.Coprime 3 (Nat.card (K.subgroupOf H)) := by rw [hcard]; exact hcop
  have hle : K.subgroupOf H ≤ CFSG.pPrimeCore 3 ↥H :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hcomp.2 hcop'
  rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono hle

theorem r875Ex_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (h873 : R873M3 D)
    (h874 : R874 D) (h875c : R875Comp D) : R875Ex D := by
  intro L X H hmin
  classical
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hXHM : X ≤ H ⊓ D.M := (h875c L X H hmin).1
  have hXH : X ≤ H := hXHM.trans inf_le_left
  obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 X
  have hP₀HM : P₀ ≤ H ⊓ D.M := hP₀.le.trans hXHM
  obtain ⟨S, hP₀S⟩ := (hP₀.isPGroup.comap_subtype (K := H ⊓ D.M)).exists_le_sylow
  let Q : Subgroup G := (S : Subgroup ↥(H ⊓ D.M)).map (H ⊓ D.M).subtype
  have hQ : IsSylowOf 3 Q (H ⊓ D.M) := ⟨S, rfl⟩
  have hP₀Q : P₀ ≤ Q := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hP₀HM]
    exact Subgroup.map_mono hP₀S
  have hQXle : Q ⊓ X ≤ X := inf_le_right
  have hQXpg : IsPGroup 3 ↥(Q ⊓ X) := hQ.isPGroup.to_inf_left
  have hP₀QX : P₀ ≤ Q ⊓ X := le_inf hP₀Q hP₀.le
  have hQXeq : Q ⊓ X = P₀ :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hP₀ hP₀QX hQXle hQXpg
  have hP : IsSylowOf 3 (Q ⊓ X) X := by rw [hQXeq]; exact hP₀
  obtain ⟨hQsyl, hΓP⟩ := h874 L X H hmin Q hQ hP
  have h873h : 2 ≤ CFSG.Open.pRank 3 X := h873 L X H hmin
  have hPle : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 (Q ⊓ X) :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hP.le hP le_rfl
  have hPrank : 2 ≤ CFSG.Open.pRank 3 (Q ⊓ X) := h873h.trans hPle
  obtain ⟨z, hzP, hzord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three
      (H := Q ⊓ X) (by omega)
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨E, hzE, hEP, hEab, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      (B := Q ⊓ X) (X := Subgroup.zpowers z) hP.isPGroup hPrank
      (Subgroup.zpowers_le.mpr hzP) hzcard
  have hEM : E ≤ D.M := hEP.trans (inf_le_left.trans (hQ.le.trans inf_le_right))
  have hΓE : rankThreeGamma 1 3 E ≤ D.M := by
    have hmono : rankThreeGamma 1 3 E ≤ rankThreeGamma 1 3 (Q ⊓ X) := by
      simpa [CFSG.Open.rankThreeGamma] using
        CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hEP
    exact hmono.trans hΓP
  have hEH : E ≤ H := hEP.trans (hP.le.trans hXH)
  have hEQ : E ≤ Q := hEP.trans inf_le_left
  let V : Subgroup G := (CFSG.pPrimeCore 3 ↥H).map H.subtype
  have hVH : V ≤ H := Subgroup.map_subtype_le _
  have hVsubH : V.subgroupOf H = CFSG.pPrimeCore 3 ↥H := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hVnormH : (V.subgroupOf H).Normal := hVsubH.symm ▸ CFSG.pPrimeCore_normal
  have hHN : H ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mp hVnormH
  have hVE : E ≤ Subgroup.normalizer (V : Set G) := hEH.trans hHN
  have hVcop : Nat.Coprime 3 (Nat.card V) := by
    dsimp only [V]
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
  have hVgen : (⨆ (a : G) (_ : a ∈ E) (_ : a ≠ 1),
      V ⊓ Subgroup.centralizer ({a} : Set G)) = V :=
    CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_three
      hEab (by rw [hEcard]) hVE hVcop
  have hterm : ∀ a ∈ E, a ≠ 1 → V ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M := by
    intro a haE ha1
    have hcent : Subgroup.centralizer ({a} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a) := by
      have ha3 : a ^ 3 = 1 := hEab.2 a haE
      have hcard : Nat.card (Subgroup.zpowers a) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
      exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl
        (CFSG.Open.isElemAbelian_zpowers ha3) (k := 1) (by rw [hcard, pow_one])
    have hnorm : Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤
        rankThreeGamma 1 3 E :=
      CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
        (p := 3) (k := 1) (Subgroup.zpowers_le.mpr haE) h1
    refine (inf_le_right.trans ?_).trans (hnorm.trans hΓE)
    rw [hcent]
    exact Subgroup.centralizer_le_normalizer _
  have hVM : V ≤ D.M := by
    rw [← hVgen]
    exact iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => hterm a haE ha1
  have hVLE : V ≤ H ⊓ D.M := le_inf hVH hVM
  have hVnormLM : (V.subgroupOf (H ⊓ D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVLE).mpr (inf_le_left.trans hHN)
  have h3dvdX : 3 ∣ Nat.card X := by
    have hEX : E ≤ X := hEP.trans inf_le_right
    have h3E : 3 ∣ Nat.card E := by rw [hEcard]; exact dvd_pow_self 3 (by norm_num)
    exact h3E.trans (Subgroup.card_dvd_of_le hEX)
  obtain hXV | hXV :=
    CFSG.CGT.Foote82.BranchAAux.le_or_commute_of_normal
      (h875c L X H hmin) hVLE hVnormLM
  · exfalso
    have hnotdvd : ¬ 3 ∣ Nat.card V := (Nat.prime_three.coprime_iff_not_dvd).mp hVcop
    exact hnotdvd (h3dvdX.trans (Subgroup.card_dvd_of_le hXV))
  have hXVc : X ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXV
  let U : Subgroup G := pCoreOf 3 H
  have hUH : U ≤ H := Subgroup.map_subtype_le _
  have hUsubH : U.subgroupOf H = CFSG.pCore 3 ↥H := by
    dsimp only [U, CFSG.Open.pCoreOf]
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hUnormH : (U.subgroupOf H).Normal := hUsubH.symm ▸ CFSG.pCore_normal
  have hUQ : U ≤ Q := by
    obtain ⟨T, hT⟩ := hQsyl
    have hcore := CFSG.Glauberman.pCore_le_sylow T
    rw [← hT]
    exact Subgroup.map_mono hcore
  have hULE : U ≤ H ⊓ D.M := le_inf hUH (hUQ.trans (hQ.le.trans inf_le_right))
  have hUnormLM : (U.subgroupOf (H ⊓ D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hULE).mpr
      (inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp hUnormH))
  obtain hXU | hXU :=
    CFSG.CGT.Foote82.BranchAAux.le_or_commute_of_normal
      (h875c L X H hmin) hULE hUnormLM
  · exfalso
    have hUpg : IsPGroup 3 U := (CFSG.pCore_isPGroup (p := 3) (G := ↥H)).map H.subtype
    have hUX : X ≤ U := hXU
    have : Group.IsNilpotent ↥U := hUpg.isNilpotent
    have hXsol : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hUX)
    exact (CFSG.CGT.Foote82.BranchAAux.not_isSolvable_of_isQuasisimple
      (h875c L X H hmin).2.2) hXsol
  have hXUc : X ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXU
  let Q' : Subgroup ↥H :=
    (CFSG.pPrimeCore 3 (CFSG.fittingSubgroup ↥H)).map (CFSG.fittingSubgroup ↥H).subtype
  have hQ'norm : Q'.Normal := by
    dsimp [Q']
    infer_instance
  have hQ'cop : Nat.Coprime 3 (Nat.card Q') := by
    dsimp [Q']
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(CFSG.fittingSubgroup ↥H))
  have hQ'le : Q' ≤ CFSG.pPrimeCore 3 ↥H :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal hQ'norm hQ'cop
  have hWleV : Q'.map H.subtype ≤ V := Subgroup.map_mono hQ'le
  have hXQ' : X ≤ Subgroup.centralizer ((Q'.map H.subtype : Subgroup G) : Set G) :=
    hXVc.trans (Subgroup.centralizer_le (by intro x hx; exact hWleV hx))
  have hF_eq : CFSG.fittingSubgroupOf H = U ⊔ Q'.map H.subtype :=
    CFSG.GorensteinWalter.fittingSubgroupOf_eq_qCore_sup_pPrimeCore_map H 3
  have hXcentFit : X ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf H : Set G) := by
    rw [hF_eq, Subgroup.le_centralizer_iff]
    exact sup_le ((Subgroup.le_centralizer_iff).mpr hXUc)
      ((Subgroup.le_centralizer_iff).mpr hXQ')
  have hXcentFit' : X.subgroupOf H ≤
      Subgroup.centralizer (CFSG.fittingSubgroup ↥H : Set ↥H) :=
    r875ex_subgroupOf_centralizer_map hXH (by simpa [CFSG.fittingSubgroupOf] using hXcentFit)
  have hcomp_cent : ∀ K' : Subgroup ↥H, CFSG.IsComponent K' →
      X.subgroupOf H ≤ Subgroup.centralizer (K' : Set ↥H) := by
    intro K' hK'
    have hKH : K'.map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hKsub : (K'.map H.subtype).subgroupOf H = K' := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have hKcomp : CFSG.Open.IsComponentOf (K'.map H.subtype) H :=
      CFSG.Assembly.isComponentOf_iff_open.mp
        ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKH).mpr
          (by rw [hKsub]; exact hK'))
    have hXK : X ≤ Subgroup.centralizer ((K'.map H.subtype : Subgroup G) : Set G) := by
      by_cases h3 : 3 ∣ Nat.card (K'.map H.subtype)
      · exact hcon _ hKcomp h3
      · have hcop : Nat.Coprime 3 (Nat.card (K'.map H.subtype)) :=
          (Nat.prime_three.coprime_iff_not_dvd).mpr h3
        have hKV : K'.map H.subtype ≤ V := r875ex_component_le_pPrimeCore hKcomp hcop
        exact hXVc.trans (Subgroup.centralizer_le (by intro x hx; exact hKV hx))
    exact r875ex_subgroupOf_centralizer_map hXH hXK
  have hlayer : X.subgroupOf H ≤ Subgroup.centralizer (CFSG.layer ↥H : Set ↥H) := by
    rw [CFSG.layer.eq_sSup, Subgroup.le_centralizer_iff]
    exact sSup_le fun K' hK' => (Subgroup.le_centralizer_iff).mpr (hcomp_cent K' hK')
  have hcentGF : X.subgroupOf H ≤
      Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.le_centralizer_iff]
    exact sup_le ((Subgroup.le_centralizer_iff).mpr hXcentFit')
      ((Subgroup.le_centralizer_iff).mpr hlayer)
  have hXFS : X.subgroupOf H ≤ CFSG.generalizedFitting ↥H :=
    hcentGF.trans (CFSG.centralizer_generalizedFitting_le ↥H)
  have hXcomm : IsMulCommutative ↥(X.subgroupOf H) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (hcentGF.trans (Subgroup.centralizer_le (by intro x hx; exact hXFS hx)))
  have hXsol_sub : Group.IsSolvable ↥(X.subgroupOf H) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hXcomm)
  have : Group.IsSolvable ↥(X.subgroupOf H) := hXsol_sub
  have hXsol : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXH).symm.toMonoidHom)
      (by
        intro a b h
        exact (Subgroup.subgroupOfEquivOfLe hXH).symm.injective h)
  exact (CFSG.CGT.Foote82.BranchAAux.not_isSolvable_of_isQuasisimple
    (h875c L X H hmin).2.2) hXsol

private theorem r875nl_isComponentOf_map_subtype {G : Type} [Group G] {H : Subgroup G}
    {L : Subgroup ↥H} (hL : CFSG.Open.IsComponentOf L ⊤) :
    CFSG.Open.IsComponentOf (L.map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
  · have hsub := hL.2.1.map H.subtype
    simpa [Subgroup.map_top, Subgroup.range_subtype] using hsub
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm hL.2.2

private theorem r875nl_isComponentOf_subgroupOf_top {G : Type} [Group G] {H C : Subgroup G}
    (hC : CFSG.Open.IsComponentOf C H) :
    CFSG.Open.IsComponentOf (C.subgroupOf H) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · rw [CFSG.Open.IsSubnormal.top_iff]
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf hC.1).mp hC.2.1
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC.1) hC.2.2

private theorem r875nl_elayer_eq_layer {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    sSup {C : Subgroup G | CFSG.Open.IsComponentOf C H} =
      (CFSG.Open.genFittingLayer ↥H).map H.subtype := by
  refine le_antisymm ?_ ?_
  · rw [CFSG.Open.genFittingLayer.eq_sSup]
    refine sSup_le ?_
    intro C hC
    have hCsub : (C.subgroupOf H).map H.subtype = C := Subgroup.map_subgroupOf_eq_of_le hC.1
    rw [← hCsub]
    exact Subgroup.map_mono (le_sSup (r875nl_isComponentOf_subgroupOf_top hC))
  · rw [Subgroup.map_le_iff_le_comap]
    rw [CFSG.Open.genFittingLayer.eq_sSup]
    refine sSup_le ?_
    intro L hL
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (r875nl_isComponentOf_map_subtype hL)

private theorem r875nl_eq_of_isComponentOf_le {G : Type} [Group G] [Finite G]
    {H M X K : Subgroup G} (hX : CFSG.Open.IsComponentOf X (H ⊓ M))
    (hK : CFSG.Open.IsComponentOf K H) (hKM : K ≤ M) (hXK : X ≤ K) : X = K := by
  have hKcompM : CFSG.Open.IsComponentOf K (H ⊓ M) :=
    CFSG.Assembly.isComponentOf_iff_open.mp
      (CFSG.Assembly.IsComponentOf.of_le_of_le
        (CFSG.Assembly.isComponentOf_iff_open.mpr hK) (le_inf hK.1 hKM) inf_le_left)
  rcases CFSG.CGT.Foote82.BranchAAux.eq_or_commute_of_isComponentOf hX hKcompM with h | h
  · exact h
  · exfalso
    have hXX : ⁅X, X⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hXK).trans (le_of_eq h))
    have hperf : ⁅X, X⁆ = X :=
      CFSG.ComponentClassification.Asc76.Sec5.commutator_self_of_isQuasisimple hX.2.2
    have hXbot : X = ⊥ := by rw [← hperf, hXX]
    have : Nontrivial ↥X := CFSG.ComponentClassification.Quasisimple.nontrivial hX.2.2
    have hsub : Subsingleton ↥X := by rw [hXbot]; infer_instance
    exact not_subsingleton ↥X hsub

private theorem r875nl_mem_uniqueSet_of_isSubnormal {G : Type} [Group G] [Finite G]
    {M : Subgroup G} (hmax : rankThreeIsMaxTwoLocal M) :
    ∀ {A B : Subgroup G}, CFSG.Open.IsSubnormal A B →
      A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M →
        B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  intro A B hsub
  induction hsub with
  | refl => exact fun hA => hA
  | @step A B C hAB hnorm _ ih =>
    intro hA
    have hNB : B ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hnorm
    have hBM : B ≤ M :=
      hNB.trans (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hmax hA)
    exact ih (CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hA hAB hBM)

private theorem r875nl_pPrimeCore_map_le_M {G : Type} [Group G] [Finite G]
    {H M E : Subgroup G} (hEH : E ≤ H) (hEab : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) (hΓE : rankThreeGamma 1 3 E ≤ M) :
    (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set V : Subgroup G := (CFSG.pPrimeCore 3 ↥H).map H.subtype with hV
  have hVcop : Nat.Coprime 3 (Nat.card V) := by
    have hcard : Nat.card V = Nat.card (CFSG.pPrimeCore 3 ↥H) := by
      rw [hV]; exact Subgroup.card_map_of_injective H.subtype_injective
    rw [hcard]; exact CFSG.pPrimeCore_coprime_card
  have hVnorm : H ≤ Subgroup.normalizer (V : Set G) := by
    have hVsub : V.subgroupOf H = CFSG.pPrimeCore 3 ↥H := by
      rw [hV]; exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hN : (CFSG.pPrimeCore 3 ↥H).Normal := CFSG.pPrimeCore_normal
    have : (V.subgroupOf H).Normal := hVsub ▸ hN
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by rw [hV]; exact Subgroup.map_subtype_le _)).mp this
  have hAX : E ≤ Subgroup.normalizer (V : Set G) := hEH.trans hVnorm
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    Nat.prime_three hEab (by norm_num [hEcard]) hAX hVcop
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  have hQP : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.mpr ha
  have hord : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hEab.2 a ha)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h (fun h => ha1 (orderOf_eq_one_iff.mp h))
    · exact h
  have hzrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a) := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      (CFSG.Open.isElemAbelian_zpowers (hEab.2 a ha)) ?_
    rw [Nat.card_zpowers, hord]; norm_num
  have hEq : Subgroup.centralizer (Subgroup.zpowers a : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcentral : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [← hEq]
    exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G)
  exact (inf_le_right.trans hcentral).trans
    ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQP hzrank).trans
      (by simpa [CFSG.Open.rankThreeGamma] using hΓE))

private theorem r875nl_fitting_le_M {G : Type} [Group G] [Finite G]
    {H M Q : Subgroup G} (hV : (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ M)
    (hQH : IsSylowOf 3 Q H) (hQM : Q ≤ M) :
    CFSG.fittingSubgroupOf H ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [show CFSG.fittingSubgroupOf H = CFSG.GorensteinWalter.fittingSubgroupOf H from rfl,
    CFSG.GorensteinWalter.fittingSubgroupOf_eq_qCore_sup_pPrimeCore_map H 3]
  refine sup_le ?_ ?_
  · obtain ⟨Q₀, hQ₀⟩ := hQH
    have hcore : CFSG.pCore 3 ↥H ≤ (Q₀ : Subgroup ↥H) := CFSG.Glauberman.pCore_le_sylow Q₀
    have hmap := Subgroup.map_mono (f := H.subtype) hcore
    have hq : CFSG.GorensteinWalter.qCoreOf H 3 ≤ Q := by
      rw [CFSG.GorensteinWalter.qCoreOf]
      exact hmap.trans (le_of_eq hQ₀)
    exact hq.trans hQM
  · have hle := CFSG.pPrimeCore_map_subtype_le_pPrimeCore_of_normal (G := ↥H) (p := 3)
      (fittingSubgroup ↥H)
    have hstep : ((CFSG.pPrimeCore 3 ↥(fittingSubgroup ↥H)).map
        (fittingSubgroup ↥H).subtype).map H.subtype ≤
        (CFSG.pPrimeCore 3 ↥H).map H.subtype :=
      Subgroup.map_mono (f := H.subtype) hle
    exact hstep.trans hV

private theorem r875nl_layer_le_M {G : Type} [Group G] [Finite G]
    {H M K P : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) (hKM : K ≤ M)
    (hSyl : IsSylowOf 3 P K) (hPrank : 1 ≤ CFSG.Open.pRank 3 P)
    (hΓ : rankThreeGamma 1 3 P ≤ M) :
    (CFSG.Open.genFittingLayer ↥H).map H.subtype ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hnPM : Subgroup.normalizer (P : Set G) ≤ M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore le_rfl hPrank).trans
      (by simpa [CFSG.Open.rankThreeGamma] using hΓ)
  have hElayerM : sSup {C : Subgroup G | CFSG.Open.IsComponentOf C H} ≤ M := by
    have hKElayer : K ≤ sSup {C : Subgroup G | CFSG.Open.IsComponentOf C H} := le_sSup hK
    have hnorm : sSup {C : Subgroup G | CFSG.Open.IsComponentOf C H} ≤
        Subgroup.normalizer (K : Set G) :=
      CFSG.CGT.Foote82.BranchAAux.sSup_le_normalizer hK
    have hFr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22t_frattini_sup
      (q := 3) hKElayer hnorm hSyl
    exact hFr.trans (sup_le hKM (inf_le_right.trans hnPM))
  rw [← r875nl_elayer_eq_layer H]
  exact hElayerM

private theorem r875nl_fstar_le_M {G : Type} [Group G] [Finite G] {H M : Subgroup G}
    (hF : CFSG.fittingSubgroupOf H ≤ M)
    (hLayer : (CFSG.Open.genFittingLayer ↥H).map H.subtype ≤ M) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H ≤ M := by
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar, CFSG.Open.genFittingFStar.eq_sup,
    Subgroup.map_sup]
  exact sup_le (by simpa [CFSG.Open.genFittingFitting, CFSG.fittingSubgroupOf] using hF) hLayer

theorem r875NotLe_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (h63 : UC6.R6_3 D)
    (h873 : R873M3 D) (h874 : R874 D) (h875c : R875Comp D) : R875NotLe D := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro L X H hmin K hK hXK hKM
  have hXcomp : CFSG.Open.IsComponentOf X (H ⊓ D.M) := h875c L X H hmin
  have hXeqK : X = K := r875nl_eq_of_isComponentOf_le hXcomp hK hKM hXK
  clear hXK
  subst K
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 3) (H ⊓ D.M)
  have hQX : IsSylowOf 3 (Q ⊓ X) X :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal hQ hXcomp.2.1
  have h874' := h874 L X H hmin Q hQ hQX
  have hQH : IsSylowOf 3 Q H := h874'.1
  have hΓP : rankThreeGamma 1 3 (Q ⊓ X) ≤ D.M := h874'.2
  have hQM : Q ≤ D.M := hQ.le.trans inf_le_right
  have hPM : Q ⊓ X ≤ D.M := inf_le_left.trans hQM
  have h873h : 2 ≤ CFSG.Open.pRank 3 X := h873 L X H hmin
  have hPle : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 (Q ⊓ X) :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hQX.le hQX le_rfl
  have hPrank : 2 ≤ CFSG.Open.pRank 3 (Q ⊓ X) := h873h.trans hPle
  obtain ⟨z, hzP, hzord⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank
    Nat.prime_three (H := Q ⊓ X) (by omega)
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨E, hzE, hEP, hEab, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      (B := Q ⊓ X) (X := Subgroup.zpowers z) hQX.isPGroup hPrank
      (Subgroup.zpowers_le.mpr hzP) hzcard
  have hEM : E ≤ D.M := hEP.trans hPM
  have hΓE : rankThreeGamma 1 3 E ≤ D.M := by
    have hmono : rankThreeGamma 1 3 E ≤ rankThreeGamma 1 3 (Q ⊓ X) := by
      simpa [CFSG.Open.rankThreeGamma] using
        CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hEP
    exact hmono.trans hΓP
  have hUniqE : CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E :=
    h63 3 (by norm_num) (by norm_num) E hEM hEab hEcard hΓE
  have hME : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall D.maxLocal hEM
      (fun N hN hEN => by
        have hmem : N ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := ⟨hN, hEN⟩
        rw [hUniqE] at hmem
        exact Set.mem_singleton_iff.mp hmem)
  have hEQ : E ≤ Q := hEP.trans inf_le_left
  have hMQ : Q ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hME hEQ hQM
  have hMP : Q ⊓ X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hME hEP hPM
  have hQHle : Q ≤ H := hQH.le
  have hEH : E ≤ H := hEQ.trans hQHle
  have hVM : (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ D.M :=
    r875nl_pPrimeCore_map_le_M hEH hEab hEcard hΓE
  have hFH : CFSG.fittingSubgroupOf H ≤ D.M := r875nl_fitting_le_M hVM hQH hQM
  have hLayerM : (CFSG.Open.genFittingLayer ↥H).map H.subtype ≤ D.M :=
    r875nl_layer_le_M hK hKM hQX (by omega) hΓP
  have hFstarM : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H ≤ D.M :=
    r875nl_fstar_le_M hFH hLayerM
  have hXF : X ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H := by
    have hxss : X ≤ sSup {C : Subgroup G | CFSG.Open.IsComponentOf C H} := le_sSup hK
    rw [r875nl_elayer_eq_layer H] at hxss
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar, CFSG.Open.genFittingFStar.eq_sup,
      Subgroup.map_sup]
    exact hxss.trans le_sup_right
  have hFstarNorm : H ≤ Subgroup.normalizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H : Set G) := by
    have hN : (CFSG.Open.genFittingFStar ↥H).Normal := by
      rw [CFSG.Adapters.genFittingFStar_eq_foundations]
      exact (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥H)).2
    have hFsub : (CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H).subgroupOf H =
        CFSG.Open.genFittingFStar ↥H := by
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar]
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have : ((CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H).subgroupOf H).Normal := hFsub ▸ hN
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (by
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar]
      exact Subgroup.map_subtype_le _)).mp this
  have hPF : Q ⊓ X ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H :=
    inf_le_right.trans hXF
  obtain ⟨S₀, hPS₀⟩ := (hQX.isPGroup.comap_subtype
    (K := CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H)).exists_le_sylow
  let S : Subgroup G := (S₀ : Subgroup ↥(CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H)).map
    (CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H).subtype
  have hS : IsSylowOf 3 S (CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H) := ⟨S₀, rfl⟩
  have hPS : Q ⊓ X ≤ S := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPF]
    exact Subgroup.map_mono hPS₀
  have hsub : CFSG.Open.IsSubnormal (Q ⊓ X) S :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hPS).2
      (CFSG.BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup hS.isPGroup
        ((Q ⊓ X).subgroupOf S))
  have hMS : S ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    r875nl_mem_uniqueSet_of_isSubnormal D.maxLocal hsub hMP
  have hNSM : Subgroup.normalizer (S : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hMS
  have hHM : H ≤ D.M := by
    have hFr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22t_frattini_sup
      (q := 3) (H := H) (K := CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H) (S := S)
      (Subgroup.map_subtype_le _) hFstarNorm hS
    exact hFr.trans (sup_le hFstarM (inf_le_right.trans hNSM))
  have hMH : D.M ≤ H := by
    rcases (IsCoatom.le_iff hmin.mem.1).mp hHM with h | h
    · exact absurd h (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_M_ne_top D)
    · exact le_of_eq h
  exact hmin.ne (le_antisymm hHM hMH)

theorem card_center_dvd_of_isSL3_or_isSU3 {X : Type} [Group X] [Finite X]
    (hgr : CFSG.Open.GriessAllModelsStatement) (hX : IsSL3 X 2 ∨ IsSU3 X 3) :
    Nat.card (Subgroup.center X) ∣ 48 := by
  rcases hX with hSL | hSU
  ·
    obtain ⟨hq, hL⟩ := hSL
    have hperf : Group.IsPerfect X := Group.isPerfect_def.2 hq.1
    have hdvd : Nat.card (Subgroup.center X) ∣
        Nat.card (griessHopfMultiplier (X ⧸ Subgroup.center X)) :=
      CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf (MulEquiv.refl _)
    obtain ⟨-, ⟨g⟩⟩ := hgr (X ⧸ Subgroup.center X) .PSL 3 2 2
      (CFSG.Models.LieModel.of_blueprint (by decide) hL)
    rw [Nat.card_congr g.toEquiv, Nat.card_prod] at hdvd
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional at hdvd
    simp only [Nat.card_prod, Nat.card_zmod,
      Nat.card_congr (Multiplicative.toAdd : _ ≃ _)] at hdvd
    simp [CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders] at hdvd
    exact hdvd
  ·
    have h3 : Nat.card (Subgroup.center X) ∣ 3 :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.u3Center_of_griess hgr X 3 hSU
    exact h3.trans (by norm_num)

private theorem isSL3_or_isSU3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : IsSL3 A 2 ∨ IsSU3 A 3) :
    IsSL3 B 2 ∨ IsSU3 B 3 := by
  rcases hA with h | h
  · left
    refine ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h.1, ?_⟩
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
        (Subgroup.map_center_eq e)) h.2
  · right
    refine ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h.1, ?_⟩
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
        (Subgroup.map_center_eq e)) h.2

private theorem card_center_map_conj_eq {G : Type} [Group G] {X : Subgroup G} (g : G) :
    Nat.card (Subgroup.center ↥(X.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (Subgroup.center ↥X) :=
  Nat.card_congr (Subgroup.centerCongr
    (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).symm.toEquiv

private theorem card_inf_le_three_of_le_center {G : Type} [Group G] {A B X : Subgroup G}
    (h : A ⊓ B ≤ (Subgroup.center ↥X).map X.subtype)
    (h9 : Nat.card ↥(A ⊓ B) ∣ 9)
    (h48 : Nat.card (Subgroup.center ↥X) ∣ 48) : Nat.card ↥(A ⊓ B) ≤ 3 := by
  have hdvd : Nat.card ↥(A ⊓ B) ∣
      Nat.card ↥((Subgroup.center ↥X).map X.subtype) :=
    Subgroup.card_dvd_of_le h
  rw [Subgroup.card_map_of_injective X.subtype_injective] at hdvd
  have h3 : Nat.card ↥(A ⊓ B) ∣ 3 := by
    have hg : Nat.gcd 9 48 = 3 := by norm_num
    rw [← hg]
    exact Nat.dvd_gcd h9 (hdvd.trans h48)
  exact Nat.le_of_dvd (by norm_num) h3

private theorem eightyOne_le_card_sup_of_three {G : Type} [Group G] [Finite G]
    {E₁ E₂ E₃ : Subgroup G}
    (h₁ : Nat.card ↥E₁ = 9) (h₂ : Nat.card ↥E₂ = 9) (h₃ : Nat.card ↥E₃ = 9)
    (hc₁₂ : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (hc₁₃ : ∀ a ∈ E₁, ∀ b ∈ E₃, a * b = b * a)
    (hc₂₃ : ∀ a ∈ E₂, ∀ b ∈ E₃, a * b = b * a)
    (hin₁₂ : Nat.card ↥(E₁ ⊓ E₂) ≤ 3)
    (hin₁₂₃ : Nat.card ↥((E₁ ⊔ E₂) ⊓ E₃) ≤ 3) :
    81 ≤ Nat.card ↥(E₁ ⊔ E₂ ⊔ E₃) := by
  have hcard₁₂ := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc₁₂).1
  rw [h₁, h₂] at hcard₁₂
  have hbig₁₂ : 27 ≤ Nat.card ↥(E₁ ⊔ E₂) := by
    have hle := Nat.mul_le_mul_left (Nat.card ↥(E₁ ⊔ E₂)) hin₁₂
    nlinarith [hcard₁₂]
  have hcent : E₁ ⊔ E₂ ≤ Subgroup.centralizer (E₃ : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => (hc₁₃ a ha b hb).symm))
      (fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => (hc₂₃ a ha b hb).symm))
  have hc₁₂₃ : ∀ a ∈ E₁ ⊔ E₂, ∀ b ∈ E₃, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hcent ha) b hb).symm
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (E₁ ⊔ E₂) E₃ hc₁₂₃).1
  rw [h₃] at hcard
  have : 81 ≤ Nat.card ↥((E₁ ⊔ E₂) ⊔ E₃) := by
    nlinarith [hcard, hbig₁₂, hin₁₂₃]
  exact this

private theorem exists_isElemAbelian_card_nine_of_two_le_pRank {G : Type} [Group G] [Finite G]
    {X Q : Subgroup G} (hQXsyl : IsSylowOf 3 (Q ⊓ X) X) (h2 : 2 ≤ CFSG.Open.pRank 3 X) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 9 := by
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 (Q ⊓ X) :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hQXsyl.le hQXsyl le_rfl
  obtain ⟨z, hzP, hzord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three
      (H := Q ⊓ X) (by omega)
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨E, -, hEP, hEab, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      (B := Q ⊓ X) (X := Subgroup.zpowers z) hQXsyl.isPGroup (h2.trans hle)
      (Subgroup.zpowers_le.mpr hzP) hzcard
  exact ⟨E, hEP.trans inf_le_right, hEab, by rw [hEcard]; norm_num⟩

theorem r875QNorm_of_inputs {G : Type} [Group G] [Finite G] (D : Data G)
    (hgr : CFSG.Open.GriessAllModelsStatement) (hSg : UC6S846.SigmaStd D) (h870 : R870 D)
    (h873 : R873 D) (h875c : R875Comp D) : R875QNorm D := by
  classical
  intro L X H hmin Q hQsyl hQXsyl
  by_contra hN
  obtain ⟨q, hqQ, hqN⟩ := Set.not_subset.mp hN
  have hcomp : IsComponentOf X (H ⊓ D.M) := h875c L X H hmin
  have h873X : IsSL3 ↥X 2 ∨ IsSU3 ↥X 3 := (h873 L X H hmin).1
  have hXm3 : 2 ≤ CFSG.Open.pRank 3 X := r873M3_of_r873 h873 L X H hmin
  have hqHM : q ∈ H ⊓ D.M := hQsyl.le hqQ
  have hq2HM : q ^ 2 ∈ H ⊓ D.M := pow_mem hqHM 2
  let X₂ : Subgroup G := X.map (MulAut.conj q).toMonoidHom
  let X₃ : Subgroup G := X.map (MulAut.conj (q ^ 2)).toMonoidHom
  have hcomp₂ : IsComponentOf X₂ (H ⊓ D.M) := by
    simpa only [X₂] using CFSG.CGT.Foote82.BranchAAux.isComponentOf_conj hcomp hqHM
  have hcomp₃ : IsComponentOf X₃ (H ⊓ D.M) := by
    simpa only [X₃] using CFSG.CGT.Foote82.BranchAAux.isComponentOf_conj hcomp hq2HM
  have h₂ne : X₂ ≠ X := fun h =>
    hqN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hodd : Odd (orderOf q) := by
    have hpQ : IsPGroup 3 ↥(Subgroup.zpowers q) :=
      IsPGroup.to_le hQsyl.isPGroup (Subgroup.zpowers_le.mpr hqQ)
    obtain ⟨k, hk⟩ := hpQ.exists_card_eq
    rw [← Nat.card_zpowers, hk]
    exact Odd.pow (by norm_num : Odd 3)
  have hq_mem_zp : q ∈ Subgroup.zpowers (q ^ 2) := by
    obtain ⟨m, hm⟩ := hodd
    refine Subgroup.mem_zpowers_iff.mpr ⟨((m + 1 : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, ← pow_mul]
    have h2 : 2 * (m + 1) = orderOf q + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have h₃ne : X₃ ≠ X := by
    intro h
    have h' : X.map (MulAut.conj (q ^ 2)).toMonoidHom = X := h
    have hq2N : q ^ 2 ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h'
    exact hqN ((Subgroup.zpowers_le.mpr hq2N) hq_mem_zp)
  have hcomp_inv : (MulAut.conj q⁻¹).toMonoidHom.comp (MulAut.conj q).toMonoidHom =
      MonoidHom.id G := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.id_apply]
    change ((MulAut.conj q⁻¹) * (MulAut.conj q)) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hcomp_qq : (MulAut.conj q⁻¹).toMonoidHom.comp (MulAut.conj (q ^ 2)).toMonoidHom =
      (MulAut.conj q).toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply]
    change ((MulAut.conj q⁻¹) * (MulAut.conj (q ^ 2))) x = (MulAut.conj q) x
    rw [← map_mul, show q⁻¹ * q ^ 2 = q by group]
  have hX₂inv : X₂.map (MulAut.conj q⁻¹).toMonoidHom = X := by
    simp only [X₂, Subgroup.map_map, hcomp_inv, Subgroup.map_id]
  have hX₃X₂ : X₃.map (MulAut.conj q⁻¹).toMonoidHom = X₂ := by
    simp only [X₃, X₂, Subgroup.map_map, hcomp_qq]
  have h₃₂ : X₃ ≠ X₂ := by
    intro heq
    have h := congrArg (Subgroup.map (MulAut.conj q⁻¹).toMonoidHom) heq
    rw [hX₃X₂, hX₂inv] at h
    exact h₂ne h
  have hcomm₁₂ : X ≤ Subgroup.centralizer (X₂ : Set G) := by
    rcases CFSG.CGT.Foote82.BranchAAux.eq_or_commute_of_isComponentOf hcomp hcomp₂ with heq | hc
    · exact absurd heq.symm h₂ne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hcomm₁₃ : X ≤ Subgroup.centralizer (X₃ : Set G) := by
    rcases CFSG.CGT.Foote82.BranchAAux.eq_or_commute_of_isComponentOf hcomp hcomp₃ with heq | hc
    · exact absurd heq.symm h₃ne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hcomm₂₃ : X₂ ≤ Subgroup.centralizer (X₃ : Set G) := by
    rcases CFSG.CGT.Foote82.BranchAAux.eq_or_commute_of_isComponentOf hcomp₂ hcomp₃ with heq | hc
    · exact absurd heq.symm h₃₂
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  obtain ⟨E₁, hE₁X, hE₁ab, hE₁card⟩ :=
    exists_isElemAbelian_card_nine_of_two_le_pRank hQXsyl hXm3
  let E₂ : Subgroup G := E₁.map (MulAut.conj q).toMonoidHom
  let E₃ : Subgroup G := E₁.map (MulAut.conj (q ^ 2)).toMonoidHom
  have hE₂X₂ : E₂ ≤ X₂ := by
    simpa only [E₂, X₂] using Subgroup.map_mono (f := (MulAut.conj q).toMonoidHom) hE₁X
  have hE₃X₃ : E₃ ≤ X₃ := by
    simpa only [E₃, X₃] using
      Subgroup.map_mono (f := (MulAut.conj (q ^ 2)).toMonoidHom) hE₁X
  have hE₂ab : IsElemAbelian 3 E₂ := by
    simpa only [E₂] using
      CFSG.SectionRank.isElemAbelian_map hE₁ab (MulAut.conj q).toMonoidHom
  have hE₃ab : IsElemAbelian 3 E₃ := by
    simpa only [E₃] using
      CFSG.SectionRank.isElemAbelian_map hE₁ab (MulAut.conj (q ^ 2)).toMonoidHom
  have hE₂card : Nat.card ↥E₂ = 9 := by
    simp only [E₂, Subgroup.card_map_of_injective (f := (MulAut.conj q).toMonoidHom)
      (MulAut.conj q).injective, hE₁card]
  have hE₃card : Nat.card ↥E₃ = 9 := by
    simp only [E₃, Subgroup.card_map_of_injective (f := (MulAut.conj (q ^ 2)).toMonoidHom)
      (MulAut.conj (q ^ 2)).injective, hE₁card]
  have hE₁C₂ : E₁ ≤ Subgroup.centralizer (X₂ : Set G) := hE₁X.trans hcomm₁₂
  have hE₁C₃ : E₁ ≤ Subgroup.centralizer (X₃ : Set G) := hE₁X.trans hcomm₁₃
  have hE₂C₃ : E₂ ≤ Subgroup.centralizer (X₃ : Set G) := hE₂X₂.trans hcomm₂₃
  have hcentE₁₂ : E₁ ⊔ E₂ ≤ Subgroup.centralizer (X₃ : Set G) := sup_le hE₁C₃ hE₂C₃
  have hcenter₂ : Nat.card (Subgroup.center ↥X₂) ∣ 48 := by
    have htype : IsSL3 ↥X₂ 2 ∨ IsSU3 ↥X₂ 3 := by
      simpa only [X₂] using isSL3_or_isSU3_of_mulEquiv
        (Subgroup.equivMapOfInjective X (MulAut.conj q).toMonoidHom
          (MulAut.conj q).injective) h873X
    exact card_center_dvd_of_isSL3_or_isSU3 hgr htype
  have hcenter₃ : Nat.card (Subgroup.center ↥X₃) ∣ 48 := by
    have htype : IsSL3 ↥X₃ 2 ∨ IsSU3 ↥X₃ 3 := by
      simpa only [X₃] using isSL3_or_isSU3_of_mulEquiv
        (Subgroup.equivMapOfInjective X (MulAut.conj (q ^ 2)).toMonoidHom
          (MulAut.conj (q ^ 2)).injective) h873X
    exact card_center_dvd_of_isSL3_or_isSU3 hgr htype
  have hin₁₂ : Nat.card ↥(E₁ ⊓ E₂) ≤ 3 := by
    refine card_inf_le_three_of_le_center ?_ ?_ hcenter₂
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hE₂X₂ hx.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hE₁C₂ hx.1) (g : G) g.2)
    · exact (Subgroup.card_dvd_of_le inf_le_left).trans (by rw [hE₁card])
  have hin₁₂₃ : Nat.card ↥((E₁ ⊔ E₂) ⊓ E₃) ≤ 3 := by
    refine card_inf_le_three_of_le_center ?_ ?_ hcenter₃
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hE₃X₃ hx.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentE₁₂ hx.1) (g : G) g.2)
    · exact (Subgroup.card_dvd_of_le inf_le_right).trans (by rw [hE₃card])
  have hE₁₂ab : IsElemAbelian 3 (E₁ ⊔ E₂) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE₁ab hE₂ab fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hE₁C₂ ha) b (hE₂X₂ hb)).symm
  have hEab : IsElemAbelian 3 (E₁ ⊔ E₂ ⊔ E₃) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE₁₂ab hE₃ab fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hcentE₁₂ ha) b (hE₃X₃ hb)).symm
  have hE81 : 81 ≤ Nat.card ↥(E₁ ⊔ E₂ ⊔ E₃) :=
    eightyOne_le_card_sup_of_three hE₁card hE₂card hE₃card
      (fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.mp (hE₁C₂ ha) b (hE₂X₂ hb)).symm)
      (fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.mp (hE₁C₃ ha) b (hE₃X₃ hb)).symm)
      (fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.mp (hE₂C₃ ha) b (hE₃X₃ hb)).symm)
      hin₁₂ hin₁₂₃
  have hEM : E₁ ⊔ E₂ ⊔ E₃ ≤ D.M :=
    sup_le (sup_le (hE₁X.trans (hcomp.1.trans inf_le_right))
      (hE₂X₂.trans (hcomp₂.1.trans inf_le_right)))
      (hE₃X₃.trans (hcomp₃.1.trans inf_le_right))
  obtain ⟨k, hk⟩ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 3 _ hEab).exists_card_eq
  have h4k : 4 ≤ k := by
    have hpow : 3 ^ 4 ≤ 3 ^ k := by rw [← hk]; exact hE81
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M :=
    h4k.trans (CFSG.SectionRank.le_pRank (by norm_num) hEM hEab hk)
  have hle3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    pRank_le_three_of_minCex hSg h870 hmin Nat.prime_three (by norm_num) (by omega)
  omega

private theorem r875le_three_dvd_card_of_two_le_pRank {G : Type} [Group G] [Finite G]
    {X : Subgroup G} (h : 2 ≤ CFSG.Open.pRank 3 X) : 3 ∣ Nat.card X := by
  obtain ⟨E, hEX, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) X
  have h3E : 3 ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_trans (by norm_num : 3 ∣ 3 ^ 2) (Nat.pow_dvd_pow 3 h)
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv] at h3E
  exact h3E.trans (Subgroup.card_subgroup_dvd_card (E.subgroupOf X))

private theorem r875le_noncentral_three {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple K) (h3 : 3 ∣ Nat.card K) :
    ∃ y ∈ K, IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ K, y * l ≠ l * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKperf : commutator ↥K = ⊤ := hKq.1
  let P : Sylow 3 ↥K := Classical.choice Sylow.nonempty
  have hnot := CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect hKperf h3 P
  obtain ⟨y, hyP, hyZ⟩ := Set.not_subset.mp hnot
  have hyq : IsPGroup 3 (Subgroup.zpowers y) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyP)
  have hyZ' : ∃ l : ↥K, y * l ≠ l * y := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hyZ (Subgroup.mem_center_iff.mpr fun g => (h g).symm)
  obtain ⟨l, hl⟩ := hyZ'
  refine ⟨(y : G), y.2, ?_, (l : G), l.2, ?_⟩
  · have hm := hyq.map K.subtype
    rwa [MonoidHom.map_zpowers K.subtype y] at hm
  · exact fun h => hl (Subtype.ext h)

private theorem r875le_component_count {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH3 : CFSG.Open.pRank 3 H ≤ 3) :
    Nat.card {A : Subgroup G // CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A} ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomp : ∀ i : {A : Subgroup G // CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A},
      CFSG.Open.IsComponentOf (i.1.subgroupOf H) ⊤ := by
    intro i
    exact (CFSG.ComponentClassification.OrdinaryComponentTransport.subgroupOf_iff i.1 H
        i.2.1.1).mpr
      ⟨(CFSG.Open.IsSubnormal.iff_subgroupOf i.2.1.1).1 i.2.1.2.1, i.2.1.2.2⟩
  have hinj : Function.Injective
      (fun i : {A : Subgroup G // CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A} =>
        i.1.subgroupOf H) := by
    intro i j hij
    apply Subtype.ext
    have h := congrArg (Subgroup.map H.subtype) hij
    rwa [Subgroup.map_subgroupOf_eq_of_le i.2.1.1,
      Subgroup.map_subgroupOf_eq_of_le j.2.1.1] at h
  have hdvd : ∀ i : {A : Subgroup G // CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A},
      3 ∣ Nat.card (i.1.subgroupOf H) := by
    intro i
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe i.2.1.1).toEquiv]
    exact i.2.2
  have h := CFSG.AGLEmbedding.le_pRank_of_components (X := ↥H) (q := 3) Nat.prime_three
    (fun i : {A : Subgroup G // CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A} =>
      i.1.subgroupOf H)
    hcomp hinj (⊤ : Subgroup ↥H)
    (fun i => Classical.choose
      (r875le_noncentral_three (G := ↥H) (K := i.1.subgroupOf H) (hcomp i).2.2 (hdvd i)))
    (fun i => Subgroup.mem_top _)
    (fun i => (Classical.choose_spec
      (r875le_noncentral_three (G := ↥H) (K := i.1.subgroupOf H) (hcomp i).2.2 (hdvd i))).1)
    (fun i => (Classical.choose_spec
      (r875le_noncentral_three (G := ↥H) (K := i.1.subgroupOf H) (hcomp i).2.2 (hdvd i))).2.1)
    (fun i => (Classical.choose_spec
      (r875le_noncentral_three (G := ↥H) (K := i.1.subgroupOf H) (hcomp i).2.2 (hdvd i))).2.2)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H] at h
  exact h.trans hH3

private theorem r875le_x_le_normalizer_K {G : Type} [Group G] [Finite G]
    {X H K : Subgroup G} (hXH : X ≤ H) (hXperf : commutator X = ⊤)
    (hH3 : CFSG.Open.pRank 3 H ≤ 3) (hK : IsComponentOf K H) (h3 : 3 ∣ Nat.card K) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Group.IsPerfect X := ⟨hXperf⟩
  have hcard : (Set.ncard {A : Subgroup G | CFSG.Open.IsComponentOf A H ∧
      3 ∣ Nat.card A}) ≤ 4 := by
    have h := r875le_component_count (G := G) (H := H) hH3
    have h' : (Set.ncard {A : Subgroup G | CFSG.Open.IsComponentOf A H ∧
        3 ∣ Nat.card A}) ≤ 3 := by
      rw [← Nat.card_coe_set_eq]
      exact h
    omega
  have hstable : ∀ g ∈ X, ∀ A ∈ {A : Subgroup G | CFSG.Open.IsComponentOf A H ∧
      3 ∣ Nat.card A},
      A.map (MulAut.conj g).toMonoidHom ∈ {A : Subgroup G |
        CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A} := by
    intro g hg A hA
    obtain ⟨hAc, h3A⟩ := hA
    refine ⟨CFSG.CGT.Foote82.BranchAAux.isComponentOf_conj hAc (hXH hg), ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3A
  have hKmem : K ∈ {A : Subgroup G | CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A} :=
    ⟨hK, h3⟩
  exact CFSG.ClassicalInvolution.RouteD.Gaps.perfect_le_normalizer_of_card_le_four X
    {A : Subgroup G | CFSG.Open.IsComponentOf A H ∧ 3 ∣ Nat.card A}
    (Set.toFinite _) hcard hstable hKmem

private theorem r875le_dichotomy {G : Type} [Group G] [Finite G]
    {X S K : Subgroup G} (hXq : CFSG.Open.IsQuasisimple X)
    (hJX : ⁅X, S⁆ ≤ X) (hJK : ⁅X, S⁆ ≤ K) :
    X ≤ K ∨ ⁅X, S⁆ = ⊥ := by
  have hXq' : CFSG.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).1 hXq
  have hJnorm : (⁅X, S⁆.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).mpr
      (Subgroup.normalizer_commutator_ge_left (H₁ := X) (H₂ := S))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq' hJnorm with htop | hcenter
  · left
    have hJeq : ⁅X, S⁆ = X := by
      have h := congrArg (Subgroup.map X.subtype) htop
      rwa [Subgroup.map_subgroupOf_eq_of_le hJX, Subgroup.map_top, Subgroup.range_subtype] at h
    rwa [hJeq] at hJK
  · right
    have hJcent : ⁅X, S⁆ ≤ Subgroup.centralizer (X : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hj' : (⟨j, hJX hj⟩ : ↥X) ∈ Subgroup.center ↥X :=
        hcenter (Subgroup.mem_subgroupOf.mpr hj)
      have hcomm := Subgroup.mem_center_iff.mp hj' ⟨x, hx⟩
      exact congrArg Subtype.val hcomm
    have hdouble : ⁅⁅X, S⁆, X⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJcent
    exact CFSG.LocalCores.perfect_double_commutator ⟨hXq.1⟩ hdouble

private theorem r875le_step6 {G : Type} [Group G] [Finite G]
    {D : Data G} {L X H K S : Subgroup G}
    (hKSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch)
    (hmin : MinCex869 D L X H)
    (hXq : CFSG.Open.IsQuasisimple X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hK : IsComponentOf K H)
    (hSyl : IsSylowOf 3 S K) (hSX : ⁅X, S⁆ = ⊥) (h3X : 3 ∣ Nat.card X)
    (hc : ¬ X ≤ Subgroup.centralizer (K : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect X := ⟨hXq.1⟩
  have hHtop : H ≠ ⊤ := hmin.mem.1.ne_top
  have hHKG : CFSG.Open.IsKGroup ↥H := D.standing.kProper.isKGroup H hHtop
  have hSS := hKSch.schreierSections hHKG
  have hKsub : CFSG.IsComponent (K.subgroupOf H) :=
    CFSG.CGT.Foote82.BranchAAux.isComponent_subgroupOf hK
  have hOutSolQ : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ((K.subgroupOf H) ⧸ Subgroup.center (K.subgroupOf H))) :=
    CFSG.ComponentClassification.LBalance.SchreierSections.outer_component
      hSS (K.subgroupOf H) hKsub
  have : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have : Group.IsPerfect ↥(K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hK.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK.1).symm.surjective
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥(K.subgroupOf H) ⧸ Subgroup.center ↥(K.subgroupOf H))) := hOutSolQ
  have hOutSolQ' : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(K.subgroupOf H)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient
      ↥(K.subgroupOf H)
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(K.subgroupOf H)) := hOutSolQ'
  have hOutK : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (Subgroup.subgroupOfEquivOfLe hK.1)
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := hOutK
  have hOut : ∀ P : Subgroup (MulAut ↥K), Group.IsPerfect P →
      P ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    intro P hP
    have : Group.IsPerfect P := hP
    intro p hp
    obtain ⟨element, heq⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
        (A := P) (G := ↥K) P.subtype ⟨p, hp⟩
    exact ⟨element, by simpa using heq.symm⟩
  have hXKC : X ≤ K ⊔ Subgroup.centralizer (K : Set G) :=
    CFSG.GroupTheory.le_sup_centralizer_of_perfect_of_perfect_aut_inner
      (K := X) (C := K) hXK hOut
  let action : X →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)
  have hact : ∀ (x : ↥X) (k : ↥K),
      ((action x) k : G) = (x : G) * (k : G) * (x : G)⁻¹ := by
    intro x k
    change ((K.normalizerMonoidHom ⟨(x : G), hXK x.2⟩) k : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hkconj : ∀ (s : ↥K) (k : ↥K),
      (((MulAut.conj s) k : ↥K) : G) = (s : G) * (k : G) * (s : G)⁻¹ := by
    intro s k
    simp
  have hactker : action.ker = (Subgroup.centralizer (K : Set G)).subgroupOf X := by
    change (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker = _
    rw [← MonoidHom.comap_ker, K.normalizerMonoidHom_ker]
    exact Subgroup.comap_inclusion_subgroupOf hXK (Subgroup.centralizer (K : Set G))
  have hAperf : Group.IsPerfect ↥action.range := Group.IsPerfect.range action
  obtain ⟨S₀, hS₀⟩ := hSyl.exists_sylow_eq_subgroupOf
  let I : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  have hAinn : action.range ≤ I := hOut action.range hAperf
  let SbarSyl : Sylow 3 I := S₀.mapSurjective (MulAut.conj.rangeRestrict_surjective)
  have hSbar : (SbarSyl : Subgroup I).map I.subtype =
      (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) := by
    change ((S₀.mapSurjective (MulAut.conj.rangeRestrict_surjective) : Sylow 3 I) :
      Subgroup I).map I.subtype = _
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, hS₀]
    rfl
  let T : Sylow 3 ↥X := Classical.choice Sylow.nonempty
  let hTbarSyl : Sylow 3 ↥action.range := T.mapSurjective action.rangeRestrict_surjective
  let Tbar : Subgroup (MulAut ↥K) := (T : Subgroup ↥X).map action
  have hTbar : (hTbarSyl : Subgroup ↥action.range).map action.range.subtype = Tbar := by
    change ((T.mapSurjective action.rangeRestrict_surjective : Sylow 3 ↥action.range) :
      Subgroup ↥action.range).map action.range.subtype = _
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    rfl
  have hTbar3 : IsPGroup 3 Tbar := by
    rw [← hTbar]
    exact hTbarSyl.isPGroup'.map action.range.subtype
  have hcomm : Tbar ≤ Subgroup.centralizer
      ((S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have hxs : (x : G) * (s : G) = (s : G) * (x : G) := by
      have h1 : X ≤ Subgroup.centralizer (S : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSX
      exact (Subgroup.mem_centralizer_iff.mp (h1 x.2) (s : G)
        (Subgroup.mem_subgroupOf.mp hs)).symm
    ext k
    simp only [MulAut.mul_apply]
    rw [hkconj s ((action x) k), hact x k, hact x ((MulAut.conj s) k), hkconj s k]
    have h2 : (s : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * (s : G)⁻¹ := by
      have h := congrArg (fun z : G => z⁻¹) hxs
      simpa only [mul_inv_rev] using h
    calc (s : G) * ((x : G) * (k : G) * (x : G)⁻¹) * (s : G)⁻¹
        = ((s : G) * (x : G)) * (k : G) * ((x : G)⁻¹ * (s : G)⁻¹) := by group
      _ = ((x : G) * (s : G)) * (k : G) * ((s : G)⁻¹ * (x : G)⁻¹) := by rw [← hxs, ← h2]
      _ = (x : G) * ((s : G) * (k : G) * (s : G)⁻¹) * (x : G)⁻¹ := by group
  have hTbarI : Tbar ≤ I := by
    rw [← hTbar]
    exact (Subgroup.map_subtype_le _).trans hAinn
  have hSbar3 : IsPGroup 3 ((S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) := by
    rw [← hSbar]
    exact SbarSyl.isPGroup'.map I.subtype
  have hsup3 : IsPGroup 3 ↥(Tbar ⊔ (S.subgroupOf K).map
      (MulAut.conj : ↥K →* MulAut ↥K)) :=
    IsPGroup.to_sup_of_normal_right' hTbar3 hSbar3
      (hcomm.trans (Subgroup.centralizer_le_normalizer _))
  have hTbar_le : Tbar ≤ (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) := by
    have hQ : ((Tbar ⊔ (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)).subgroupOf I) =
        (SbarSyl : Subgroup I) := by
      refine SbarSyl.is_maximal' ?_ ?_
      · exact hsup3.comap_subtype
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        have hy' : (y : MulAut ↥K) ∈ (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) := by
          rw [← hSbar]
          exact Subgroup.mem_map_of_mem I.subtype hy
        exact (le_sup_right : (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) ≤
          Tbar ⊔ (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) hy'
    have hmap := congrArg (Subgroup.map I.subtype) hQ
    rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hTbarI (by rw [← hSbar]; exact Subgroup.map_subtype_le _)),
      hSbar] at hmap
    exact le_sup_left.trans (le_of_eq hmap)
  have hSbar_cent : (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) ≤
      Subgroup.centralizer (action.range : Set (MulAut ↥K)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := MonoidHom.mem_range.mp hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have hxs : (x : G) * (s : G) = (s : G) * (x : G) := by
      have h1 : X ≤ Subgroup.centralizer (S : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSX
      exact (Subgroup.mem_centralizer_iff.mp (h1 x.2) (s : G)
        (Subgroup.mem_subgroupOf.mp hs)).symm
    ext k
    simp only [MulAut.mul_apply]
    rw [hact x ((MulAut.conj s) k), hkconj s k, hkconj s ((action x) k), hact x k]
    have h2 : (s : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * (s : G)⁻¹ := by
      have h := congrArg (fun z : G => z⁻¹) hxs
      simpa only [mul_inv_rev] using h
    calc (x : G) * ((s : G) * (k : G) * (s : G)⁻¹) * (x : G)⁻¹
        = ((x : G) * (s : G)) * (k : G) * ((s : G)⁻¹ * (x : G)⁻¹) := by group
      _ = ((s : G) * (x : G)) * (k : G) * ((x : G)⁻¹ * (s : G)⁻¹) := by rw [hxs, h2]
      _ = (s : G) * ((x : G) * (k : G) * (x : G)⁻¹) * (s : G)⁻¹ := by group
  have hTbar_center : (hTbarSyl : Subgroup ↥action.range) ≤
      Subgroup.center ↥action.range := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hy' : (y : MulAut ↥K) ∈ Tbar := by
      rw [← hTbar]
      exact ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hSbar_cent (hTbar_le hy')) z z.2)
  have hTbar_bot : Tbar = ⊥ := by
    by_contra hne
    have h3A : 3 ∣ Nat.card ↥action.range := by
      have hne' : (hTbarSyl : Subgroup ↥action.range) ≠ ⊥ := by
        intro h
        apply hne
        rw [← hTbar, h, Subgroup.map_bot]
      have hcard : Nat.card ↥(hTbarSyl : Subgroup ↥action.range) ≠ 1 := by
        have h1 : 1 < Nat.card ↥(hTbarSyl : Subgroup ↥action.range) :=
          (Subgroup.one_lt_card_iff_ne_bot _).mpr hne'
        omega
      rcases (hTbarSyl.isPGroup'.card_eq_or_dvd) with h1 | hd
      · exact absurd h1 hcard
      · exact hd.trans (Subgroup.card_subgroup_dvd_card _)
    exact (CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect
      hAperf.commutator_eq_top h3A hTbarSyl) hTbar_center
  have hTle : (T : Subgroup ↥X) ≤ (Subgroup.centralizer (K : Set G)).subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxker : x ∈ action.ker := by
      rw [MonoidHom.mem_ker]
      have hmemT : action x ∈ Tbar := Subgroup.mem_map_of_mem action hx
      rw [hTbar_bot, Subgroup.mem_bot] at hmemT
      exact hmemT
    rwa [hactker, Subgroup.mem_subgroupOf] at hxker
  have hXq' : CFSG.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).1 hXq
  have hNnorm : ((Subgroup.centralizer (K : Set G)).subgroupOf X).Normal := by
    rw [← hactker]
    infer_instance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq' hNnorm with htop | hcenter
  · exact hc (Subgroup.subgroupOf_eq_top.mp htop)
  · have hTc : (T : Subgroup ↥X) ≤ Subgroup.center ↥X := hTle.trans hcenter
    have hTne : (T : Subgroup ↥X) ≠ ⊥ := Sylow.ne_bot_of_dvd_card T h3X
    exact (CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect
      hXq.1 h3X T) hTc

theorem r875Le_of_inputs {G : Type} [Group G] [Finite G] (D : Data G)
    (hKSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch) (hSg : UC6S846.SigmaStd D) (h870 : R870 D)
    (h873 : R873 D) (h874 : R874 D) (h875c : R875Comp D) (hQN : R875QNorm D) : R875Le D := by
  intro L X H hmin K hK h3 hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXcomp : IsComponentOf X (H ⊓ D.M) := h875c L X H hmin
  have hXH : X ≤ H := hXcomp.1.trans inf_le_left
  have hXperf : commutator X = ⊤ := hXcomp.2.2.1
  obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 X
  have hP₀HM : P₀ ≤ H ⊓ D.M := hP₀.le.trans hXcomp.1
  obtain ⟨Q₀, hP₀Q₀⟩ := (hP₀.isPGroup.comap_subtype (K := H ⊓ D.M)).exists_le_sylow
  let Q : Subgroup G := (Q₀ : Subgroup ↥(H ⊓ D.M)).map (H ⊓ D.M).subtype
  have hQsyl : IsSylowOf 3 Q (H ⊓ D.M) := ⟨Q₀, rfl⟩
  have hP₀Q : P₀ ≤ Q := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hP₀HM]
    exact Subgroup.map_mono hP₀Q₀
  have hQXsyl : IsSylowOf 3 (Q ⊓ X) X := by
    have hQX : Q ⊓ X = P₀ :=
      IsSylowOf.eq_of_le hP₀ (le_inf hP₀Q hP₀.le) inf_le_right hQsyl.isPGroup.to_inf_left
    rwa [hQX]
  have hQN' : Q ≤ Subgroup.normalizer (X : Set G) := hQN L X H hmin Q hQsyl hQXsyl
  have hQH : IsSylowOf 3 Q H := (h874 L X H hmin Q hQsyl hQXsyl).1
  have hQM : Q ≤ D.M := hQsyl.le.trans inf_le_right
  have hH3 : CFSG.Open.pRank 3 H ≤ 3 := by
    have h873M3 : 2 ≤ CFSG.Open.pRank 3 X := r873M3_of_r873 h873 L X H hmin
    have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
      pRank_le_three_of_minCex hSg h870 hmin Nat.prime_three (by norm_num) (by omega)
    have hle : CFSG.Open.pRank 3 H ≤ CFSG.Open.pRank 3 D.M :=
      CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hQH.le hQH hQM
    omega
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    r875le_x_le_normalizer_K hXH hXperf hH3 hK h3
  have hQK : IsSylowOf 3 (Q ⊓ K) K :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal hQH hK.2.1
  have hJX : ⁅X, Q ⊓ K⁆ ≤ X :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp (inf_le_left.trans hQN')
  have hJK : ⁅X, Q ⊓ K⁆ ≤ K :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp hXK)
  rcases r875le_dichotomy hXcomp.2.2 hJX hJK with hXK' | hJbot
  · exact hXK'
  · exfalso
    exact r875le_step6 hKSch hmin hXcomp.2.2 hXK hK hQK hJbot
      (r875le_three_dvd_card_of_two_le_pRank (r873M3_of_r873 h873 L X H hmin)) hc

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
