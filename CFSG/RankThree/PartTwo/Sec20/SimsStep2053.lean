module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofPush
public import CFSG.RankThree.PartTwo.Sec20.SimsSL2Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.Models.PGLSimple
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Late.Item2010
public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf)

namespace SimsStep2053

private theorem false_of_normal_sylow_psl2 {L : Type*} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (e : L ≃* projSL 2 (GaloisField 2 n)) {U : Subgroup L} (hUn : U.Normal)
    (hU2 : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsimple : IsSimpleGroup (projSL 2 (GaloisField 2 n)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have : IsSimpleGroup L := e.isSimpleGroup
  have hcard : Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr (e.trans (Sec21.projSLTwoEquivSL (GaloisField 2 n))).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 n (by omega)]
  haveI := hUn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
  · rw [h, Subgroup.index_bot] at hUi
    apply hUi
    rw [hcard]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · rw [h] at hU2
    have hL2 : IsPGroup 2 L := hU2.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := hL2.exists_card_eq
    have h3' : 3 ∣ 2 ^ k := hk ▸ Sec21.three_dvd_card_of_mulEquiv_projSL e
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)

section Sylow

variable {H : Type*} [Group H] [Finite H] {Lb Sb Nb : Subgroup H} {n : ℕ}

private theorem isSylowOf_inf_normal (hL : Lb.Normal) (hS : IsSylowOf 2 Sb ⊤) :
    IsSylowOf 2 (Sb ⊓ Lb) Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hL).ge

private theorem normalizer_ne_top (hn : 2 ≤ n) (hL : Lb.Normal)
    (e : Lb ≃* projSL 2 (GaloisField 2 n)) (hS : IsSylowOf 2 Sb ⊤) :
    Subgroup.normalizer ((Sb ⊓ Lb : Subgroup H) : Set H) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  have hUn : (Sb ⊓ Lb).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hSL := isSylowOf_inf_normal hL hS
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSL
  exact false_of_normal_sylow_psl2 hn e (hUn.subgroupOf Lb) hSL.2.1.comap_subtype hSL.2.2

private theorem eq_top_or_le_normalizer (hn : 0 < n) (hL : Lb.Normal)
    (e : Lb ≃* projSL 2 (GaloisField 2 n)) (hS : IsSylowOf 2 Sb ⊤) (hLS : Lb ⊔ Sb = ⊤)
    (hSN : Sb ≤ Nb) :
    Nb = ⊤ ∨ Nb ≤ Subgroup.normalizer ((Sb ⊓ Lb : Subgroup H) : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (isSylowOf_inf_normal hL hS).exists_sylow_eq_subgroupOf
  have hUR : (Q : Subgroup Lb) ≤ (Nb ⊓ Lb).subgroupOf Lb := by
    rw [hQ]
    exact Subgroup.comap_mono (inf_le_inf_right Lb hSN)
  rcases SimsSL2.le_normalizer_or_eq_top_of_sylow_psl2 hn e Q _ hUR with hR | hR
  · right
    intro x hx
    have hx' : x ∈ ((Lb ⊔ Sb : Subgroup H) : Set H) := by rw [hLS]; exact Subgroup.mem_top x
    rw [Subgroup.normal_mul] at hx'
    obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    have hlN : l ∈ Nb := by
      have := Nb.mul_mem hx (Nb.inv_mem (hSN hs))
      rwa [mul_inv_cancel_right] at this
    have hlmem : (⟨l, hl⟩ : Lb) ∈ Subgroup.normalizer ((Q : Subgroup Lb) : Set Lb) :=
      hR (Subgroup.mem_subgroupOf.mpr ⟨hlN, hl⟩)
    have hl' : l ∈ Subgroup.normalizer ((Sb ⊓ Lb : Subgroup H) : Set H) := by
      rw [Subgroup.mem_normalizer_iff] at hlmem ⊢
      intro u
      constructor
      · intro hu
        have := (hlmem ⟨u, hu.2⟩).mp (by rw [hQ]; exact hu)
        rw [hQ] at this
        exact this
      · intro hu
        have huL : u ∈ Lb := by
          have := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hu.2) hl
          rwa [show l⁻¹ * (l * u * l⁻¹) * l = u by group] at this
        have := (hlmem ⟨u, huL⟩).mpr (by rw [hQ]; exact hu)
        rw [hQ] at this
        exact this
    have hs' : s ∈ Subgroup.normalizer ((Sb ⊓ Lb : Subgroup H) : Set H) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
        by rw [Subgroup.normalizer_eq_top_iff.mpr hL]; exact Subgroup.mem_top _⟩
    exact Subgroup.mul_mem _ hl' hs'
  · left
    rw [Subgroup.subgroupOf_eq_top] at hR
    rw [eq_top_iff, ← hLS]
    exact sup_le (hR.trans inf_le_left) hSN

end Sylow

section CGS

variable {G : Type} [Group G] [Finite G]

private theorem cgsIn_sup_ne {K T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTX : IsSylowOf 2 T (K ⊔ T))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 2 (GaloisField 2 n))
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ K ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) :
    CFSG.Quasithin.cgsIn (K ⊔ T) T ≠ K ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := K ⊔ T
  have hKX : K ≤ X := le_sup_left
  have hTXle : T ≤ X := le_sup_right
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hQT : CFSG.Open.pCoreOf 2 X ≤ T := pCoreOf_le_of_isSylowOf hTX
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set J := K.subgroupOf X with hJ
  have hJn : J.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  set Lb := J.map π with hLb
  have hLn : Lb.Normal := hJn.map π hπs
  set Sb := (T.subgroupOf X).map π with hSb
  set φ : ↥K →* ↥X ⧸ CFSG.pCore 2 ↥X := π.comp (Subgroup.inclusion hKX) with hφ
  have hrange : φ.range = Lb := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← CFSG.mem_openPCoreOf_iff, ← CFSG.mem_openPCoreOf_iff,
      ← Res6.inf_pCoreOf_sup_eq hTK]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  let eL : Lb ≃* projSL 2 (GaloisField 2 n) :=
    (MulEquiv.subgroupCongr hrange.symm).trans ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans e))
  have hSbS : IsSylowOf 2 Sb ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hTX ⊢
    refine ⟨le_top, (hTX.2.1.comap_subtype (K := X)).map π, fun hdvd => hTX.2.2 ?_⟩
    rw [Subgroup.relIndex_top_right] at hdvd
    exact hdvd.trans (Subgroup.index_map_dvd (T.subgroupOf X) hπs)
  have hLS : Lb ⊔ Sb = ⊤ := by
    rw [hLb, hSb, ← Subgroup.map_sup, hJ, ← Subgroup.subgroupOf_sup hKX hTXle,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective π hπs]
  set P : Subgroup G :=
    ((Subgroup.normalizer ((Sb ⊓ Lb : Subgroup _) : Set _)).comap π).map X.subtype
  have hcgs : CFSG.Quasithin.cgsIn X T ≤ P := by
    refine iSup_le fun C => iSup_le fun hCT => iSup_le fun hC1 => iSup_le fun hCc => ?_
    have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mp (by haveI := hCc; infer_instance)
    set Nc : Subgroup ↥X := (Subgroup.normalizer (C : Set G)).subgroupOf X
    have hSN : Sb ≤ Nc.map π :=
      Subgroup.map_mono (fun t ht => hTC (Subgroup.mem_subgroupOf.mp ht))
    have hkerN : CFSG.pCore 2 ↥X ≤ Nc := fun x hx =>
      hTC (hQT ((CFSG.mem_openPCoreOf_iff x).mpr hx))
    rcases eq_top_or_le_normalizer (by omega) hLn eL hSbS hLS hSN with htop | hle
    · exfalso
      have hNtop : Nc = ⊤ := by
        have h1 := Subgroup.comap_map_eq π Nc
        rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hkerN] at h1
        exact h1.symm
      have hC1' : C.subgroupOf T ≠ ⊥ := fun h => hC1 (by
        rw [← Subgroup.map_subgroupOf_eq_of_le hCT, h, Subgroup.map_bot])
      refine h2 (C.subgroupOf T) hCc hC1' ?_
      rw [Subgroup.map_subgroupOf_eq_of_le hCT]
      intro x hx
      have : (⟨x, hx⟩ : ↥X) ∈ Nc := hNtop ▸ Subgroup.mem_top _
      exact this
    · rintro g ⟨hgX, hgN⟩
      exact ⟨⟨g, hgX⟩, hle (Subgroup.mem_map_of_mem π hgN), rfl⟩
  intro hX
  apply normalizer_ne_top hn hLn eL hSbS
  rw [eq_top_iff]
  intro z _
  obtain ⟨x, rfl⟩ := hπs z
  have hxc : (x : G) ∈ CFSG.Quasithin.cgsIn X T := by rw [hX]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hcgs hxc
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end CGS

private theorem isSubnormal_inf_normal {G : Type*} [Group G] {A B N : Subgroup G}
    (h : CFSG.Open.IsSubnormal A B) (hNB : N ≤ B) (hN : (N.subgroupOf B).Normal) :
    CFSG.Open.IsSubnormal (A ⊓ N) N := by
  induction h with
  | refl A =>
    rw [inf_eq_right.mpr hNB]
    exact CFSG.Open.IsSubnormal.refl _
  | step hAM hn _ ih =>
    refine CFSG.Open.IsSubnormal.step (inf_le_inf_right N hAM) ?_ (ih hNB hN)
    rw [Subgroup.normal_subgroupOf_iff hAM] at hn
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hAM)]
    intro x g hx hg
    exact ⟨hn x g hx.1 hg.1, N.mul_mem (N.mul_mem hg.2 hx.2) (N.inv_mem hg.2)⟩

end SimsStep2053

theorem step2053L2_of_localCGT (h316 : Sec19.Item316) :
    Step2053L2 := by
  intro G _ _ A M L N c T hT h2 n hn hn0 ⟨e⟩ h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hT.isSimpleGroup
  set K := kTwenty M c
  set X := K ⊔ T
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTM.trans hMK
  have hXM : X ≤ M := sup_le hKM hTM
  have hKX : K ≤ X := le_sup_left
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
  have hMloc := hT.mem_scriptM.1
  have hM2 : CFSG.Assembly.IsTwoLocal M := by
    obtain ⟨P, hP, hP2, hMP⟩ := hMloc.1
    exact ⟨P, hP, hP2, hMP⟩
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot hT.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hMloc)
  have hXtop : X ≠ ⊤ := fun h => hMtop (top_le_iff.mp (h ▸ hXM))
  have hKgrp : CFSG.Open.IsKGroup ↥X :=
    CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant hT.kProper X hXtop
  have hTX : IsSylowOf 2 T X := hT.sylow.of_le le_sup_right hXM
  have hOMX : CFSG.Open.pCoreOf 2 M ≤ X := (pCoreOf_le_of_isSylowOf hT.sylow).trans le_sup_right
  have hchar : CFSG.QuasithinUnique.CharTwo X := by
    have h1 : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOMX
        (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    intro x hx
    exact h1 (hT.charTwoType M hM2 ⟨hXM hx.1, Subgroup.centralizer_le h1 hx.2⟩)
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf T X := CFSG.ABGLocalTools.isSylowOf_iff.mp hTX
  have hcgs : CFSG.Quasithin.cgsIn X T ≠ X := by
    obtain ⟨r, hr⟩ := hn
    exact SimsStep2053.cgsIn_sup_ne (by omega) hTK hTX e h2
  obtain ⟨Y, hYX, hYs, hYblock, -⟩ :=
    LocalAnalysis.RankThreeTheoremC.aschbacherLocalCGTBlock_proved G X T hKgrp hchar hsyl hcgs
  have hYK : Y ≤ K := by
    have hN : (K.subgroupOf Y).Normal :=
      Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr fun y hy =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hXK (hYX hy), Subgroup.le_normalizer hy⟩
    refine Subgroup.subgroupOf_eq_top.mp (hYblock.1.1 (K.subgroupOf Y) ?_)
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha⟩ := Res6.exists_pow_mem_of_sup hT2 hTK (hYX y.2)
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact ha
  have hJn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hYK' : CFSG.Open.IsSubnormal Y K := by
    have := SimsStep2053.isSubnormal_inf_normal hYs hKX hJn
    rwa [inf_eq_left.mpr hYK] at this
  have hKn : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK
  have hKM' : CFSG.Open.IsSubnormal K M :=
    CFSG.Open.IsSubnormal.step hKM hKn (CFSG.Open.IsSubnormal.refl M)
  have hbl := Sec19.Item194Proof.isScriptLBlock_of_inClassXBlock (hYK.trans hKM)
    (hYK'.trans hKM') hYblock
  exact hT.not_inCatalog (h316 G hT.isSimpleGroup hT.nonabelian hT.kProper hT.charTwoType
    hT.evenRank_eq M Y hT.mem_scriptM.1 hbl)

end CFSG.RankThree.PartTwo.Sec20
