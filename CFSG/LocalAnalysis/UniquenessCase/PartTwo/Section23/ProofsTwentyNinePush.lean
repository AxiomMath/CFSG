module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.NormalizerLeN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedG
public import CFSG.Quasithin.Background.FFC4Small1
public import CFSG.LocalAnalysis.UniquenessCase.UC1S3Defs340

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem InS3.thompsonJ_eq_quasithin (X : Subgroup G) :
    InS3.thompsonJ X = CFSG.Quasithin.thompsonJ X := by
  rw [InS3.thompsonJ, CFSG.inSubgroup]
  exact CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ X

theorem InS3.omegaOneZJ_eq_quasithin (X : Subgroup G) :
    InS3.omegaOneZJ X = CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ X) := by
  rw [InS3.omegaOneZJ, CFSG.inSubgroup]
  exact CFSG.Quasithin.elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf X

theorem InS3.thompsonJ_eq_of_le {S R : Subgroup G} (hJ : InS3.thompsonJ S ≤ R)
    (hRS : R ≤ S) : InS3.thompsonJ R = InS3.thompsonJ S := by
  have hJ' : CFSG.Quasithin.thompsonJ S ≤ R := by
    simpa [InS3.thompsonJ_eq_quasithin] using hJ
  rw [InS3.thompsonJ_eq_quasithin, InS3.thompsonJ_eq_quasithin]
  exact CFSG.QuasithinUnique.GammaExtra.thompsonJ_eq_of_le hJ' hRS

private theorem isPGroup_quotient_of_sup_eq_top {H K T : Subgroup G}
    [hN : (K.subgroupOf H).Normal]
    (hKH : K ≤ H) (hTH : T ≤ H) (hsup : K ⊔ T = H) (hT2 : IsPGroup 2 T) :
    IsPGroup 2 (↥H ⧸ K.subgroupOf H) := by
  classical
  let N : Subgroup ↥H := K.subgroupOf H
  haveI hN' : N.Normal := hN
  change IsPGroup 2 (↥H ⧸ N)
  let π : ↥H →* (↥H ⧸ N) := QuotientGroup.mk' N
  have hsup' : N ⊔ T.subgroupOf H = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := K) (A' := T) (B := H) hKH hTH
    rw [hsup, Subgroup.subgroupOf_self] at h
    simpa [N] using h.symm
  rw [IsPGroup.iff_orderOf]
  intro q
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hs_top : s ∈ N ⊔ T.subgroupOf H := by rw [hsup']; trivial
  obtain ⟨l, hlN, t, htN, hlt⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := N) (t := T.subgroupOf H)).mp hs_top
  have hqeq : π s = π t := by
    rw [← hlt, map_mul]
    have hl1 : π l = 1 := (QuotientGroup.eq_one_iff (N := N) l).2 hlN
    rw [hl1, one_mul]
  let t' : ↥T := ⟨(t : G), Subgroup.mem_subgroupOf.mp htN⟩
  have htH : (t' : G) ∈ H := hTH t'.2
  have ht'_eq : (⟨(t' : G), htH⟩ : ↥H) = t := Subtype.ext rfl
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) t'
  rw [hqeq]
  have hdvd : orderOf (π t) ∣ 2 ^ k := by
    have hmap : orderOf (π t) ∣ orderOf t' := by
      have h1 : π t = π (⟨(t' : G), htH⟩ : ↥H) := by rw [ht'_eq]
      rw [h1]
      simpa [Subgroup.orderOf_coe] using orderOf_map_dvd π (⟨(t' : G), htH⟩ : ↥H)
    simpa [hk] using hmap
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, hj⟩

private theorem sup_pCoreOf_eq_of_barImage_eq_top {M K : Subgroup G} (hKM : K ≤ M)
    (h : barImage M K = ⊤) : K ⊔ CFSG.Open.pCoreOf 2 M = M := by
  refine le_antisymm (sup_le hKM (CFSG.openPCoreOf_le 2 M)) ?_
  intro x hx
  have hq : uc22p21cPi M ⟨x, hx⟩ ∈ (⊤ : Subgroup (Bar2 M)) := Subgroup.mem_top _
  rw [← h] at hq
  obtain ⟨m, hmK, hmq⟩ := uc22p21c_mem_barImage.1 hq
  have hmM : (m : G) ∈ M := m.2
  have hker : uc22p21cPi M (m⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hmq]
    group
  have hmemO : ((m : G)⁻¹ * x) ∈ CFSG.Open.pCoreOf 2 M := by
    refine (CFSG.mem_openPCoreOf_iff (⟨(m : G)⁻¹ * x,
      M.mul_mem (M.inv_mem hmM) hx⟩ : ↥M)).2 ?_
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥M) _).1 hker
  have hxeq : x = (m : G) * ((m : G)⁻¹ * x) := by group
  rw [hxeq]
  exact (K ⊔ CFSG.Open.pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left hmK)
    (Subgroup.mem_sup_right hmemO)

private theorem normal_subgroupOf_inf_thompsonJ {L H : Subgroup G} (hLH : L ≤ H) :
    ((InS3.thompsonJ H ⊓ L).subgroupOf L).Normal := by
  have hJH : H ≤ Subgroup.normalizer (InS3.thompsonJ H : Set G) := by
    refine (Subgroup.le_normalizer (H := H)).trans ?_
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ H
  have hLJ : L ≤ Subgroup.normalizer (InS3.thompsonJ H : Set G) := hLH.trans hJH
  have hLK : L ≤ Subgroup.normalizer (InS3.thompsonJ H ⊓ L : Set G) :=
    (le_inf hLJ (Subgroup.le_normalizer (H := L))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hLK

private theorem le_thompsonJ_of_barImage_eq_top {L H : Subgroup G} (hLH : L ≤ H)
    (hperf : ⁅L, L⁆ = L) (h : barImage L (InS3.thompsonJ H ⊓ L) = ⊤) :
    L ≤ InS3.thompsonJ H := by
  classical
  let K : Subgroup G := InS3.thompsonJ H ⊓ L
  have hKleL : K ≤ L := inf_le_right
  have hKnormal : (K.subgroupOf L).Normal := normal_subgroupOf_inf_thompsonJ hLH
  haveI : (K.subgroupOf L).Normal := hKnormal
  have hsup : K ⊔ CFSG.Open.pCoreOf 2 L = L :=
    sup_pCoreOf_eq_of_barImage_eq_top hKleL h
  have hO2p : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) := uc22main1_isPGroup_pCoreOf L
  have hQp : IsPGroup 2 (↥L ⧸ K.subgroupOf L) :=
    isPGroup_quotient_of_sup_eq_top hKleL (CFSG.openPCoreOf_le 2 L) hsup hO2p
  have hres : opResidual 2 L ≤ K := by
    refine CFSG.Quasithin.opResidual_le_of_pow_mem (p := 2) (A := L) (N := K) ?_
    intro x hx
    let xL : ↥L := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hQp.exists_pow_pow_eq_one (QuotientGroup.mk xL)
    refine ⟨k, ?_⟩
    have hmem : xL ^ 2 ^ k ∈ K.subgroupOf L :=
      (QuotientGroup.eq_one_iff (N := K.subgroupOf L) _).1 hk
    exact Subgroup.mem_subgroupOf.mp (by simpa using hmem)
  have hLperf : opResidual 2 L = L := CFSG.Quasithin.C2Nine.opResidual_eq_of_perfect hperf
  rw [hLperf] at hres
  exact hres.trans inf_le_left

private theorem inf_thompsonJ_le_pCoreOf_L {L H : Subgroup G} (hLH : L ≤ H)
    (hperf : ⁅L, L⁆ = L) (hsimple : IsSimpleGroup (Bar2 L))
    (hnot : ¬ L ≤ InS3.thompsonJ H) :
    InS3.thompsonJ H ⊓ L ≤ CFSG.Open.pCoreOf 2 L := by
  classical
  let K : Subgroup G := InS3.thompsonJ H ⊓ L
  have hKleL : K ≤ L := inf_le_right
  have hKnormal : (K.subgroupOf L).Normal := normal_subgroupOf_inf_thompsonJ hLH
  haveI : IsSimpleGroup (Bar2 L) := hsimple
  have hYnormal : (barImage L K).Normal :=
    hKnormal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  haveI : (barImage L K).Normal := hYnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (barImage L K) with hbot | htop
  · exact le_pCoreOf_of_barImage_eq_bot hKleL hbot
  · exact absurd (le_thompsonJ_of_barImage_eq_top hLH hperf htop) hnot

private theorem isPGroup_thompsonJ_of_not_le {L H T : Subgroup G} (hsup : L ⊔ T = H)
    (hLnormal : H ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hperf : ⁅L, L⁆ = L) (hsimple : IsSimpleGroup (Bar2 L))
    (hnot : ¬ L ≤ InS3.thompsonJ H) : IsPGroup 2 (InS3.thompsonJ H) := by
  classical
  have hLH : L ≤ H := le_sup_left.trans hsup.le
  have hTH : T ≤ H := le_sup_right.trans hsup.le
  let K : Subgroup G := InS3.thompsonJ H ⊓ L
  have hKleO2 : K ≤ CFSG.Open.pCoreOf 2 L :=
    inf_thompsonJ_le_pCoreOf_L hLH hperf hsimple hnot
  have hKp : IsPGroup 2 K := (uc22main1_isPGroup_pCoreOf L).to_le hKleO2
  have hKnormal : (K.subgroupOf L).Normal := normal_subgroupOf_inf_thompsonJ hLH
  haveI hN : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hLnormal
  have hQp : IsPGroup 2 (↥H ⧸ L.subgroupOf H) :=
    isPGroup_quotient_of_sup_eq_top (K := L) (T := T) hLH hTH hsup hT2
  have hJleH : InS3.thompsonJ H ≤ H := by
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.Quasithin.B6.thompsonJ_le H
  rw [isPGroup_iff_pow_pow_eq_one]
  intro j
  let jH : ↥H := ⟨(j : G), hJleH j.2⟩
  obtain ⟨k, hk⟩ := hQp.exists_pow_pow_eq_one (QuotientGroup.mk jH)
  have hmemN : jH ^ 2 ^ k ∈ L.subgroupOf H :=
    (QuotientGroup.eq_one_iff (N := L.subgroupOf H) _).1 hk
  have hmemL : (j : G) ^ 2 ^ k ∈ L :=
    Subgroup.mem_subgroupOf.mp (by simpa using hmemN)
  have hmemK : (j : G) ^ 2 ^ k ∈ K :=
    Subgroup.mem_inf.mpr ⟨(InS3.thompsonJ H).pow_mem j.2 _, hmemL⟩
  obtain ⟨m, hm⟩ := hKp.exists_pow_pow_eq_one (⟨(j : G) ^ 2 ^ k, hmemK⟩ : ↥K)
  refine ⟨k + m, ?_⟩
  apply Subtype.ext
  rw [pow_add, pow_mul]
  change ((j : G) ^ 2 ^ k) ^ 2 ^ m = 1
  simpa using congrArg Subtype.val hm

private theorem opResidual_eq_of_sup {L H T : Subgroup G} (hsup : L ⊔ T = H)
    (hLnormal : H ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hperf : ⁅L, L⁆ = L) : opResidual 2 H = L := by
  classical
  have hLH : L ≤ H := le_sup_left.trans hsup.le
  have hTH : T ≤ H := le_sup_right.trans hsup.le
  haveI hN : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hLnormal
  have hQp : IsPGroup 2 (↥H ⧸ L.subgroupOf H) :=
    isPGroup_quotient_of_sup_eq_top (K := L) (T := T) hLH hTH hsup hT2
  refine le_antisymm ?_ ?_
  · refine CFSG.Quasithin.opResidual_le_of_pow_mem (p := 2) (A := H) (N := L) ?_
    intro x hx
    let xH : ↥H := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hQp.exists_pow_pow_eq_one (QuotientGroup.mk xH)
    refine ⟨k, ?_⟩
    have hmem : xH ^ 2 ^ k ∈ L.subgroupOf H :=
      (QuotientGroup.eq_one_iff (N := L.subgroupOf H) _).1 hk
    exact Subgroup.mem_subgroupOf.mp (by simpa using hmem)
  · calc L = opResidual 2 L := (CFSG.Quasithin.C2Nine.opResidual_eq_of_perfect hperf).symm
      _ ≤ opResidual 2 H := CFSG.CGT.PushingUpLit.BHS.opResidual_mono 2 hLH

private theorem le_normalizer_thompsonJ_of_push {T T₀ X : Subgroup G} (hT₀T : T₀ ≤ T)
    (hJT : InS3.thompsonJ T ≤ T₀)
    (hX : X ≤ Subgroup.normalizer (T₀ : Set G)) :
    X ≤ Subgroup.normalizer (InS3.thompsonJ T : Set G) := by
  have hJeq : InS3.thompsonJ T₀ = InS3.thompsonJ T :=
    InS3.thompsonJ_eq_of_le hJT hT₀T
  rw [← hJeq]
  have hchar : Subgroup.normalizer (T₀ : Set G) ≤
      Subgroup.normalizer (InS3.thompsonJ T₀ : Set G) := by
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ T₀
  exact hX.trans hchar

private theorem fixV_barSub_eq_bot_of_binaryNaturalSL {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) {n : ℕ}
    (hnat : CFSG.Quasithin.BinaryNaturalSL (barSub ⊥ V hV L) ⊤ ⊥ 2 n) :
    CFSG.Quasithin.fixV (barSub ⊥ V hV L) = ⊥ := by
  obtain ⟨K, hKfield, hKfin, -, hreal⟩ := hnat
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have h := CFSG.Quasithin.FFC.fixV_inf_eq_bot_of_nat (d := 2) (by norm_num) hπ
  simpa using h

private theorem le_centralizer_of_le_center {L H Z : Subgroup G} (hLH : L ≤ H)
    (hZ : Z ≤ (Subgroup.center ↥H).map H.subtype) :
    L ≤ Subgroup.centralizer (Z : Set G) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨c, hc, hcz⟩ := hZ hz
  have hcomm : (c : ↥H) * ⟨l, hLH hl⟩ = ⟨l, hLH hl⟩ * c :=
    (Subgroup.mem_center_iff.mp hc _).symm
  have hval : (c : G) * (l : G) = (l : G) * (c : G) := congrArg Subtype.val hcomm
  have hzc : z = (c : G) := hcz.symm
  calc z * l = (c : G) * l := by rw [hzc]
    _ = l * (c : G) := hval
    _ = l * z := by rw [hzc]

private theorem Z_eq_bot_of_fixV_barSub_eq_bot {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {H : Subgroup G} (hLH : c.L ≤ H)
    (hV : IsElemAbelian 2 c.V)
    (hLcentral : c.L ≤ Subgroup.centralizer (D.Z : Set G))
    (hfix : CFSG.Quasithin.fixV (barSub ⊥ c.V hV c.L) = ⊥) :
    D.Z = ⊥ := by
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left.trans (Ctx23L.sup_le_N D Ch c)).trans
      (uc22p22v_le_normalizer_conjClosure c.N D.Z)
  have hLbot : c.L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hLstab : c.L ≤ stabTil ⊥ c.V := le_stabTil hLV hLbot
  rw [eq_bot_iff]
  intro z hz
  have hzV : z ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hz
  let x : IntMod c.V hV := IntMod.mk hV ⟨z, hzV⟩
  have hxfix : mkTil ⊥ c.V hV x ∈ CFSG.Quasithin.fixV (barSub ⊥ c.V hV c.L) := by
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨g, hgL, hgφ⟩ := (mem_barSub ⊥ c.V hV c.L φ).1 hφ
    rw [← hgφ, actTil_mk, mkTil_eq_iff, actStab_apply_val]
    change (g : G) * z * (g : G)⁻¹ * z⁻¹ ∈ (⊥ : Subgroup G)
    have hcomm : (g : G) * z * (g : G)⁻¹ = z := by
      have h1 := Subgroup.mem_centralizer_iff.mp (hLcentral hgL) z hz
      rw [← h1]
      group
    rw [hcomm]
    simp
  rw [hfix] at hxfix
  have hx1 : mkTil ⊥ c.V hV x = 1 := by simpa using hxfix
  have hmem : z * (1 : G)⁻¹ ∈ (⊥ : Subgroup G) := by
    refine (mkTil_eq_iff ⊥ c.V hV x (1 : IntMod c.V hV)).1 ?_
    simpa [x] using hx1
  simpa using hmem

private theorem not_omegaOneCenterIn_le_center {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {H : Subgroup G} (hLH : c.L ≤ H) {n : ℕ}
    (hV : IsElemAbelian 2 c.V)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (barSub ⊥ c.V hV c.L) ⊤ ⊥ 2 n) :
    ¬ CFSG.RankThree.PartOne.omegaOneCenterIn D.T ≤
      (Subgroup.center ↥H).map H.subtype := by
  intro hZ
  have hLcentral : c.L ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_of_le_center hLH hZ
  have hfix : CFSG.Quasithin.fixV (barSub ⊥ c.V hV c.L) = ⊥ :=
    fixV_barSub_eq_bot_of_binaryNaturalSL hV hnat
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left.trans (Ctx23L.sup_le_N D Ch c)).trans
      (uc22p22v_le_normalizer_conjClosure c.N D.Z)
  have hLbot : c.L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hLstab : c.L ≤ stabTil ⊥ c.V := le_stabTil hLV hLbot
  have hZbot : D.Z = ⊥ :=
    Z_eq_bot_of_fixV_barSub_eq_bot c hLH hV hLcentral hfix
  exact uc22main1_Z_ne_bot D hZbot

private theorem T_le_L_sup_pCoreOf {D : Data G} {Ch : Choice2011 G}
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    D.T ≤ c.L ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
  intro t ht
  obtain ⟨l, hl, htl⟩ :=
    Ctx23L.exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c ht
  have hlT : l ∈ D.T := (Subgroup.mem_inf.mp hl).1
  have hlL : l ∈ c.L := (Subgroup.mem_inf.mp hl).2
  have hmemC : t * l⁻¹ ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) :=
    ⟨D.T.mul_mem ht (D.T.inv_mem hlT), htl⟩
  have hO2 : t * l⁻¹ ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    centTVLeO2LT_of D Ch h4 h23 h1930 c hmemC
  have hteq : t = (t * l⁻¹) * l := by group
  rw [hteq]
  exact (c.L ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).mul_mem
    (Subgroup.mem_sup_right hO2) (Subgroup.mem_sup_left hlL)

private theorem k340_apply {D : Data G} {Ch : Choice2011 G} (hK340 : InS3.K340)
    (h23 : S23_23 D Ch) (hOff : OffenderV2329 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLJ : c.L ≤ InS3.thompsonJ (c.L ⊔ D.T))
    (hTLQ : D.T ≤ c.L ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) {X : Subgroup G}
    (hXNJ : X ⊔ D.T ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G)) :
    InS3.thompsonJ (c.L ⊔ D.T) ≤
        Subgroup.normalizer (conjClosure (X ⊔ D.T)
          (InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) : Set G) ∨
      ∃ a ∈ X ⊔ D.T,
        ⁅c.V, c.V.map (MulAut.conj a).toMonoidHom⁆ ≠ ⊥ := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let F : Subgroup G := InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 H)
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  obtain ⟨hV, hL2, hnat⟩ := h23 h1930 c
  obtain ⟨hFJ, hVJ, hVLW⟩ := hOff h1930 c
  have hHset : H ∈ hSet D.T D.M := c.hL.1.2.2.1
  have hHleN : H ≤ c.N := Ctx23L.sup_le_N D Ch c
  have hTH : D.T ≤ H := le_sup_right
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N :=
    D.sylowG.of_le (le_sup_right.trans hHleN) le_top
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := hSylN.of_le hTH hHleN
  have hHnormalL : H ≤ Subgroup.normalizer (c.L : Set G) :=
    sup_le (Subgroup.le_normalizer (H := c.L)) c.hL.1.1
  have hperf : ⁅c.L, c.L⁆ = c.L := c.hL.1.2.1
  have hResid : opResidual 2 H = c.L :=
    opResidual_eq_of_sup (L := c.L) (H := H) (T := D.T) rfl hHnormalL
      (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG) hperf
  have hnotCenter : ¬ CFSG.RankThree.PartOne.omegaOneCenterIn D.T ≤
      (Subgroup.center ↥H).map H.subtype :=
    not_omegaOneCenterIn_le_center c le_sup_left hV hnat
  have hVLW' : c.V = ⁅c.L, CFSG.RankThree.PartOne.omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 H)⁆ := hVLW hLJ |>.symm
  exact hK340 G H c.L D.T F c.V (X ⊔ D.T) n
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight.fstar_eq_pCoreOf_of_mem_hSet hHset)
    hResid.symm hL2 hSylH (sup_comm (c.L) D.T) hTLQ hnotCenter rfl hVLW' hFJ hVJ hXNJ
    (inf_le_right.trans le_sup_right)

private theorem commV_map_conj_eq_bot {D : Data G} {Ch : Choice2011 G} (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (hComm : CommV2329 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {T₀ : Subgroup G} (hT₀ : T₀ ≤ D.T)
    (hTnorm : D.T ≤ Subgroup.normalizer (T₀ : Set G))
    (hcyc : ∃ g ∈ D.T, D.T ≤ T₀ ⊔ Subgroup.zpowers g) (hVle : c.V ≤ T₀)
    {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (T₀ : Set G))
    (hXZ : X ≤ Subgroup.normalizer (D.Z : Set G)) {a : G} (ha : a ∈ X ⊔ D.T) :
    ⁅c.V, c.V.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
  have h4c := h4 h1930 c
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    simpa [h4c.1] using h4c.2.2
  have hTZ : D.T ≤ Subgroup.normalizer (D.Z : Set G) := D.sylowM.le.trans hMZ
  have haT₀ : a ∈ Subgroup.normalizer (T₀ : Set G) := (sup_le hX hTnorm) ha
  have haZ : a ∈ Subgroup.normalizer (D.Z : Set G) := (sup_le hXZ hTZ) ha
  have hUleT₀ : c.V.map (MulAut.conj a).toMonoidHom ≤ T₀ := by
    rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp haT₀ v).1 (hVle hv)
  have hcomm0 : ⁅T₀, c.V⁆ ≤ D.Z := by
    refine Subgroup.commutator_le.mpr ?_
    intro t ht v hv
    simpa [commutatorElement_def] using
      Ctx23L.commutator_mem_Z_of_mem_T D Ch h4 h23 h1930 c (hT₀ ht) hv
  have hmapZ : D.Z.map (MulAut.conj a).toMonoidHom = D.Z :=
    CFSG.QuasithinUnique.GammaExtra.map_conj_eq_self_of_mem_normalizer haZ
  have hmapT₀ : T₀.map (MulAut.conj a).toMonoidHom = T₀ :=
    CFSG.QuasithinUnique.GammaExtra.map_conj_eq_self_of_mem_normalizer haT₀
  have hmapcomm : ⁅T₀, c.V.map (MulAut.conj a).toMonoidHom⁆ =
      (⁅T₀, c.V⁆).map (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.map_commutator (H₁ := T₀) (H₂ := c.V)
      (f := (MulAut.conj a).toMonoidHom), hmapT₀]
  have hcommU : ⁅T₀, c.V.map (MulAut.conj a).toMonoidHom⁆ ≤ D.Z := by
    rw [hmapcomm]
    exact (Subgroup.map_mono hcomm0).trans (le_of_eq hmapZ)
  exact hComm h1930 c h3 T₀ hT₀ hTnorm hcyc
    (c.V.map (MulAut.conj a).toMonoidHom) hUleT₀ hcommU

private theorem V_le_omegaOneZJ {D : Data G} {Ch : Choice2011 G} (hOff : OffenderV2329 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLJ : c.L ≤ InS3.thompsonJ (c.L ⊔ D.T)) :
    c.V ≤ InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  have hVLW : c.V = ⁅c.L, W⁆ := ((hOff h1930 c).2.2 hLJ).symm
  have hRnormH : H ≤ Subgroup.normalizer (R : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact uc22main1_conj_mem_pCoreOf_self hh
    · intro hx
      have h := uc22main1_conj_mem_pCoreOf_self (K := H) (k := h⁻¹) (H.inv_mem hh) hx
      simpa [mul_assoc] using h
  have hWnormH : H ≤ Subgroup.normalizer (W : Set G) := by
    have h := hRnormH.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf R)
    simpa [W, CFSG.CGT.PushingUpLit.Glue.omegaOneCenterIn_eq] using h
  have hLnormW : c.L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hWnormH
  have hLWleW : ⁅c.L, W⁆ ≤ W := by
    have h := (Subgroup.le_normalizer_iff_commutator_le_left (H := c.L) (K := W)).mp hLnormW
    simpa [Subgroup.commutator_comm] using h
  have hWleF : W ≤ InS3.omegaOneZJ R := by
    rw [InS3.omegaOneZJ_eq_quasithin]
    have hWeq : W = CFSG.Quasithin.omegaOneCenterOf R :=
      CFSG.CGT.PushingUpLit.Glue.omegaOneCenterIn_eq R
    simpa [hWeq, CFSG.Quasithin.omegaOneCenterOf_eq] using
      omegaOneCenter_le_omegaOneCenterOf_thompsonJ R
  exact hVLW.le.trans (hLWleW.trans hWleF)

private theorem first_alternative_le_N {D : Data G} {Ch : Choice2011 G} (h4 : S23_4 D Ch)
    (hOff : OffenderV2329 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLJ : c.L ≤ InS3.thompsonJ (c.L ⊔ D.T)) {X : Subgroup G}
    (hXNJ : X ⊔ D.T ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G))
    (hN : InS3.thompsonJ (c.L ⊔ D.T) ≤ Subgroup.normalizer
      (conjClosure (X ⊔ D.T)
        (InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) : Set G)) :
    X ≤ c.N := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let F : Subgroup G := InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 H)
  let C : Subgroup G := conjClosure (X ⊔ D.T) F
  have hFJ : F ≤ InS3.thompsonJ D.T := (hOff h1930 c).1
  have hVF : c.V ≤ F := V_le_omegaOneZJ hOff h1930 c hLJ
  have hFne : F ≠ ⊥ := by
    intro hF
    exact c.V_ne_bot h4 h1930 (le_bot_iff.mp (hVF.trans (le_of_eq hF)))
  have hFC : F ≤ C := uc22p22v_le_conjClosure (X ⊔ D.T) F
  have hCne : C ≠ ⊥ := by
    intro hC
    exact hFne (le_bot_iff.mp (hFC.trans (le_of_eq hC)))
  have hCJ : C ≤ InS3.thompsonJ D.T :=
    uc22p22v_conjClosure_le hXNJ hFJ
  have hJleT : InS3.thompsonJ D.T ≤ D.T := by
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.Quasithin.B6.thompsonJ_le D.T
  have hC2 : IsPGroup 2 C :=
    (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG).to_le (hCJ.trans hJleT)
  have hX'normC : X ⊔ D.T ≤ Subgroup.normalizer (C : Set G) :=
    uc22p22v_le_normalizer_conjClosure (X ⊔ D.T) F
  have hHC : c.L ⊔ D.T ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hLJ.trans hN) (le_sup_right.trans hX'normC)
  have hNle : Subgroup.normalizer (C : Set G) ≤ c.N :=
    Ctx23L.normalizer_le_N_of_isPGroup c hCne hC2 hHC
  exact (le_sup_left.trans hX'normC).trans hNle

private theorem thompsonJ_sup_eq_of_not_le {D : Data G} {Ch : Choice2011 G}
    (h4 : S23_4 D Ch) (hOff : OffenderV2329 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hsimple : IsSimpleGroup (Bar2 c.L)) {X : Subgroup G}
    (hLnot : ¬ c.L ≤ InS3.thompsonJ (c.L ⊔ D.T))
    (hXJ : X ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G)) :
    IsPGroup 2 (InS3.thompsonJ (c.L ⊔ D.T)) ∧
      InS3.thompsonJ (c.L ⊔ D.T) ≤ D.T ∧
        InS3.thompsonJ D.T = InS3.thompsonJ (c.L ⊔ D.T) := by
  let H : Subgroup G := c.L ⊔ D.T
  have hT2 : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG
  have hTH : D.T ≤ H := le_sup_right
  have hHleN : H ≤ c.N := Ctx23L.sup_le_N D Ch c
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N :=
    D.sylowG.of_le (le_sup_right.trans hHleN) le_top
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := hSylN.of_le hTH hHleN
  have hHnormalL : H ≤ Subgroup.normalizer (c.L : Set G) :=
    sup_le (Subgroup.le_normalizer (H := c.L)) c.hL.1.1
  have hperf : ⁅c.L, c.L⁆ = c.L := c.hL.1.2.1
  have hJp : IsPGroup 2 (InS3.thompsonJ H) :=
    isPGroup_thompsonJ_of_not_le (L := c.L) (H := H) (T := D.T) rfl hHnormalL hT2 hperf
      hsimple hLnot
  have hJleH : InS3.thompsonJ H ≤ H := by
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.Quasithin.B6.thompsonJ_le H
  have hJnormH : H ≤ Subgroup.normalizer (InS3.thompsonJ H : Set G) := by
    refine (Subgroup.le_normalizer (H := H)).trans ?_
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ H
  have hJleO2 : InS3.thompsonJ H ≤ CFSG.Open.pCoreOf 2 H :=
    uc22main1_le_pCoreOf hJleH hJp fun k hk x hx =>
      (Subgroup.mem_normalizer_iff.mp (hJnormH hk) x).1 hx
  have hJleT : InS3.thompsonJ H ≤ D.T :=
    hJleO2.trans (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylH))
  exact ⟨hJp, hJleT, InS3.thompsonJ_eq_of_le (S := H) (R := D.T) hJleT hTH⟩

private theorem push_case_not_le {D : Data G} {Ch : Choice2011 G} (h4 : S23_4 D Ch)
    (hOff : OffenderV2329 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hsimple : IsSimpleGroup (Bar2 c.L)) {X : Subgroup G}
    (hLnot : ¬ c.L ≤ InS3.thompsonJ (c.L ⊔ D.T))
    (hXJ : X ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G)) :
    X ≤ c.N := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  obtain ⟨hJp, hJleT, hJeq⟩ :=
    thompsonJ_sup_eq_of_not_le h4 hOff h1930 c hsimple hLnot hXJ
  have hJnormH : H ≤ Subgroup.normalizer (InS3.thompsonJ H : Set G) := by
    refine (Subgroup.le_normalizer (H := H)).trans ?_
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ H
  have hJp2 : IsPGroup 2 (InS3.thompsonJ D.T) := by
    rw [hJeq]
    exact hJp
  have hVJ : c.V ≤ InS3.thompsonJ D.T := (hOff h1930 c).2.1
  have hJne : InS3.thompsonJ D.T ≠ ⊥ := by
    intro hbot
    exact c.V_ne_bot h4 h1930 (le_bot_iff.mp (hVJ.trans (le_of_eq hbot)))
  have hHnormJ : H ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G) := by
    rw [hJeq]
    exact hJnormH
  exact hXJ.trans (Ctx23L.normalizer_le_N_of_isPGroup c hJne hJp2 hHnormJ)

theorem push2329_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (hK340 : InS3.K340) (hComm : CommV2329 D Ch) (hOff : OffenderV2329 D Ch) :
    Push2329 D Ch := by
  intro h1930 c h3 T₀ hT₀ hTnorm hcyc hVle hJT X hX hXZ
  classical
  let H : Subgroup G := c.L ⊔ D.T
  obtain ⟨hV, hL2, hnat⟩ := h23 h1930 c
  haveI : IsSimpleGroup (Bar2 c.L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  have hXJ : X ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G) :=
    le_normalizer_thompsonJ_of_push hT₀ hJT hX
  have hTJ : D.T ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G) := by
    refine (Subgroup.le_normalizer (H := D.T)).trans ?_
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ D.T
  have hXNJ : X ⊔ D.T ≤ Subgroup.normalizer (InS3.thompsonJ D.T : Set G) :=
    sup_le hXJ hTJ
  by_cases hLJ : c.L ≤ InS3.thompsonJ H
  · have hK := k340_apply hK340 h23 hOff h1930 c hLJ
        (T_le_L_sup_pCoreOf h4 h23 h1930 c) hXNJ
    rcases hK with hfirst | ⟨a, ha, hne⟩
    · exact first_alternative_le_N h4 hOff h1930 c hLJ hXNJ hfirst
    · exact absurd (commV_map_conj_eq_bot h4 h23 hComm h1930 c h3 hT₀ hTnorm hcyc hVle hX hXZ ha)
        hne
  · exact push_case_not_le h4 hOff h1930 c inferInstance hLJ hXJ

end CFSG.LocalAnalysis.UniquenessCase.UC22
