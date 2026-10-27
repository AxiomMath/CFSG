module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.GroupTheory.Commutator.SupNormalizer
import CFSG.GroupTheory.PerfectCentralizer
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGenericCatalog
import CFSG.Quasithin.Vol2.Ch11SKFCompA
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma fixed_iff_zpowers_generator {A X : Type*} [Group A] [Group X]
    (γ : A →* MulAut X) (g : A) (hg : Subgroup.zpowers g = ⊤) (x : X) :
    (∀ a : A, γ a x = x) ↔ γ g x = x := by
  refine ⟨fun h => h g, fun h a => ?_⟩
  have ha : a ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top a
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hgn : γ a = (γ g) ^ n := by rw [← hn, map_zpow]
  rw [hgn]
  have hfix : x ∈ MulAction.fixedBy X (γ g) := h
  have hpow := MulAction.mem_fixedBy_zpow hfix n
  change (γ g ^ n) x = x at hpow
  exact hpow

private abbrev zpowersGen (e : G) : ↥(Subgroup.zpowers e) := ⟨e, Subgroup.mem_zpowers e⟩

private noncomputable abbrev compConjAction (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) : ↥(Subgroup.zpowers e) →* MulAut ↥K :=
  (Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr heK))

private lemma compConjAction_gen_apply (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (x : ↥K) :
    ((compConjAction K e heK (zpowersGen e) x : ↥K) : G) = e * (x : G) * e⁻¹ := by
  rw [compConjAction, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

private lemma compConjAction_mem_center (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (a : ↥(Subgroup.zpowers e))
    {n : ↥K} (hn : n ∈ Subgroup.center ↥K) :
    compConjAction K e heK a n ∈ Subgroup.center ↥K := by
  have hmap : (Subgroup.center ↥K).map
      ((compConjAction K e heK a : MulAut ↥K).toMonoidHom) = Subgroup.center ↥K :=
    Subgroup.map_center_eq (compConjAction K e heK a)
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hn

private noncomputable abbrev compConjActionCenter (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) :
    ↥(Subgroup.zpowers e) →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction (compConjAction K e heK)
    (Subgroup.center ↥K) (compConjAction_mem_center K e heK)

private abbrev centralizerIn (K : Subgroup G) (e : G) : Subgroup G :=
  K ⊓ Subgroup.centralizer ({e} : Set G)

private abbrev centerQuotientMap (K : Subgroup G) : ↥K →* (↥K ⧸ Subgroup.center ↥K) :=
  QuotientGroup.mk' (Subgroup.center ↥K)

private theorem exists_suzukiModel_centerQuotient
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hKP : CFSG.Open.IsKProper G)
    {H K : Subgroup G} (hHtop : H ≠ ⊤) (hK : CFSG.GorensteinWalter.IsComponentOf K H)
    (hK3 : ¬ 3 ∣ Nat.card K) :
    ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 f := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥K := ⟨hK.2.2.2.1, hK.2.2.2.2⟩
  have hKH : CFSG.Open.IsKGroup ↥H := hKP.isKGroup H hHtop
  have hKG : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hKH hK.1
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup hq hKG
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have h3 : ¬ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := fun h =>
    hK3 (h.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥K)))
  have hnab :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_noncomm_quotient_center_of_quasisimple
      hq
  exact hKPSz _ hnab hcat h3

private theorem orderOf_compConjActionCenter_eq_three {H K : Subgroup G} {e : G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (he : e ^ 3 = 1)
    (heK : e ∈ Subgroup.normalizer (K : Set G))
    (hcent : ¬ ∀ k : ↥K, compConjAction K e heK (zpowersGen e) k = k) :
    orderOf (compConjActionCenter K e heK (zpowersGen e)) = 3 := by
  classical
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hK.2.2.2.1
  have hβne : compConjActionCenter K e heK (zpowersGen e) ≠ 1 := by
    intro hβ
    apply hcent
    have hα1 : compConjAction K e heK (zpowersGen e) = 1 := by
      refine CFSG.GroupTheory.MulAut.eq_one_of_mul_mem_center hperf _ ?_
      intro x
      have h1 : centerQuotientMap K (compConjAction K e heK (zpowersGen e) x) =
          centerQuotientMap K x := by
        show QuotientGroup.mk ((compConjAction K e heK (zpowersGen e)) x) = QuotientGroup.mk x
        have h := congrArg (fun g : MulAut (↥K ⧸ Subgroup.center ↥K) =>
          g (QuotientGroup.mk x)) hβ
        simpa only [compConjActionCenter, MulAut.one_apply,
          CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk] using h
      have h2 : centerQuotientMap K (compConjAction K e heK (zpowersGen e) x * x⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h2
    intro k
    have h := congrArg (fun g : MulAut ↥K => g k) hα1
    simpa only [MulAut.one_apply] using h
  have hpow : compConjActionCenter K e heK (zpowersGen e) ^ 3 = 1 := by
    have h3 : zpowersGen e ^ 3 = 1 := by
      apply Subtype.ext
      simpa [zpowersGen] using he
    calc compConjActionCenter K e heK (zpowersGen e) ^ 3
        = compConjActionCenter K e heK (zpowersGen e ^ 3) := (map_pow _ _ 3).symm
      _ = 1 := by rw [h3, map_one]
  exact orderOf_eq_prime hpow hβne

private lemma mem_subgroupOf_centralizer_iff (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (c : ↥K) :
    c ∈ (centralizerIn K e).subgroupOf K ↔ compConjAction K e heK (zpowersGen e) c = c := by
  rw [centralizerIn, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hcomm⟩
    apply Subtype.ext
    rw [compConjAction_gen_apply, hcomm e (Set.mem_singleton e)]
    group
  · intro hc
    have hce : e * (c : G) = (c : G) * e := by
      have h1 : e * (c : G) * e⁻¹ = (c : G) := by
        rw [← compConjAction_gen_apply K e heK c]
        exact congrArg Subtype.val hc
      calc e * (c : G) = (e * (c : G) * e⁻¹) * e := by group
        _ = (c : G) * e := by rw [h1]
    exact ⟨c.2, fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hce⟩

private lemma zpowers_zpowersGen (e : G) : Subgroup.zpowers (zpowersGen e) = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (a.2 : (a : G) ∈ Subgroup.zpowers e)
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

private lemma fixed_set_eq_centralizer (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) :
    {c : ↥K | ∀ a : ↥(Subgroup.zpowers e), compConjAction K e heK a c = c} =
      ((centralizerIn K e).subgroupOf K : Set ↥K) := by
  ext c
  rw [Set.mem_setOf_eq, fixed_iff_zpowers_generator _ (zpowersGen e) (zpowers_zpowersGen e)]
  exact (mem_subgroupOf_centralizer_iff K e heK c).symm

private lemma fixed_set_center_eq_generator (K : Subgroup G) (e : G)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) :
    {q : ↥K ⧸ Subgroup.center ↥K | ∀ a : ↥(Subgroup.zpowers e),
        compConjActionCenter K e heK a q = q} =
      {q : ↥K ⧸ Subgroup.center ↥K |
        compConjActionCenter K e heK (zpowersGen e) q = q} := by
  ext q
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
    fixed_iff_zpowers_generator _ (zpowersGen e) (zpowers_zpowersGen e)]

private theorem map_subgroupOf_centralizer_eq_eqLocus {H K : Subgroup G} {e : G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (he : e ^ 3 = 1)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (hK3 : ¬ 3 ∣ Nat.card K) :
    ((centralizerIn K e).subgroupOf K).map (centerQuotientMap K) =
      MonoidHom.eqLocus (compConjActionCenter K e heK (zpowersGen e)).toMonoidHom
        (MonoidHom.id (↥K ⧸ Subgroup.center ↥K)) := by
  classical
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) :=
    fun h => hK3 (h.trans (Subgroup.card_subgroup_dvd_card (Subgroup.center ↥K)))
  have hA3 : IsPGroup 3 ↥(Subgroup.zpowers e) := by
    have hcard : Nat.card ↥(Subgroup.zpowers e) = orderOf e := Nat.card_zpowers e
    obtain h | h := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf e)
      (orderOf_dvd_iff_pow_eq_one.mpr he)
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h]; norm_num)
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting
    (A := ↥(Subgroup.zpowers e)) (G := ↥K) 3 hA3 (compConjAction K e heK)
      (Subgroup.center ↥K) (compConjAction_mem_center K e heK) h3Z
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    change compConjActionCenter K e heK (zpowersGen e) (QuotientGroup.mk c) = QuotientGroup.mk c
    have hc' : c ∈ {c : ↥K | ∀ a : ↥(Subgroup.zpowers e), compConjAction K e heK a c = c} := by
      rw [fixed_set_eq_centralizer K e heK]; exact hc
    exact congrArg (centerQuotientMap K) (hc' (zpowersGen e))
  · intro hq
    change compConjActionCenter K e heK (zpowersGen e) q = q at hq
    have hq' : q ∈ {q : ↥K ⧸ Subgroup.center ↥K |
        ∀ a : ↥(Subgroup.zpowers e), compConjActionCenter K e heK a q = q} := by
      rw [fixed_set_center_eq_generator K e heK]; exact hq
    rw [hlift] at hq'
    obtain ⟨c, hc, hcq⟩ := hq'
    refine ⟨c, ?_, hcq⟩
    rw [fixed_set_eq_centralizer K e heK] at hc
    exact hc

private theorem five_dvd_card_centralizer
    {H K : Subgroup G} {e : G} {f : ℕ}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (hK3 : ¬ 3 ∣ Nat.card K)
    (he : e ^ 3 = 1) (heK : e ∈ Subgroup.normalizer (K : Set G))
    (hcent : ¬ ∀ k : ↥K, compConjAction K e heK (zpowersGen e) k = k)
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 f) :
    5 ∣ Nat.card (((centralizerIn K e).subgroupOf K).map (centerQuotientMap K)) := by
  classical
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have h3Kb : ¬ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := fun h =>
    hK3 (h.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥K)))
  rw [map_subgroupOf_centralizer_eq_eqLocus hK he heK hK3]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.five_dvd_card_fixed hSz h3Kb _
    (orderOf_compConjActionCenter_eq_three hK he heK hcent)

private theorem map_subgroupOf_sup_centralizer_eq_top_of_not_centralizing
    {H K M T : Subgroup G} {e : G} {f : ℕ}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (hK3 : ¬ 3 ∣ Nat.card K) (he : e ^ 3 = 1)
    (heK : e ∈ Subgroup.normalizer (K : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T K) (hTM : T ≤ M)
    (hCM : centralizerIn K e ≤ M)
    (hcent : ¬ ∀ k : ↥K, compConjAction K e heK (zpowersGen e) k = k)
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 f) :
    (((centralizerIn K e ⊔ T).subgroupOf K).map (centerQuotientMap K)) = ⊤ := by
  classical
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) :=
    (⟨hK.2.2.2.1, hK.2.2.2.2⟩ : CFSG.Open.IsQuasisimple ↥K).2
  by_contra hJtop
  have h5 := five_dvd_card_centralizer hK hK3 he heK hcent hSz
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  let S : Sylow 2 (↥K ⧸ Subgroup.center ↥K) :=
    Sylow.mapSurjective (p := 2) (QuotientGroup.mk'_surjective (Subgroup.center ↥K)) Q
  have hScoe : (S : Subgroup (↥K ⧸ Subgroup.center ↥K)) =
      (T.subgroupOf K).map (centerQuotientMap K) := by
    rw [Sylow.coe_mapSurjective, hQ]
  have hJTsyl : (S : Subgroup (↥K ⧸ Subgroup.center ↥K)) ≤
      (((centralizerIn K e ⊔ T).subgroupOf K).map (centerQuotientMap K)) := by
    rw [hScoe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K le_sup_right)
  have hJ5 : 5 ∣ Nat.card
      (((centralizerIn K e ⊔ T).subgroupOf K).map (centerQuotientMap K)) :=
    h5.trans (Subgroup.card_dvd_of_le
      (Subgroup.map_mono (Subgroup.subgroupOf_mono K le_sup_left)))
  have hle := CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.le_normalizer_of_suzuki
    hSz S hJTsyl hJtop
  exact absurd (hJ5.trans (Subgroup.card_dvd_of_le hle))
    (CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.not_five_dvd_normalizer hSz S)

private theorem le_sup_of_map_subgroupOf_eq_top {K J : Subgroup G}
    (hperf : Group.IsPerfect ↥K) (hJK : J ≤ K)
    (hJtop : ((J.subgroupOf K).map (centerQuotientMap K)) = ⊤) : K ≤ J := by
  classical
  haveI : Group.IsPerfect ↥K := hperf
  let Z : Subgroup ↥K := Subgroup.center ↥K
  have hJZ : (J.subgroupOf K) ⊔ Z = ⊤ := by
    have h := Subgroup.comap_map_eq (f := centerQuotientMap K) (J.subgroupOf K)
    rw [hJtop, QuotientGroup.ker_mk'] at h
    simpa using h.symm
  have hperf' : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := Subgroup.commutator_eq_self
  have hcomm1 : ⁅(J.subgroupOf K) ⊔ Z, (J.subgroupOf K) ⊔ Z⁆ =
      ⁅J.subgroupOf K, J.subgroupOf K⁆ := by
    have hZcent : Z ≤ Subgroup.centralizer
        (((J.subgroupOf K) ⊔ Z : Subgroup ↥K) : Set ↥K) := Subgroup.center_le_centralizer _
    have hZcentJ : Z ≤ Subgroup.centralizer ((J.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
      Subgroup.center_le_centralizer _
    have hZnorm : Z ≤ Subgroup.normalizer ((J.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
      hZcentJ.trans (Subgroup.centralizer_le_normalizer _)
    calc ⁅(J.subgroupOf K) ⊔ Z, (J.subgroupOf K) ⊔ Z⁆
        = ⁅J.subgroupOf K, (J.subgroupOf K) ⊔ Z⁆ :=
          CFSG.commutator_sup_eq_commutator_left hZnorm hZcent
      _ = ⁅(J.subgroupOf K) ⊔ Z, J.subgroupOf K⁆ := Subgroup.commutator_comm _ _
      _ = ⁅J.subgroupOf K, J.subgroupOf K⁆ :=
          CFSG.commutator_sup_eq_commutator_left hZnorm hZcentJ
  have hle : (⊤ : Subgroup ↥K) ≤ J.subgroupOf K := by
    rw [← hperf', ← hJZ, hcomm1]
    simpa using Subgroup.commutator_le_sup (J.subgroupOf K) (J.subgroupOf K)
  have hJ'eq : (J.subgroupOf K) = ⊤ := top_le_iff.mp hle
  rw [← Subgroup.map_subgroupOf_eq_of_le hJK, hJ'eq, Subgroup.map_top,
    Subgroup.range_subtype]

private lemma centralizerIn_eq_of_centralizing {K : Subgroup G} {e : G}
    (heK : e ∈ Subgroup.normalizer (K : Set G))
    (hcent : ∀ k : ↥K, compConjAction K e heK (zpowersGen e) k = k) :
    centralizerIn K e = K := by
  refine le_antisymm inf_le_left ?_
  refine le_inf le_rfl ?_
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have h1 : e * k * e⁻¹ = k := by
    rw [← compConjAction_gen_apply K e heK ⟨k, hk⟩]
    exact congrArg Subtype.val (hcent ⟨k, hk⟩)
  calc e * k = (e * k * e⁻¹) * e := by group
    _ = k * e := by rw [h1]

theorem le_of_suzuki_component
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hKP : CFSG.Open.IsKProper G)
    {H K M T : Subgroup G} {e : G} (hHtop : H ≠ ⊤)
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (hK3 : ¬ 3 ∣ Nat.card K) (he : e ^ 3 = 1)
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T K)
    (hTM : T ≤ M) (hCM : K ⊓ Subgroup.centralizer ({e} : Set G) ≤ M) : K ≤ M := by
  classical
  obtain ⟨f, hSz⟩ := exists_suzukiModel_centerQuotient hKPSz hKP hHtop hK hK3
  by_cases hcent : ∀ k : ↥K, compConjAction K e heK (zpowersGen e) k = k
  · have hCK : K ⊓ Subgroup.centralizer ({e} : Set G) = K :=
      centralizerIn_eq_of_centralizing heK hcent
    rw [hCK] at hCM
    exact hCM
  · have hJtop := map_subgroupOf_sup_centralizer_eq_top_of_not_centralizing
      hK hK3 he heK hT hTM hCM hcent hSz
    have hKJ : K ≤ centralizerIn K e ⊔ T :=
      le_sup_of_map_subgroupOf_eq_top (Group.isPerfect_def.mpr hK.2.2.2.1)
        (sup_le inf_le_left hT.le) hJtop
    exact hKJ.trans (sup_le hCM hTM)

private lemma map_conj_sq_map_conj {K : Subgroup G} {e : G} (he : e ^ 3 = 1) :
    (K.map (MulAut.conj (e ^ 2)).toMonoidHom).map (MulAut.conj e).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have hmul : (MulAut.conj e) * (MulAut.conj (e ^ 2)) = 1 := by
    rw [← map_mul, show e * e ^ 2 = e ^ 3 by group, he, map_one]
  have hcomp : (MulAut.conj e).toMonoidHom.comp (MulAut.conj (e ^ 2)).toMonoidHom =
      MonoidHom.id G := by
    calc (MulAut.conj e).toMonoidHom.comp (MulAut.conj (e ^ 2)).toMonoidHom
        = ((MulAut.conj e) * (MulAut.conj (e ^ 2))).toMonoidHom := rfl
      _ = (1 : MulAut G).toMonoidHom := by rw [hmul]
      _ = MonoidHom.id G := rfl
  rw [hcomp]
  exact Subgroup.map_id K

private lemma map_conj_sq_ne {K : Subgroup G} {e : G} (he : e ^ 3 = 1)
    (hKe : K.map (MulAut.conj e).toMonoidHom ≠ K) :
    K.map (MulAut.conj (e ^ 2)).toMonoidHom ≠ K := by
  intro h
  apply hKe
  have h1 : K = K.map (MulAut.conj e).toMonoidHom := by
    calc K = (K.map (MulAut.conj (e ^ 2)).toMonoidHom).map (MulAut.conj e).toMonoidHom :=
          (map_conj_sq_map_conj (K := K) he).symm
      _ = K.map (MulAut.conj e).toMonoidHom := by rw [h]
  exact h1.symm

private theorem diagonal_mem_centralizer {H K K1 K2 : Subgroup G} {e : G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H)
    (hK1c : CFSG.GorensteinWalter.IsComponentOf K1 H)
    (hK2c : CFSG.GorensteinWalter.IsComponentOf K2 H)
    (hK1ne : K1 ≠ K) (hK2ne : K2 ≠ K)
    (hK1 : K1 = K.map (MulAut.conj e).toMonoidHom)
    (hK2 : K2 = K.map (MulAut.conj (e ^ 2)).toMonoidHom)
    (he : e ^ 3 = 1) {x : G} (hx : x ∈ K) :
    x * (e * x * e⁻¹) * (e ^ 2 * x * (e ^ 2)⁻¹) ∈
      Subgroup.centralizer ({e} : Set G) := by
  set x1 : G := e * x * e⁻¹ with hx1
  set x2 : G := e ^ 2 * x * (e ^ 2)⁻¹ with hx2
  have hx1K : x1 ∈ K1 := by
    rw [hx1, hK1]
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    change (MulAut.conj e) x = x1
    rw [MulAut.conj_apply, ← hx1]
  have hx2K : x2 ∈ K2 := by
    rw [hx2, hK2]
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    change (MulAut.conj (e ^ 2)) x = x2
    rw [MulAut.conj_apply, ← hx2]
  have hx1x : x1 * x = x * x1 :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.mul_comm_of_ne hK1c hK hK1ne hx1K hx
  have hx2x : x2 * x = x * x2 :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.mul_comm_of_ne hK2c hK hK2ne hx2K hx
  have hx1e : e * x1 * e⁻¹ = x2 := by rw [hx1, hx2, pow_two]; group
  have hmul : (MulAut.conj e) * (MulAut.conj (e ^ 2)) = 1 := by
    rw [← map_mul, show e * e ^ 2 = e ^ 3 by group, he, map_one]
  have hx2e : e * x2 * e⁻¹ = x := by
    rw [hx2]
    have h := congrArg (fun f : MulAut G => f x) hmul
    simpa only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] using h
  have hfixe : e * (x * x1 * x2) * e⁻¹ = x * x1 * x2 := by
    calc e * (x * x1 * x2) * e⁻¹
        = (e * x * e⁻¹) * (e * x1 * e⁻¹) * (e * x2 * e⁻¹) := by group
      _ = x1 * x2 * x := by rw [hx1, hx1e, hx2e]
      _ = x * x1 * x2 := by rw [mul_assoc, hx2x, ← mul_assoc, hx1x]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  calc e * (x * x1 * x2) = (e * (x * x1 * x2) * e⁻¹) * e := by group
    _ = (x * x1 * x2) * e := by rw [hfixe]

private theorem subgroupOf_inf_normal {H K K1 K2 M : Subgroup G} {e : G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H)
    (hK1c : CFSG.GorensteinWalter.IsComponentOf K1 H)
    (hK2c : CFSG.GorensteinWalter.IsComponentOf K2 H)
    (hK1ne : K1 ≠ K) (hK2ne : K2 ≠ K)
    (hK1 : K1 = K.map (MulAut.conj e).toMonoidHom)
    (hK2 : K2 = K.map (MulAut.conj (e ^ 2)).toMonoidHom)
    (he : e ^ 3 = 1) (hCM : Subgroup.centralizer ({e} : Set G) ≤ M) :
    ((K ⊓ M).subgroupOf K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  have hnK : (n : G) ∈ K := (Subgroup.mem_subgroupOf.mp hn).1
  have hnM : (n : G) ∈ M := (Subgroup.mem_subgroupOf.mp hn).2
  have hxK : (g : G) ∈ K := g.2
  refine ⟨K.mul_mem (K.mul_mem hxK hnK) (K.inv_mem hxK), ?_⟩
  set x : G := (g : G) with hx
  set m : G := (n : G) with hm
  set x1 : G := e * x * e⁻¹ with hx1
  set x2 : G := e ^ 2 * x * (e ^ 2)⁻¹ with hx2
  have hx1K : x1 ∈ K1 := by
    rw [hx1, hK1]
    refine Subgroup.mem_map.mpr ⟨x, hxK, ?_⟩
    change (MulAut.conj e) x = x1
    rw [MulAut.conj_apply, ← hx1]
  have hx2K : x2 ∈ K2 := by
    rw [hx2, hK2]
    refine Subgroup.mem_map.mpr ⟨x, hxK, ?_⟩
    change (MulAut.conj (e ^ 2)) x = x2
    rw [MulAut.conj_apply, ← hx2]
  have hx1m : x1 * m = m * x1 :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.mul_comm_of_ne hK1c hK hK1ne hx1K hnK
  have hx2m : x2 * m = m * x2 :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.mul_comm_of_ne hK2c hK hK2ne hx2K hnK
  have hdM : x * x1 * x2 ∈ M := by
    refine hCM ?_
    rw [hx1, hx2]
    exact diagonal_mem_centralizer hK hK1c hK2c hK1ne hK2ne hK1 hK2 he hxK
  have hx1c : x1 * m * x1⁻¹ = m := by rw [hx1m]; group
  have hx2c : x2 * m * x2⁻¹ = m := by rw [hx2m]; group
  have hd : (x * x1 * x2) * m * (x * x1 * x2)⁻¹ = x * m * x⁻¹ := by
    calc (x * x1 * x2) * m * (x * x1 * x2)⁻¹
        = x * (x1 * (x2 * m * x2⁻¹) * x1⁻¹) * x⁻¹ := by group
      _ = x * (x1 * m * x1⁻¹) * x⁻¹ := by rw [hx2c]
      _ = x * m * x⁻¹ := by rw [hx1c]
  change x * m * x⁻¹ ∈ M
  rw [← hd]
  exact mul_mem (mul_mem hdM hnM) (inv_mem hdM)

private theorem le_of_normal_not_le_center {K M T : Subgroup G}
    (hqs : CFSG.GorensteinWalter.IsQuasisimple ↥K)
    (hN : ((K ⊓ M).subgroupOf K).Normal)
    (hTK : T ≤ K) (hTM : T ≤ M)
    (hTZ : ¬ T ≤ (Subgroup.center ↥K).map K.subtype) : K ≤ M := by
  rcases CFSG.GorensteinWalter.normal_subgroup_le_center_or_eq_top hqs
    ((K ⊓ M).subgroupOf K) hN with hcen | htop
  · exfalso
    apply hTZ
    have hTN : T.subgroupOf K ≤ (K ⊓ M).subgroupOf K := by
      intro t ht
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hTK (Subgroup.mem_subgroupOf.mp ht), hTM (Subgroup.mem_subgroupOf.mp ht)⟩
    calc T = (T.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hTK).symm
      _ ≤ ((K ⊓ M).subgroupOf K).map K.subtype := Subgroup.map_mono hTN
      _ ≤ (Subgroup.center ↥K).map K.subtype := Subgroup.map_mono hcen
  · have hKM : K ⊓ M = K := by
      have h := congrArg (Subgroup.map K.subtype) htop
      rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left, Subgroup.map_top,
        Subgroup.range_subtype] at h
    exact inf_eq_left.mp hKM

theorem le_of_component_conj_ne {H K M T : Subgroup G} {e : G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (heH : e ∈ H) (he : e ^ 3 = 1)
    (hKe : K.map (MulAut.conj e).toMonoidHom ≠ K)
    (hCM : Subgroup.centralizer ({e} : Set G) ≤ M) (hTK : T ≤ K) (hTM : T ≤ M)
    (hTZ : ¬ T ≤ (Subgroup.center ↥K).map K.subtype) : K ≤ M := by
  classical
  set K1 : Subgroup G := K.map (MulAut.conj e).toMonoidHom with hK1
  set K2 : Subgroup G := K.map (MulAut.conj (e ^ 2)).toMonoidHom with hK2
  have he2H : e ^ 2 ∈ H := by rw [pow_two]; exact H.mul_mem heH heH
  have hK1c : CFSG.GorensteinWalter.IsComponentOf K1 H :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.isComponentOf_map_conj hK heH
  have hK2c : CFSG.GorensteinWalter.IsComponentOf K2 H :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.isComponentOf_map_conj hK he2H
  have hK1ne : K1 ≠ K := by rw [hK1]; exact hKe
  have hK2ne : K2 ≠ K := by rw [hK2]; exact map_conj_sq_ne he hKe
  exact le_of_normal_not_le_center hK.2.2
    (subgroupOf_inf_normal hK hK1c hK2c hK1ne hK2ne hK1 hK2 he hCM) hTK hTM hTZ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
