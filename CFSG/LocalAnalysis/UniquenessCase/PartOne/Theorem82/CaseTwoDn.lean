module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem card_Z_subgroupOf_Dn {N : Subgroup G} (hZN : t.Z ≤ N) :
    Nat.card (t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) = 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (t.Z_le_Dn hZN)).toEquiv, t.card_Z]

theorem inf_pPrimeCore_eq_bot_Dn {N : Subgroup G} (hZN : t.Z ≤ N) :
    (t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) ⊓
      CFSG.pPrimeCore 3 ↥(t.Dn N) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card ↥((t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) ⊓
      CFSG.pPrimeCore 3 ↥(t.Dn N))) 3 :=
    (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card).symm
  have hdvd : Nat.card ↥((t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) ⊓
      CFSG.pPrimeCore 3 ↥(t.Dn N)) ∣ 3 := by
    rw [← card_Z_subgroupOf_Dn t hZN]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

@[expose] noncomputable def DhatZ (t : CaseTwoTransitive c) (N : Subgroup G) :
    Subgroup (t.Dhat N) :=
  (t.Z.subgroupOf (t.Dn N)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N)))

theorem card_DhatZ {N : Subgroup G} (hZN : t.Z ≤ N) :
    Nat.card (DhatZ t N) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card (DhatZ t N) ∣ 3 := by
    have h := Subgroup.card_map_dvd (t.Z.subgroupOf (t.Dn N))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N)))
    rwa [card_Z_subgroupOf_Dn t hZN] at h
  rcases Nat.prime_three.eq_one_or_self_of_dvd (Nat.card (DhatZ t N)) hdvd with h | h
  · exfalso
    have hbot : DhatZ t N = ⊥ := Subgroup.card_eq_one.mp h
    have hle : t.Z.subgroupOf (t.Dn N) ≤ CFSG.pPrimeCore 3 ↥(t.Dn N) := by
      have hmap : Subgroup.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N)))
          (t.Z.subgroupOf (t.Dn N)) = ⊥ := hbot
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
      exact hmap
    have h1 : Nat.card (t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) = 1 := by
      have hle' : t.Z.subgroupOf (t.Dn N) ≤ ⊥ := by
        have h2 : t.Z.subgroupOf (t.Dn N) ≤
            (t.Z.subgroupOf (t.Dn N) ⊓ CFSG.pPrimeCore 3 ↥(t.Dn N)) := le_inf le_rfl hle
        rwa [inf_pPrimeCore_eq_bot_Dn t hZN] at h2
      exact Subgroup.card_eq_one.mpr (le_bot_iff.mp hle')
    rw [card_Z_subgroupOf_Dn t hZN] at h1
    norm_num at h1
  · exact h

theorem normal_inf_pCoreOf_subgroupOf {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal := by
  have hHnorm : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.openPCoreOf_le 2 H)).mp
      (by rw [CFSG.openPCoreOf_subgroupOf]
          exact CFSG.pCore_normal (p := 2) (G := ↥H))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro d hd
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hd, hHnorm (hDH hd)⟩

theorem inf_pCoreOf_le_pCoreOf_Dn {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    t.Dn N ⊓ CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 (t.Dn N) := by
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ inf_le_left
    (t.normal_inf_pCoreOf_subgroupOf hDH) ?_
  rw [CFSG.openPCoreOf_eq_map_pCore]
  exact ((CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype).to_le inf_le_right

theorem pCoreOf_Dn_le_On (N : Subgroup G) :
    CFSG.Open.pCoreOf 2 (t.Dn N) ≤ t.On N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.pCore 2 ↥(t.Dn N) ≤ CFSG.pPrimeCore 3 ↥(t.Dn N) := by
    refine CFSG.le_pPrimeCore_of_normal_coprime
      (CFSG.pCore_normal (p := 2) (G := ↥(t.Dn N))) ?_
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(t.Dn N))).exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow_right n
  rw [CFSG.openPCoreOf_eq_map_pCore]
  change (CFSG.pCore 2 ↥(t.Dn N)).map (t.Dn N).subtype ≤
    (CFSG.pPrimeCore 3 ↥(t.Dn N)).map (t.Dn N).subtype
  exact Subgroup.map_mono hle

theorem inf_pCoreOf_le_On {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    t.Dn N ⊓ CFSG.Open.pCoreOf 2 H ≤ t.On N :=
  (t.inf_pCoreOf_le_pCoreOf_Dn hDH).trans (t.pCoreOf_Dn_le_On N)

theorem subgroupOf_On_eq_pPrimeCore (N : Subgroup G) :
    (t.On N).subgroupOf (t.Dn N) = CFSG.pPrimeCore 3 ↥(t.Dn N) := by
  have h : t.On N = (CFSG.pPrimeCore 3 ↥(t.Dn N)).map (t.Dn N).subtype := rfl
  rw [h, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (t.Dn N).subtype_injective]

theorem subgroupOf_inf_pCoreOf_le_pPrimeCore {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N) ≤
      CFSG.pPrimeCore 3 ↥(t.Dn N) := by
  rw [← t.subgroupOf_On_eq_pPrimeCore N]
  exact Subgroup.subgroupOf_mono (t.Dn N) (t.inf_pCoreOf_le_On hDH)

theorem Dn_le_of_map_eq_top {N H : Subgroup G} (hHM : H ≤ c.S.M) (hO : t.On N ≤ c.S.M)
    (htop : (H.subgroupOf (t.Dn N)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))) = ⊤) :
    t.Dn N ≤ c.S.M := by
  intro d hd
  let π : ↥(t.Dn N) →* t.Dhat N := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))
  have hmem : π ⟨d, hd⟩ ∈ (H.subgroupOf (t.Dn N)).map π := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hπ⟩ := Subgroup.mem_map.mp hmem
  have hmM : (m : G) ∈ c.S.M := hHM (Subgroup.mem_subgroupOf.mp hm)
  have hker : (m⁻¹ * ⟨d, hd⟩ : ↥(t.Dn N)) ∈ CFSG.pPrimeCore 3 ↥(t.Dn N) := by
    refine (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥(t.Dn N))
      (m⁻¹ * ⟨d, hd⟩)).mp ?_
    change π (m⁻¹ * ⟨d, hd⟩) = 1
    rw [map_mul, map_inv, hπ]
    simp
  have hOn : ((m⁻¹ * ⟨d, hd⟩ : ↥(t.Dn N)) : G) ∈ t.On N :=
    Subgroup.mem_map.mpr ⟨_, hker, rfl⟩
  have hxeq : d = (m : G) * ((m⁻¹ * ⟨d, hd⟩ : ↥(t.Dn N)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hxeq]
  exact c.S.M.mul_mem hmM (hO hOn)

theorem exists_conj_eq_Z {N : Subgroup G} (hZN : t.Z ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) {W : Subgroup G} (hWD : W ≤ t.Dn N)
    (hW : Nat.card W = 3) : ∃ d ∈ t.Dn N, W.map (MulAut.conj d).toMonoidHom = t.Z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZD : t.Z ≤ t.Dn N := t.Z_le_Dn hZN
  have hDrank : CFSG.pRank 3 ↥(t.Dn N) = 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hrank
  have hWcard : Nat.card (W.subgroupOf (t.Dn N)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWD).toEquiv, hW]
  have hWp : IsPGroup 3 ↥(W.subgroupOf (t.Dn N)) :=
    IsPGroup.of_card (n := 1) (by rw [hWcard]; norm_num)
  obtain ⟨Q, hWQ⟩ := hWp.exists_le_sylow
  have hQcyc : IsCyclic ↥Q := by
    refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) Q.isPGroup' ?_
    have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num)
      (Q : Subgroup ↥(t.Dn N)).subtype (Q : Subgroup ↥(t.Dn N)).subtype_injective
      (⊤ : Subgroup ↥Q)
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    calc CFSG.pRank 3 ↥Q
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥Q) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥Q
      _ ≤ CFSG.Open.pRank 3 (Q : Subgroup ↥(t.Dn N)) := h1
      _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(t.Dn N)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = CFSG.pRank 3 ↥(t.Dn N) :=
          (CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(t.Dn N)).symm
      _ = 1 := hDrank
  have hZ'card : Nat.card (t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) = 3 :=
    card_Z_subgroupOf_Dn t hZN
  have hZp : IsPGroup 3 ↥(t.Z.subgroupOf (t.Dn N)) :=
    IsPGroup.of_card (n := 1) (by rw [hZ'card]; norm_num)
  obtain ⟨QZ, hZQZ⟩ := hZp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(t.Dn N) QZ Q
  have hZgQ : (t.Z.subgroupOf (t.Dn N)).map (MulAut.conj g).toMonoidHom ≤ Q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : (MulAut.conj g) x ∈ ((g • QZ : Sylow 3 ↥(t.Dn N)) : Subgroup ↥(t.Dn N)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (QZ : Subgroup ↥(t.Dn N))
        (hZQZ hx)
    rwa [hg] at hmem
  have hcapW : Nat.card ↥((W.subgroupOf (t.Dn N)).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv, hWcard]
  have hcapZ : Nat.card ↥(((t.Z.subgroupOf (t.Dn N)).map
      (MulAut.conj g).toMonoidHom).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZgQ).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ'card]
  have heq : (W.subgroupOf (t.Dn N)).subgroupOf Q =
      ((t.Z.subgroupOf (t.Dn N)).map (MulAut.conj g).toMonoidHom).subgroupOf Q :=
    (IsCyclic.subgroup_eq_iff_card_eq (G := ↥Q)).mpr (hcapW.trans hcapZ.symm)
  have heq' : W.subgroupOf (t.Dn N) =
      (t.Z.subgroupOf (t.Dn N)).map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (Q : Subgroup ↥(t.Dn N)).subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hWQ, Subgroup.map_subgroupOf_eq_of_le hZgQ] at h1
  have hW_eq : W = t.Z.map (MulAut.conj (g : G)).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (Subgroup.subtype (t.Dn N))) heq'
    rw [Subgroup.map_subgroupOf_eq_of_le hWD, Subgroup.map_map] at h1
    have hcomp : (Subgroup.subtype (t.Dn N)).comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp (Subgroup.subtype (t.Dn N)) := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hZD] at h1
    exact h1
  refine ⟨((g : G))⁻¹, (t.Dn N).inv_mem g.2, ?_⟩
  rw [hW_eq, Subgroup.map_map]
  have hcomp : (MulAut.conj ((g : G))⁻¹).toMonoidHom.comp
      (MulAut.conj (g : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    change (MulAut.conj ((g : G))⁻¹) ((MulAut.conj (g : G)) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

theorem Ky_le_Dn (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N : Subgroup G}
    (hKN : t.Ky ≤ N) : t.Ky ≤ t.Dn N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : IsPGroup 2 t.d.N := SylowThreeData.N_isPGroup t.d
  have hZKy : t.Z ≤ t.Ky := t.Z_le_Ky
  have hZD : t.Z ≤ t.Dn N := t.Z_le_Dn (hZKy.trans hKN)
  have hnorm : t.Ky ≤ Subgroup.normalizer
      ((t.Ky ⊓ t.Dn N : Subgroup G) : Set G) := by
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.Ky) (K := t.Dn N)
      ⟨Subgroup.le_normalizer hk, (t.le_normalizer_Dn N) (hKN hk)⟩
  rcases t.le_N_or_eq_Ky hK32 hGA hSp inf_le_left hnorm with hle | heq
  · exfalso
    have hZle : t.Z ≤ t.Ky ⊓ t.Dn N := le_inf hZKy hZD
    have hZ2 : IsPGroup 2 ↥t.Z := hN2.to_le (hZle.trans hle)
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    rw [t.card_Z] at hn
    rcases n with _ | m
    · norm_num at hn
    · have hdvd : 2 ∣ 3 := by
        rw [hn]
        exact dvd_pow_self 2 (Nat.succ_ne_zero m)
      norm_num at hdvd
  · rw [← heq]
    exact inf_le_right

theorem commutator_Dn (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N : Subgroup G}
    (hKN : t.Ky ≤ N) : ⁅t.Dn N, t.Dn N⁆ = t.Dn N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKyD : t.Ky ≤ t.Dn N := t.Ky_le_Dn hK32 hGA hSp hKN
  have hZKy : t.Z ≤ t.Ky := t.Z_le_Ky
  have hCD : ⁅t.Dn N, t.Dn N⁆ ≤ t.Dn N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact (t.Dn N).mul_mem ((t.Dn N).mul_mem ((t.Dn N).mul_mem hx hy)
      ((t.Dn N).inv_mem hx)) ((t.Dn N).inv_mem hy)
  have hnormD : Subgroup.normalizer (t.Dn N : Set G) ≤
      Subgroup.normalizer (((⁅t.Dn N, t.Dn N⁆ : Subgroup G)) : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := t.Dn N) (_root_.commutator ↥(t.Dn N))
    rwa [Subgroup.map_subtype_commutator] at h
  have hCnorm : N ≤ Subgroup.normalizer (((⁅t.Dn N, t.Dn N⁆ : Subgroup G)) : Set G) :=
    (t.le_normalizer_Dn N).trans hnormD
  have hCleN : ⁅t.Dn N, t.Dn N⁆ ≤ N := hCD.trans (t.Dn_le N)
  have hZleC : t.Z ≤ ⁅t.Dn N, t.Dn N⁆ := by
    calc t.Z ≤ t.Ky := hZKy
      _ = ⁅t.Ky, t.Ky⁆ := t.commutator_Ky.symm
      _ ≤ ⁅t.Dn N, t.Dn N⁆ := Subgroup.commutator_mono hKyD hKyD
  have hZsub : t.Z.subgroupOf N ≤ (⁅t.Dn N, t.Dn N⁆).subgroupOf N := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hZleC (Subgroup.mem_subgroupOf.mp hz))
  haveI hnormal : ((⁅t.Dn N, t.Dn N⁆).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCleN).mpr hCnorm
  have hnc : Subgroup.normalClosure ((t.Z.subgroupOf N : Subgroup ↥N) : Set ↥N) ≤
      (⁅t.Dn N, t.Dn N⁆).subgroupOf N := Subgroup.normalClosure_le_normal hZsub
  have hDleC : t.Dn N ≤ ⁅t.Dn N, t.Dn N⁆ := by
    have h := Subgroup.map_mono (f := N.subtype) hnc
    rw [Subgroup.map_subgroupOf_eq_of_le hCleN,
      show (Subgroup.normalClosure ((t.Z.subgroupOf N : Subgroup ↥N) : Set ↥N)).map
        N.subtype = t.Dn N from rfl] at h
    exact h
  exact le_antisymm hCD hDleC

theorem pRank_Dhat_eq_one {N : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) : CFSG.pRank 3 (t.Dhat N) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(t.Dn N)) := by
    intro h
    have h1 : 3 = 1 := Nat.Coprime.eq_one_of_dvd CFSG.pPrimeCore_coprime_card h
    norm_num at h1
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _ hO,
    CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact hrank

private theorem pRank_Dhat_top_eq_one {N : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (t.Dhat N)) = 1 := by
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (t.Dhat N))
      = CFSG.pRank 3 (t.Dhat N) :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (t.Dhat N)).symm
    _ = 1 := pRank_Dhat_eq_one t hrank

theorem isCyclic_of_isPGroup_Dhat {N : Subgroup G} (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    {P : Subgroup (t.Dhat N)} (hP : IsPGroup 3 P) : IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPrank : CFSG.pRank 3 ↥P ≤ 1 := by
    have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num)
      P.subtype P.subtype_injective (⊤ : Subgroup ↥P)
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    calc CFSG.pRank 3 ↥P
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥P) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥P
      _ ≤ CFSG.Open.pRank 3 (P : Subgroup (t.Dhat N)) := h1
      _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (t.Dhat N)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = CFSG.pRank 3 (t.Dhat N) :=
          (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (t.Dhat N)).symm
      _ = 1 := pRank_Dhat_eq_one t hrank
  exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) hP hPrank

private theorem normalClosure_Z_subgroupOf_Dn {N : Subgroup G} (hZN : t.Z ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) :
    Subgroup.normalClosure ((t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) :
      Set ↥(t.Dn N)) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZD : t.Z ≤ t.Dn N := t.Z_le_Dn hZN
  let N₀ : Subgroup ↥(t.Dn N) :=
    Subgroup.normalClosure (t.Z.subgroupOf (t.Dn N) : Set ↥(t.Dn N))
  let N₁ : Subgroup G := N₀.map (t.Dn N).subtype
  have hNnorm : N₀.Normal := Subgroup.normalClosure_normal
  have hZle : t.Z ≤ N₁ := by
    have h1 : (t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)).map
        (t.Dn N).subtype ≤ N₁ := Subgroup.map_mono Subgroup.le_normalClosure
    rwa [Subgroup.map_subgroupOf_eq_of_le hZD] at h1
  have hN₁conj : ∀ x ∈ t.Dn N, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁ := by
    intro x hx n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    exact Subgroup.mem_map_of_mem _ (hNnorm.conj_mem m hm ⟨x, hx⟩)
  have hDeq : t.Dn N = (Subgroup.normalClosure (t.Z.subgroupOf N : Set ↥N)).map N.subtype :=
    rfl
  have hDle : t.Dn N ≤ N₁ := by
    intro g hg
    have hg' : g ∈ (Subgroup.normalClosure (t.Z.subgroupOf N : Set ↥N)).map N.subtype := by
      rwa [hDeq] at hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg'
    change k ∈ Subgroup.closure (Group.conjugatesOfSet (t.Z.subgroupOf N : Set ↥N)) at hk
    refine Subgroup.closure_induction (G := ↥N) (p := fun w _ => (w : G) ∈ N₁) ?_ ?_ ?_ ?_ hk
    · intro w hw
      obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hw
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hzZ : (z : G) ∈ t.Z := Subgroup.mem_subgroupOf.mp hz
      have hWD : t.Z.map (MulAut.conj (u : G)).toMonoidHom ≤ t.Dn N := by
        intro y hy
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
        have hnorm : (u : G) ∈ Subgroup.normalizer (t.Dn N : Set G) :=
          t.le_normalizer_Dn N u.2
        exact (Subgroup.mem_normalizer_iff.mp hnorm c).mp (t.Z_le_Dn hZN hc)
      have hWcard : Nat.card (t.Z.map (MulAut.conj (u : G)).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective, t.card_Z]
      obtain ⟨d, hdD, hdW⟩ :=
        t.exists_conj_eq_Z hZN hrank hWD hWcard
      have hwW : (w : G) ∈ t.Z.map (MulAut.conj (u : G)).toMonoidHom := by
        rw [← hu]
        exact Subgroup.mem_map_of_mem _ hzZ
      have hdw : d * (w : G) * d⁻¹ ∈ t.Z := by
        have hmem : d * (w : G) * d⁻¹ ∈
            (t.Z.map (MulAut.conj (u : G)).toMonoidHom).map
              (MulAut.conj d).toMonoidHom := Subgroup.mem_map_of_mem _ hwW
        rwa [hdW] at hmem
      have h1 : d⁻¹ * (d * (w : G) * d⁻¹) * d ∈ N₁ := by
        simpa using hN₁conj d⁻¹ ((t.Dn N).inv_mem hdD) _ (hZle hdw)
      have h2 : d⁻¹ * (d * (w : G) * d⁻¹) * d = (w : G) := by group
      rwa [h2] at h1
    · exact N₁.one_mem
    · intro a b _ _ ha hb
      exact N₁.mul_mem ha hb
    · intro a _ ha
      exact N₁.inv_mem ha
  have hN₁le : N₁ ≤ t.Dn N := Subgroup.map_subtype_le N₀
  have hNeq : N₀ = ⊤ := by
    apply Subgroup.map_injective (t.Dn N).subtype_injective
    show N₀.map (t.Dn N).subtype = (⊤ : Subgroup ↥(t.Dn N)).map (t.Dn N).subtype
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact le_antisymm hN₁le hDle
  exact hNeq

private theorem normalClosure_DhatZ_eq_top {N : Subgroup G} (hZN : t.Z ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) :
    Subgroup.normalClosure ((DhatZ t N : Subgroup (t.Dhat N)) : Set (t.Dhat N)) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))) :=
    QuotientGroup.mk'_surjective _
  have hset : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))) ''
      (t.Z.subgroupOf (t.Dn N) : Set ↥(t.Dn N)) = (DhatZ t N : Set (t.Dhat N)) := by
    rw [DhatZ, Subgroup.coe_map]
  calc Subgroup.normalClosure ((DhatZ t N : Subgroup (t.Dhat N)) : Set (t.Dhat N))
      = Subgroup.normalClosure ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))) ''
          (t.Z.subgroupOf (t.Dn N) : Set ↥(t.Dn N))) := by rw [hset]
    _ = (Subgroup.normalClosure ((t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) :
          Set ↥(t.Dn N))).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))) :=
        (Subgroup.map_normalClosure _ _ hsurj).symm
    _ = ⊤ := by
        rw [normalClosure_Z_subgroupOf_Dn t hZN hrank, Subgroup.map_top,
          MonoidHom.range_eq_top.mpr hsurj]

private theorem exists_conj_map_eq_DhatZ {N : Subgroup G} (hZN : t.Z ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) {W : Subgroup (t.Dhat N)}
    (hW : Nat.card W = 3) : ∃ k : t.Dhat N, W.map (MulAut.conj k).toMonoidHom = DhatZ t N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWp : IsPGroup 3 ↥W := IsPGroup.of_card (n := 1) (by rw [hW]; norm_num)
  obtain ⟨Q, hWQ⟩ := hWp.exists_le_sylow
  have hQcyc : IsCyclic ↥Q := t.isCyclic_of_isPGroup_Dhat hrank Q.isPGroup'
  have hZp : IsPGroup 3 ↥(DhatZ t N) :=
    IsPGroup.of_card (n := 1) (by rw [card_DhatZ t hZN]; norm_num)
  obtain ⟨QZ, hZQZ⟩ := hZp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (t.Dhat N) QZ Q
  have hZkQ : (DhatZ t N).map (MulAut.conj k).toMonoidHom ≤ Q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : (MulAut.conj k) x ∈
        ((k • QZ : Sylow 3 (t.Dhat N)) : Subgroup (t.Dhat N)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj k) (QZ : Subgroup (t.Dhat N))
        (hZQZ hx)
    rwa [hk] at hmem
  have hWQ' : W ≤ Q := hWQ
  have hcapW : Nat.card ↥(W.subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ').toEquiv, hW]
  have hcapZ : Nat.card ↥(((DhatZ t N).map (MulAut.conj k).toMonoidHom).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZkQ).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj k).injective, card_DhatZ t hZN]
  have heq : W.subgroupOf Q = ((DhatZ t N).map (MulAut.conj k).toMonoidHom).subgroupOf Q :=
    (IsCyclic.subgroup_eq_iff_card_eq (G := ↥Q)).mpr (hcapW.trans hcapZ.symm)
  have heq' : W = (DhatZ t N).map (MulAut.conj k).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (Q : Subgroup (t.Dhat N)).subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hWQ', Subgroup.map_subgroupOf_eq_of_le hZkQ] at h1
  refine ⟨k⁻¹, ?_⟩
  rw [heq', Subgroup.map_map]
  have hcomp : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      MonoidHom.id (t.Dhat N) := by
    ext x
    change (MulAut.conj k⁻¹) ((MulAut.conj k) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

theorem isSimpleGroup_Dhat {N : Subgroup G} (hZN : t.Z ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) : IsSimpleGroup (t.Dhat N) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : Subgroup.normalClosure ((DhatZ t N : Subgroup (t.Dhat N)) :
      Set (t.Dhat N)) = ⊤ := normalClosure_DhatZ_eq_top t hZN hrank
  have hnt : Nontrivial (t.Dhat N) := by
    have hne : DhatZ t N ≠ ⊥ := by
      intro hb
      have h1 : Nat.card (DhatZ t N) = 1 := by rw [hb, Subgroup.card_bot]
      rw [card_DhatZ t hZN] at h1
      norm_num at h1
    haveI : Nontrivial ↥(DhatZ t N) := (Subgroup.nontrivial_iff_ne_bot (DhatZ t N)).mpr hne
    obtain ⟨a, b, hab⟩ := ‹Nontrivial ↥(DhatZ t N)›
    exact ⟨(a : t.Dhat N), (b : t.Dhat N), fun h => hab (Subtype.ext h)⟩
  refine (isSimpleGroup_iff (t.Dhat N)).mpr ⟨hnt, fun M hM => ?_⟩
  by_cases h3 : 3 ∣ Nat.card M
  · right
    obtain ⟨w, hwN, hword⟩ : ∃ w : t.Dhat N, w ∈ M ∧ orderOf w = 3 := by
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 3 h3
      exact ⟨(w : t.Dhat N), w.2, by rwa [← Subgroup.orderOf_mk (w : t.Dhat N) w.2]⟩
    have hWcard : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hword]
    have hWN : Subgroup.zpowers w ≤ M := Subgroup.zpowers_le.mpr hwN
    obtain ⟨k, hk⟩ := exists_conj_map_eq_DhatZ t hZN hrank hWcard
    have hZle : DhatZ t N ≤ M := by
      rw [← hk]
      calc (Subgroup.zpowers w).map (MulAut.conj k).toMonoidHom
          ≤ M.map (MulAut.conj k).toMonoidHom := Subgroup.map_mono hWN
        _ = M := Subgroup.normal_iff_map_conj_eq.mp hM k
    have hle : Subgroup.normalClosure ((DhatZ t N : Subgroup (t.Dhat N)) :
        Set (t.Dhat N)) ≤ M :=
      (Subgroup.normalClosure_subset_iff (N := M)).mp hZle
    rw [htop] at hle
    exact top_le_iff.mp hle
  · left
    have hcop : Nat.Coprime 3 (Nat.card M) := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have hle : M ≤ CFSG.pPrimeCore 3 (t.Dhat N) := CFSG.le_pPrimeCore_of_normal_coprime hM hcop
    have hbot : CFSG.pPrimeCore 3 (t.Dhat N) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    rw [hbot] at hle
    exact le_bot_iff.mp hle

theorem exists_mul_ne_mul_Dhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N : Subgroup G}
    (hKN : t.Ky ≤ N) : ∃ a b : t.Dhat N, a * b ≠ b * a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  by_contra h
  push Not at h
  haveI hcomm : IsMulCommutative (t.Dhat N) := isMulCommutative_iff.mpr fun a b => h a b
  have hKyD : t.Ky ≤ t.Dn N := t.Ky_le_Dn hK32 hGA hSp hKN
  have hquot : ⁅(⊤ : Subgroup ↥(t.Dn N)), ⊤⁆ ≤ CFSG.pPrimeCore 3 ↥(t.Dn N) := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have hmem : ⁅g₁, g₂⁆ ∈ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact isMulCommutative_iff.mp hcomm _ _
    rwa [QuotientGroup.ker_mk'] at hmem
  have hcommle : ⁅t.Dn N, t.Dn N⁆ ≤ t.On N := by
    show ⁅t.Dn N, t.Dn N⁆ ≤ Subgroup.map (t.Dn N).subtype (CFSG.pPrimeCore 3 ↥(t.Dn N))
    have h2 := Subgroup.map_mono (f := (t.Dn N).subtype) hquot
    rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  have hKyle : t.Ky ≤ ⁅t.Dn N, t.Dn N⁆ := by
    rw [← t.commutator_Ky]
    exact Subgroup.commutator_mono hKyD hKyD
  have hZleOn : t.Z ≤ t.On N :=
    t.Z_le_Ky.trans (hKyle.trans hcommle)
  have hZ'leO : t.Z.subgroupOf (t.Dn N) ≤ CFSG.pPrimeCore 3 ↥(t.Dn N) := by
    intro z hz
    obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp (hZleOn (Subgroup.mem_subgroupOf.mp hz))
    have hzo : z = o := Subtype.ext hoeq.symm
    rwa [hzo]
  have hbot : t.Z.subgroupOf (t.Dn N) = ⊥ := by
    refine le_bot_iff.mp ?_
    have h2 : t.Z.subgroupOf (t.Dn N) ≤
        (t.Z.subgroupOf (t.Dn N) ⊓ CFSG.pPrimeCore 3 ↥(t.Dn N)) := le_inf le_rfl hZ'leO
    rwa [inf_pPrimeCore_eq_bot_Dn t hZN] at h2
  have h1 : Nat.card (t.Z.subgroupOf (t.Dn N) : Subgroup ↥(t.Dn N)) = 1 := by
    rw [hbot, Subgroup.card_bot]
  rw [card_Z_subgroupOf_Dn t hZN] at h1
  norm_num at h1

theorem isKGroup_Dhat {N : Subgroup G} (hN : N ≠ ⊤) : CFSG.Open.IsKGroup (t.Dhat N) := by
  haveI hOnormal : (CFSG.pPrimeCore 3 ↥(t.Dn N)).Normal := CFSG.pPrimeCore_normal
  have hDne : t.Dn N ≠ ⊤ := by
    intro htop
    exact hN (top_le_iff.mp (htop ▸ t.Dn_le N))
  exact (c.standing.kProper.isKGroup (t.Dn N) hDne).quotient
    (CFSG.pPrimeCore 3 ↥(t.Dn N))

theorem Dhat_cases (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N : Subgroup G}
    (hN : N ≠ ⊤) (hKN : t.Ky ≤ N) (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) :
    (∃ ℓ f : ℕ, CFSG.Blueprint.LieModel (t.Dhat N) .PSL 2 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel (t.Dhat N) .PSL 3 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel (t.Dhat N) .PSU 3 ℓ f) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor (t.Dhat N) .J1 :=
  hK32 (t.Dhat N) (t.isKGroup_Dhat (N := N) hN)
    (t.isSimpleGroup_Dhat (N := N) (t.Z_le_Ky.trans hKN) hrank)
    (t.exists_mul_ne_mul_Dhat (N := N) hK32 hGA hSp hKN)
    (pRank_Dhat_top_eq_one (N := N) t hrank)

theorem not_Dn_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {N : Subgroup G} (hZN : t.Z ≤ N)
    (hNM : ¬ N ≤ c.S.M) (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) : ¬ t.Dn N ≤ c.S.M := by
  classical
  intro hDM
  apply hNM
  intro n hn
  have hWD : t.Z.map (MulAut.conj n).toMonoidHom ≤ t.Dn N := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    have hnorm : n ∈ Subgroup.normalizer (t.Dn N : Set G) := t.le_normalizer_Dn N hn
    exact (Subgroup.mem_normalizer_iff.mp hnorm c).mp (t.Z_le_Dn hZN hc)
  have hWcard : Nat.card (t.Z.map (MulAut.conj n).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, t.card_Z]
  obtain ⟨d, hdD, hdW⟩ := t.exists_conj_eq_Z hZN hrank hWD hWcard
  have hmap : t.Z.map (MulAut.conj (d * n)).toMonoidHom = t.Z := by
    have hcomp : (MulAut.conj (d * n)).toMonoidHom =
        (MulAut.conj d).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map, hdW]
  have hdn : d * n ∈ Subgroup.normalizer (t.Z : Set G) := by
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hnM : n ∈ c.S.M := by
    have h1 : d⁻¹ ∈ c.S.M := hDM ((t.Dn N).inv_mem hdD)
    have h2 : d * n ∈ c.S.M := t.normalizer_Z_le hp hN hZ hdn
    have h3 : n = d⁻¹ * (d * n) := by group
    rw [h3]
    exact c.S.M.mul_mem h1 h2
  exact hnM

theorem pCoreOf_Dn_ne_bot {N : Subgroup G} (hN : CFSG.Open.IsTwoLocal N) (hZN : t.Z ≤ N) :
    CFSG.Open.pCoreOf 2 (t.Dn N) ≠ ⊥ := by
  classical
  intro hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZD : t.Z ≤ t.Dn N := t.Z_le_Dn hZN
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 N
  have hQle : t.Dn N ⊓ Q ≤ CFSG.Open.pCoreOf 2 (t.Dn N) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ ?_
    · refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
      refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      exact (t.Dn_le N).trans
        (CFSG.LocalAnalysis.UniquenessCase.UC6.le_normalizer_pCoreOf 2 N)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_right
  rw [hbot] at hQle
  have hinf : t.Dn N ⊓ Q = ⊥ := le_bot_iff.mp hQle
  have hDNQ : t.Dn N ≤ Subgroup.normalizer (Q : Set G) :=
    (t.Dn_le N).trans (CFSG.LocalAnalysis.UniquenessCase.UC6.le_normalizer_pCoreOf 2 N)
  have hQN : Q ≤ Subgroup.normalizer (t.Dn N : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans (t.le_normalizer_Dn N)
  have hcommQ : ⁅Q, t.Dn N⁆ ≤ Q :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := t.Dn N) (K := Q)).mp hDNQ
  have hcommD : ⁅Q, t.Dn N⁆ ≤ t.Dn N :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := Q) (K := t.Dn N)).mp hQN
  have hcomm : ⁅t.Dn N, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.mp (hinf ▸ le_inf hcommD hcommQ)
  have hDleC : t.Dn N ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hDleQ : t.Dn N ≤ Q :=
    (le_inf (t.Dn_le N) hDleC).trans (c.standing.charTwo N hN)
  have hZQ : t.Z ≤ Q := hZD.trans hDleQ
  have hZ2 : IsPGroup 2 ↥t.Z :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le hZQ
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  rw [t.card_Z] at hk
  rcases k with _ | m
  · norm_num at hk
  · have hdvd : 2 ∣ 3 := by
      rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero m)
    norm_num at hdvd

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
