module

public import CFSG.Quasithin.H13.A6S1372L74e
public import CFSG.Quasithin.H13.A6S1372L76W
public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.A6S1372L76A
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

theorem isSimpleGroup_of_a5_or_l32 {G : Type} [Group G] {K : Subgroup G}
    (h : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) :
    IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := A6L76A.isSimpleGroup_alt (by norm_num)
    exact e.isSimpleGroup
  · exact (LieType.Simplicity.fam_PSL_simplicity _ 3 2 1
      (statedClassicalModel_of_lieModel_psl32 h)).2

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Setting

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz)
include hNS h13315 h1356two hH

theorem isFaithfulLocal_of_cComp
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    quasithinIsFaithfulLocal T K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ : Subgroup G := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)
    with hU₀def
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hU₀Q : U₀ ≤ pCoreOf 2 H :=
    inf_le_left.trans hF.conjClosure_Vp_le_pCoreOf
  have hU₀N : U₀ ≤ Subgroup.normalizer (K : Set G) := fun u hu =>
    P134.pCoreOf_le_normalizer_of_mem_cComp hKc (hU₀Q hu)
  have hKN : K ≤ Subgroup.normalizer (U₀ : Set G) :=
    (le_of_mem_cComp hKc).trans S.le_normalizer_U0
  have hc1 : ⁅U₀, K⁆ ≤ K := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hU₀N
  have hc2 : ⁅U₀, K⁆ ≤ U₀ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hKN
  have hp : IsPGroup 2 ↥(⁅U₀, K⁆) := (pCoreOf_isPGroup 2 H).to_le (hc2.trans hU₀Q)
  have hcO : ⁅U₀, K⁆ ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 hc1 (fun k hk =>
      SBd5.mem_normalizer_commutator_of (hKN hk) (Subgroup.le_normalizer hk)) hp
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hΩ : ⁅U₀, K⁆ ≤ omegaOneCenterOf (pCoreOf 2 K) := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hcO hx, ?_⟩, ?_⟩
    · intro y hy
      exact (hc2 hx).2 y (hOK hy)
    · exact hab.2 x (hc2 hx).1
  have hU₀ab : ∀ x ∈ U₀, ∀ y ∈ U₀, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hcc : ⁅⁅U₀, K⁆, K⁆ = ⁅U₀, K⁆ :=
    SBd5.commutator_commutator_eq_self hperf hKN hU₀ab
  have hne : ⁅U₀, K⁆ ≠ ⊥ := by
    intro h
    apply hKU
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact Subgroup.le_centralizer_iff.mp h
  have hVY : VY K ≠ ⊥ := by
    intro h
    apply hne
    rw [← hcc, eq_bot_iff, ← h]
    exact Subgroup.commutator_mono hΩ le_rfl
  have hXC : IsXClass K := ⟨ne_bot_of_mem_cComp hKc, eq_oTwoUpper_of_perfect hperf,
    A4.charTwo_of_subnormal (subnormal_of_mem_cComp hKc) hF.charTwo_H⟩
  have hloc := isLocal_of_mem_cComp_of_sylow
    (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH) hH.1.2 hKc
  exact isFaithfulLocal_iff_isXf.mpr ⟨hloc, hXC, hVY⟩

omit hNS h13315 h1356two in
theorem le_normalizer_of_T_le (h37 : A37ForSQTK) (h38 : A38ForSQTK) {K : Subgroup G}
    (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have h := normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
    hH.1.2 (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH) hKc
  have he : conjClosure K T = K := le_antisymm
    (conjClosure_le fun t ht k hk => (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
    (le_conjClosure K T)
  rwa [he] at h

omit hNS h13315 h1356two hH in
theorem inf_centralizer_U0_le_of_simple {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ : Subgroup G := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)
    with hU₀def
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hQU : pCoreOf 2 H ≤ Subgroup.centralizer (U₀ : Set G) := fun q hq => by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp hu.2 q hq).symm
  have hKN : K ≤ Subgroup.normalizer (U₀ : Set G) := hKH.trans S.le_normalizer_U0
  set N : Subgroup ↥K := (K ⊓ Subgroup.centralizer (U₀ : Set G)).subgroupOf K with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
    exact InternalSec.le_normalizer_centralizer hKN g.2 |> fun h =>
      (Subgroup.mem_normalizer_iff.mp h _).mp hn.2
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have := hs
  have := hNn.map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro x hx
    have h1 : π ⟨x, hx.1⟩ ∈ N.map π := ⟨⟨x, hx.1⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (A6L74.mem_pCoreOf_iff (H := K) ⟨x, hx.1⟩).2 h1
  · exfalso
    apply hKU
    intro k hk
    have h1 : π ⟨k, hk⟩ ∈ N.map π := h ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := h1
    have h2 : n⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K), QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      have : (n : ↥K ⧸ CFSG.pCore 2 ↥K) = (⟨k, hk⟩ : ↥K) := hnk
      rw [this, inv_mul_cancel]
    have h3 := hQU (hOQ ((A6L74.mem_pCoreOf_iff (H := K) _).2 h2))
    have hn' : (n : G) ∈ Subgroup.centralizer (U₀ : Set G) := hn.2
    have e : k = (n : G) * ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ hn' h3

theorem L1_le_of_hat (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (hhat : ¬ IsHatA6 L) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hP : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3)
    (hE : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      alternatingGroup (Fin 6))) : S.L1 ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have hSQ' := SQTKHyp.of_sqtkGroup ↥H hSQ
  have hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    obtain ⟨e⟩ := hE
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := A6L76A.isSimpleGroup_alt (by norm_num)
    have ha : swap (0 : Fin 6) 1 * swap 1 2 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      rfl
    have hb : swap (1 : Fin 6) 2 * swap 2 3 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      rfl
    refine ⟨hP, e.isSimpleGroup, e.symm ⟨_, ha⟩, e.symm ⟨_, hb⟩, fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (e.symm.injective h)
    simp only [Subgroup.coe_mul] at h'
    exact absurd h' (by decide)
  have hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 6)) := ⟨hQ, hZ, hE⟩
  have hLc := subgroupOf_mem_cComp hKc
  obtain ⟨e₀⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.quotPCore_subgroupOf_equiv (L := K) hKH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr : 1 < CFSG.Open.pRank 3 (K.subgroupOf H) := by
    rw [CFSG.Quasithin.Vol2.Ch11.SecA.pRank_subgroupOf_eq (L := K) hKH Nat.prime_three
      (by norm_num)]
    have := (FFC.threeRank2_hat hHat).pRank_two_le
    omega
  have hconc := a318 hF hSQ (h36 _ hSQ') (h38 _ hSQ') hLc hQ' Nat.prime_three (by norm_num) hr
  have hLmap : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set ρ : ↥K →* PStar 3 ↥H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).comp (Subgroup.inclusion hKH) with hρ
  have hρrange : ρ.range = starImage 3 (K.subgroupOf H) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKH k, k.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hO2 : CFSG.pCore 2 ↥K ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have hxO : (x : G) ∈ pCoreOf 2 K := (A6L74.mem_pCoreOf_iff (H := K) x).2 hx
    set O : Subgroup ↥H := (pCoreOf 2 K).subgroupOf H with hOdef
    have hOn : O.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((pCoreOf_le 2 K).trans hKH)).mpr (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K))
    have hO3 : Nat.Coprime 3 (Nat.card O) := by
      have h2 : IsPGroup 2 O := ((pCoreOf_isPGroup 2 K).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 K).trans hKH)).symm)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    have hle : O ≤ CFSG.pPrimeCore 3 ↥H := le_sSup ⟨hOn, hO3⟩
    exact hle hxO
  set ψ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(starImage 3 (K.subgroupOf H)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) ((MonoidHom.codRestrict ρ _ fun k => by
      rw [← hρrange]; exact ⟨k, rfl⟩)) (fun x hx => by
        apply Subtype.ext
        exact (MonoidHom.mem_ker.mp (hO2 hx))) with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hρrange] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨(k : ↥K ⧸ CFSG.pCore 2 ↥K), rfl⟩
  have hnt : ¬ Subsingleton ↥(starImage 3 (K.subgroupOf H)) := by
    intro hsub
    have h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [R3c2.card_of_isHat_alt6 hHat]
      norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K ⧸ CFSG.pCore 2 ↥K) 3 h3
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) g
    have hk1 : ψ (QuotientGroup.mk' _ k) = 1 := Subsingleton.elim _ _
    have hρk : ρ k = 1 := congrArg Subtype.val hk1
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hρk
    have hcop := (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
    have hord : orderOf (⟨Subgroup.inclusion hKH k, hρk⟩ : ↥(CFSG.pPrimeCore 3 ↥H)) ∣
        Nat.card ↥(CFSG.pPrimeCore 3 ↥H) := orderOf_dvd_natCard _
    have h3k : 3 ∣ orderOf k := by
      have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) k
      rw [hg] at h1
      exact h1
    have h3' : 3 ∣ orderOf (⟨Subgroup.inclusion hKH k, hρk⟩ : ↥(CFSG.pPrimeCore 3 ↥H)) := by
      rw [Subgroup.orderOf_mk, orderOf_injective _ (Subgroup.inclusion_injective hKH) k]
      exact h3k
    exact absurd (Nat.Coprime.coprime_dvd_right (h3'.trans hord) hcop) (by norm_num)
  have hcard := R3c2.card_quotient_hat hHat ψ hψs hnt
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · have h1' : K = oPrimeResidualOf 3 H := by
      rw [← CFSG.Quasithin.Vol2.Ch11.SecA.map_oPrimeResidualOf_top, ← h1, hLmap]
    rw [h1']
    exact S.L1_le_oPrimeResidualOf hH
  · exfalso
    obtain ⟨s, q, hmod, hPSL, -⟩ := h2
    exact R3c2.not_case2_of_card_hat6 hcard s q hmod hPSL
  · rcases h3 with h | h
    · have hK : K = thetaOf H := by rw [← hLmap, h, R3c2.map_thetaOf_top]
      rw [hK]
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨⟨hxL, hxN⟩, m, hm, hxm⟩
      have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨⟨hxL, hxN⟩, m, hm, hxm⟩
      have hx3 : x ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, S.cube_mem_pCoreOf_L1 hhat hxL1⟩
        have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
        rw [← orderOf_eq_one_iff]
        exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
          (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk')
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨S.L1_le_of_mem_Hz hNS h13315 h1356two hH hxL1,
          orderOf_eq_prime hx3 hx1⟩
    · exfalso
      obtain ⟨s, q, x, hSL, -⟩ := h
      exact R3c2.not_isSLEps3_of_card_hat6 hcard s q hSL

end Setting

end Setting4

end CFSG.Quasithin.H13.A6
