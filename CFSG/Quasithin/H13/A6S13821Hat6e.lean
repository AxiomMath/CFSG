module

public import CFSG.Quasithin.H13.A6S13821g
public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.H13.A6S13821zz
public import CFSG.Quasithin.H13.A6S13822b
public import CFSG.Quasithin.H13.A6S13824h
public import CFSG.Quasithin.H13.L32AC47g

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Quasithin.E1.LiftS5 (quotConj quotConj_of_mem)
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_of_hat6 (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 6))) : S.L1 ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have hSQ' := SQTKHyp.of_sqtkGroup ↥H hSQ
  have hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := hHat.1
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
        obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, S.cube_mem_pCoreOf_L1' hxL1⟩
        have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
        rw [← orderOf_eq_one_iff]
        exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
          (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk')
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨hH.1.1 (Subgroup.mem_sup_left hxL1),
          orderOf_eq_prime hx3 hx1⟩
    · exfalso
      obtain ⟨s, q, x, hSL, -⟩ := h
      exact R3c2.not_isSLEps3_of_card_hat6 hcard s q hSL

omit [Finite G] S in
theorem oTwoRes_eq_bot_of_le_pGroup {X P : Subgroup G} (hP : IsPGroup 2 P)
    (h : oTwoRes X ≤ P) : oTwoRes X = ⊥ := by
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxX, m, hm, hxm⟩
  have hxP : x ∈ P := h (Subgroup.subset_closure ⟨hxX, m, hm, hxm⟩)
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [SetLike.mem_coe, Subgroup.mem_bot, ← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
    (orderOf_dvd_of_pow_eq_one hxm) (orderOf_dvd_of_pow_eq_one hk')

theorem quotConj_center_of_mem_R (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K)
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 6))) {y : G}
    (hyR : y ∈ pCoreOf 2 (S.L1 ⊔ T)) (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    ∀ z ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K), quotConj K ⟨y, hyN⟩ z = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hX := A6Hat7.oTwoRes_solvRad_ne_bot hK hHat.2.1
  have hXeq : oTwoRes (solvRad H) = S.X13820 := by
    rcases S.oTwoRes_solvRad_cases h139 h1334 h13 hS hH with h | ⟨hhat, h⟩ | ⟨hhat, h⟩
    · exact absurd h hX
    · rw [h, S.X13820_of_not_hat hhat]
    · rw [h, S.X13820_of_hat hhat]
  have hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G) := by
    rw [← hXeq]
    exact A5.le_normalizer_oTwoRes_of_le_normalizer
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H))
  obtain ⟨c, hcX, hc3, -, hfpf, htri, hdich⟩ := S.exists_c_13820a' hS hH hHX
  have hcK : c ∈ K := hL1K (S.plusData_X13820.le_L1 hcX)
  have hcS : c ∈ solvRad H := by
    rw [← hXeq] at hcX
    exact oTwoRes_le _ hcX
  set cq : ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk (⟨c, hcK⟩ : ↥K) with hcq
  have hcZ : cq ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
    A6Hat7.mem_center_of_mem_solvRad hKH hHat.1 hcS
  have hc1 : cq ≠ 1 := by
    intro h1
    have hcO : c ∈ pCoreOf 2 K := by
      rw [hcq, QuotientGroup.eq_one_iff, A6L24.mem_pCore_iff'] at h1
      exact h1
    have hcQ : c ∈ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) hcO
    have hle : oTwoRes (solvRad H) ≤ pCoreOf 2 H := by
      intro x hx
      rw [hXeq] at hx
      rcases htri x hx with h | h | h
      · exact h
      · have := (pCoreOf 2 H).mul_mem h hcQ
        simpa using this
      · have := (pCoreOf 2 H).mul_mem h ((pCoreOf 2 H).inv_mem hcQ)
        simpa using this
    exact hX (oTwoRes_eq_bot_of_le_pGroup (pCoreOf_isPGroup 2 H) hle)
  have hfix : quotConj K ⟨y, hyN⟩ cq = cq := by
    have h1 := S.comm_c_of_mem_R hS hH hcX hc3 hfpf hdich hyR
    have h2 : y * c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 H := by
      have h3 := (pCoreOf 2 H).inv_mem h1
      have e : (c * y * c⁻¹ * y⁻¹)⁻¹ = y * c * y⁻¹ * c⁻¹ := by group
      rwa [e] at h3
    have hyc : y * c * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyN c).mp hcK
    have h4 : y * c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 K :=
      L32A.C.pCoreOf_inf_le_of_le hKH ⟨h2, K.mul_mem hyc (K.inv_mem hcK)⟩
    rw [hcq, A6L24.quotConj_mk, QuotientGroup.eq_iff_div_mem, A6L24.mem_pCore_iff']
    simpa [div_eq_mul_inv] using h4
  have hord : orderOf cq = 3 := by
    have h3 : cq ^ 3 = 1 := by
      rw [hcq, ← QuotientGroup.mk_pow]
      have : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simp [hc3])
      rw [this, QuotientGroup.mk_one]
    exact orderOf_eq_prime h3 hc1
  have hZ : Subgroup.zpowers cq = Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZ) ?_
    rw [Nat.card_zpowers, hord, hHat.2.1]
  intro z hz
  rw [← hZ] at hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [map_zpow, hfix]

theorem exists_quad_VH_elem
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T))
    (hA : ∀ x ∈ pCoreOf 2 (S.L1 ⊔ T), ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) :
    ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (S.L1 ⊔ T) ∧ ⁅⁅conjClosure V H, Y⁆, Y⁆ = ⊥ ∧
      4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y ∧ ∀ y ∈ Y, y * y = 1 := by
  have hF := hS.hF H hH
  obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle⟩ := S.case2_of_no_transv_loc hF hA
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS H hH K hK hKn hHK γ γ' g s
    (conjClosure S.V3 H) le_rfl hDH.not_ge
  have hm := S.lem13818Four_loc hS.hNS h13315 h1356two hH hF h13314 hA s hDγ hDH hle hgen
  obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF s
  refine ⟨conjSub c (F8.Uγ V H (g : G)), hcR, ?_, ?_, ?_⟩
  · have h1 := congrArg (conjSub c) (S.comm_comm_VH_Vγ hF s)
    rwa [← conjSub_commutator, ← conjSub_commutator,
      conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V H hcH), conjSub_bot] at h1
  · have hY2 : IsPGroup 2 (conjSub c (F8.Uγ V H (g : G))) :=
      (pCoreOf_isPGroup 2 _).to_le hcR
    rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
    have hQ : conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
    rw [← hQ, ← conjSub_inf, F9.mIdx_conjSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) :=
        Nat.pow_le_pow_right (by norm_num) hm
  · rintro _ ⟨y₀, hy₀, rfl⟩
    have h2 : y₀ ^ 2 = 1 := (hF.isElemAbelian_Vγ (g := g)).2 y₀ hy₀
    rw [← map_mul, ← sq, h2, map_one]

end Setting4

end CFSG.Quasithin.H13.A6
