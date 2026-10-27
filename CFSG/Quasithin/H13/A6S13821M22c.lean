module

public import CFSG.Quasithin.H13.A6S13821g
public import CFSG.Quasithin.EmptyFaithful.T1515eD

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top)
open CFSG.Quasithin.H13.L34 (pslOrd psuOrd slOrd suOrd card_of_isPSLEps3q card_of_isSLEps3
  big_bound)

namespace HatM22

theorem card_of_isHat_m22 {X : Type} [Group X] [Finite X]
    (h : IsHat X (NativeSporadic.Carrier .M22)) : Nat.card X = 1330560 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h22 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv, h22]

theorem card_quotient_hatM22 {X Q : Type} [Group X] [Finite X]
    [Group Q] (h : IsHat X (NativeSporadic.Carrier .M22)) (π : X →* Q)
    (hπ : Function.Surjective π) (hQ : ¬ Subsingleton Q) :
    Nat.card Q = 1330560 ∨ Nat.card Q = 443520 := by
  have hX := card_of_isHat_m22 h
  have hne : π.ker ≠ ⊤ := by
    intro ht
    refine hQ ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    rw [MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top a'),
      MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top b')]
  have hle := le_center_of_normal_ne_top h.1 hne
  have hdvd : Nat.card π.ker ∣ 3 := by
    rw [← h.2.1]
    exact Subgroup.card_dvd_of_le hle
  have hprod : Nat.card Q * Nat.card π.ker = 1330560 := by
    rw [← hX, Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · left
    rw [h1] at hprod
    omega
  · right
    rw [h3] at hprod
    omega

theorem l3Free_1330560 : L3Free1515e 1330560 0 :=
  L3Free1515e.of_check (B := 111) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem false_of_isPSLEps3q {Q : Type} [Group Q] {N : ℕ} (hN : Nat.card Q = N)
    (hL : L3Free1515e N 0) {s : Bool} {q : ℕ} (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1))
    (hQ : IsPSLEps3q s q Q) : False := by
  obtain ⟨hq2, hc⟩ := card_of_isPSLEps3q hQ
  rw [hN] at hc
  have hmod := Int.emod_emod_of_dvd (q : ℤ) (dvd_refl (3 : ℤ))
  cases s with
  | true =>
    have hm : q % 3 = 1 := by
      simp only [↓reduceIte, Int.ModEq] at hq
      omega
    have hg : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left (by omega)
    have hdiv : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
      have h3 : q ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hm]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (by omega) _) _
    rw [Bool.cond_true, pslOrd, hg] at hc
    have hN3 : N * 3 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
      rw [hc]
      exact Nat.div_mul_cancel hdiv
    have hcop : Nat.Coprime (q ^ 3) 3 :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (by omega)).symm
    have hq3 : q ^ 3 ∣ N := hcop.dvd_of_dvd_mul_right ⟨_, hN3⟩
    exact hL.sl q hq2 hm (by omega) hq3 (by rw [hg]; exact hN3)
  | false =>
    have hm : q % 3 = 2 := by
      simp only [Bool.false_eq_true, ↓reduceIte, Int.ModEq] at hq
      omega
    have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left (by omega)
    have hdiv : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
      have h3 : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hm]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (by omega) _) _
    rw [Bool.cond_false, psuOrd, hg] at hc
    have hN3 : N * 3 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
      rw [hc]
      exact Nat.div_mul_cancel hdiv
    have hcop : Nat.Coprime (q ^ 3) 3 :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (by omega)).symm
    have hq3 : q ^ 3 ∣ N := hcop.dvd_of_dvd_mul_right ⟨_, hN3⟩
    exact hL.su q hq2 hm hq3 (by rw [hg]; exact hN3)

theorem false_of_isSLEps3 {Q : Type} [Group Q] (hN : Nat.card Q = 1330560 ∨ Nat.card Q = 443520)
    {s : Bool} {q : ℕ} (hQ : IsSLEps3 s q Q) : False := by
  obtain ⟨hq2, hc⟩ := card_of_isSLEps3 hQ
  have key : ∀ q, 2 ≤ q → slOrd q ≠ 1330560 ∧ slOrd q ≠ 443520 ∧ suOrd q ≠ 1330560 ∧
      suOrd q ≠ 443520 := by
    intro q hq
    by_cases h9 : 9 ≤ q
    · have hb := big_bound h9
      have hle : slOrd q ≤ suOrd q := by
        simp only [slOrd, suOrd]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      have hb' : 729 * (80 * 728) ≤ slOrd q := hb
      omega
    · interval_cases q <;> decide
  obtain ⟨k1, k2, k3, k4⟩ := key q hq2
  cases s with
  | true =>
    rw [Bool.cond_true] at hc
    rcases hN with h | h <;> rw [h] at hc
    · exact k1 hc.symm
    · exact k2 hc.symm
  | false =>
    rw [Bool.cond_false] at hc
    rcases hN with h | h <;> rw [h] at hc
    · exact k3 hc.symm
    · exact k4 hc.symm

theorem threeRank2_hatM22 {X : Type} [Group X] [Finite X]
    (h : IsHat X (NativeSporadic.Carrier .M22)) : FFC.ThreeRank2 X := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (NativeSporadic.Carrier .M22) := Nat.finite_of_card_ne_zero (by
    rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from CFSG.Sporadic.Mathieu.card_M22]
    norm_num)
  have hp : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  have hM : FFC.ThreeRank2 (NativeSporadic.Carrier .M22) :=
    FFC.ThreeRank2.of_pRank (a318Exclusion_m22 (X := NativeSporadic.Carrier .M22)
      ⟨MulEquiv.refl _⟩).rank
  exact FFC.ThreeRank2.of_surjective_pgroup_ker (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) hp (hM.of_mulEquiv e.symm)

end HatM22

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_of_hatM22
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (NativeSporadic.Carrier .M22)) : S.L1 ≤ K := by
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
    have := (HatM22.threeRank2_hatM22 hHat).pRank_two_le
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
      rw [HatM22.card_of_isHat_m22 hHat]
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
  have hcard := HatM22.card_quotient_hatM22 hHat ψ hψs hnt
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · have h1' : K = oPrimeResidualOf 3 H := by
      rw [← CFSG.Quasithin.Vol2.Ch11.SecA.map_oPrimeResidualOf_top, ← h1, hLmap]
    rw [h1']
    exact S.L1_le_oPrimeResidualOf hH
  · exfalso
    obtain ⟨s, q, hmod, hPSL, -⟩ := h2
    rcases hcard with hc | hc
    · exact HatM22.false_of_isPSLEps3q hc HatM22.l3Free_1330560 hmod hPSL
    · exact HatM22.false_of_isPSLEps3q hc l3Free_443520 hmod hPSL
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
      exact HatM22.false_of_isSLEps3 hcard hSL

end Setting4

end CFSG.Quasithin.H13.A6
