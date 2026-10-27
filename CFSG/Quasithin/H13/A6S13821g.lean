module

public import CFSG.Quasithin.EmptyFaithful.S152VL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.EmptyFaithful.R3c2Base
public import CFSG.Quasithin.H13.A6S1372L74e
public import CFSG.Quasithin.H13.A6S1372L76W
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top)
open CFSG.Quasithin.H13.L34 (ListOrd pslOrd psuOrd slOrd suOrd pslOrd_listOrd psuOrd_not_listOrd
  slOrd_not_listOrd suOrd_listOrd card_of_isPSLEps3q card_of_isSLEps3)

namespace A6Hat7

theorem card_of_isHat_alt7 {X : Type} [Group X] [Finite X]
    (h : IsHat X (alternatingGroup (Fin 7))) : Nat.card X = 7560 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv, S152V.card_alternatingGroup_seven']

theorem card_quotient_hat7 {X Q : Type} [Group X] [Finite X] [Group Q]
    (h : IsHat X (alternatingGroup (Fin 7))) (π : X →* Q) (hπ : Function.Surjective π)
    (hQ : ¬ Subsingleton Q) : Nat.card Q = 7560 ∨ Nat.card Q = 2520 := by
  have hX := card_of_isHat_alt7 h
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
  have hprod : Nat.card Q * Nat.card π.ker = 7560 := by
    rw [← hX, Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · left
    rw [h1] at hprod
    omega
  · right
    rw [h3] at hprod
    omega

theorem not_case2_of_card_hat7 {Q : Type} [Group Q] (h : Nat.card Q = 7560 ∨ Nat.card Q = 2520)
    (s : Bool) (q : ℕ) (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (hQ : IsPSLEps3q s q Q) :
    False := by
  have hL : ListOrd (Nat.card Q) := by unfold ListOrd; omega
  obtain ⟨hq2, hcard⟩ := card_of_isPSLEps3q hQ
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL h
    have h4 := pslOrd_listOrd hq2 hL
    subst h4
    simp [pslOrd] at h
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL
    have hq3 : q % 3 = 2 := by
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      have := Int.emod_emod_of_dvd (q : ℤ) (dvd_refl (3 : ℤ))
      unfold Int.ModEq at hq
      omega
    exact psuOrd_not_listOrd hq2 hq3 hL

theorem not_isSLEps3_of_card_hat7 {Q : Type} [Group Q]
    (h : Nat.card Q = 7560 ∨ Nat.card Q = 2520) (s : Bool) (q : ℕ) (hQ : IsSLEps3 s q Q) :
    False := by
  have hL : ListOrd (Nat.card Q) := by unfold ListOrd; omega
  obtain ⟨hq2, hcard⟩ := card_of_isSLEps3 hQ
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL
    exact slOrd_not_listOrd hq2 hL
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL h
    have h3 := suOrd_listOrd hq2 hL
    subst h3
    simp [suOrd] at h

theorem threeRank2_hat7 {X : Type} [Group X] [Finite X]
    (h : IsHat X ↥(alternatingGroup (Fin 7))) : FFC.ThreeRank2 X := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  exact FFC.ThreeRank2.of_surjective_pgroup_ker (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) hp ((FFC.threeRank2_alt (by norm_num)).of_mulEquiv e.symm)

end A6Hat7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem cube_mem_pCoreOf_L1' {x : G} (hx : x ∈ S.L1) :
    x ^ 3 ∈ pCoreOf 2 S.L1 := by
  by_cases hhat : IsHatA6 L
  · exact S.cube_mem_pCoreOf_L1_hat hhat hx
  · exact S.cube_mem_pCoreOf_L1 hhat hx

theorem L1_le_of_hat7 (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7))) : S.L1 ≤ K := by
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
    have := (A6Hat7.threeRank2_hat7 hHat).pRank_two_le
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
      rw [A6Hat7.card_of_isHat_alt7 hHat]
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
  have hcard := A6Hat7.card_quotient_hat7 hHat ψ hψs hnt
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · have h1' : K = oPrimeResidualOf 3 H := by
      rw [← CFSG.Quasithin.Vol2.Ch11.SecA.map_oPrimeResidualOf_top, ← h1, hLmap]
    rw [h1']
    exact S.L1_le_oPrimeResidualOf hH
  · exfalso
    obtain ⟨s, q, hmod, hPSL, -⟩ := h2
    exact A6Hat7.not_case2_of_card_hat7 hcard s q hmod hPSL
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
      exact A6Hat7.not_isSLEps3_of_card_hat7 hcard s q hSL

end Setting4

end CFSG.Quasithin.H13.A6
