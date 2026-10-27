module

public import CFSG.Quasithin.EmptyFaithful.S152He8Facts
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.H13.A6S1372L76B

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_oPrimeResidualOf {H : Subgroup G}
    (hH : H ∈ S.Hz) : S.L1 ≤ oPrimeResidualOf 3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨⟨hxL, hxN⟩, m, hm, hxm⟩
  have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨⟨hxL, hxN⟩, m, hm, hxm⟩
  have hxH : x ∈ H := hH.1.1 (Subgroup.mem_sup_left hxL1)
  refine Subgroup.subset_closure ⟨hxH, ?_⟩
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hxL
  set g : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, hxV⟩ with hg
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := g) hxL1
  have h6 : S.frame.ρ g ^ 6 = 1 := by
    rw [← K4L_sq _ (cube_mem_K4L h4 h5 hs), ← pow_add]
  have hgm : g ^ m = 1 := Subtype.ext (by simpa [hg] using hxm)
  have hρm : S.frame.ρ g ^ m = 1 := by rw [← map_pow, hgm, map_one]
  have hρ3 : S.frame.ρ g ^ 3 = 1 := by
    have hdm := orderOf_dvd_of_pow_eq_one hρm
    have hcop : Nat.Coprime (orderOf (S.frame.ρ g)) 2 :=
      (Odd.coprime_two_left (Odd.of_dvd_nat hm hdm)).symm
    exact orderOf_dvd_iff_pow_eq_one.1
      (hcop.dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one h6))
  have hx3V : x ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    have h := (S.rho_eq_one_iff (g ^ 3)).1 (by rw [map_pow, hρ3])
    simpa [hg] using h
  set y : ↥L := ⟨x, hxL⟩ ^ 3 with hy
  have hyV : (y : G) ∈ Subgroup.centralizer (V : Set G) := by simpa [hy] using hx3V
  have hyZ := S.mk_mem_center hyV
  have hy3 : (y : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
      (x := ⟨_, hyZ⟩)
    rcases S.card_center_Q with h1 | h1
    · rw [h1, pow_one] at h
      have h2 : (y : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := congrArg Subtype.val h
      rw [h2, one_pow]
    · rw [h1] at h
      simpa using congrArg Subtype.val h
  have hyN : y ^ 3 ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy3]
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨_, hyN⟩
  have hk' : (y ^ 3) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hxm' : (⟨x, hxL⟩ : ↥L) ^ m = 1 := Subtype.ext (by simpa using hxm)
  have hym : (y ^ 3) ^ m = 1 := by
    rw [hy, ← pow_mul, ← pow_mul, show 3 * (3 * m) = m * 9 by ring, pow_mul, hxm', one_pow]
  have hcop : Nat.Coprime (2 ^ k) m := (Odd.coprime_two_left hm).pow_left k
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hym)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff, hy, ← pow_mul] at h1
  have hx9 : x ^ (3 ^ 2) = 1 := by simpa using congrArg Subtype.val h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx9)
  exact ⟨i, hi⟩

theorem exists_quotEquiv_tilde (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  have hker : κ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_pCore_iff, ← GoldS146R.inf_pCoreOf_eq_of_mem_cComp hK,
      Subgroup.mem_inf, and_iff_right k.2, S.mem_QH_iff_tilde hNS h13315 h1356two hH (hKH k.2)]
    exact Subtype.ext_iff.trans (A6Mod.secAct_eq_one_iff hHU hHV ⟨k, hKH k.2⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective κ hκ)⟩

theorem exists_quotEquiv_of_realizes
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G}
    (hK : K ∈ cComp H) {D : FFModel} (hD : D.Faithful)
    {U Z : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hR : D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) U Z) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* D.Gam) := by
  obtain ⟨e₀⟩ := S.exists_quotEquiv_tilde hNS h13315 h1356two hH hK
  obtain ⟨π, hπ⟩ := hR
  exact ⟨e₀.trans (MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec hD hπ, hπ.1⟩).symm⟩

theorem L1_le_of_quotEquiv (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    {X : Type} [Group X] [Finite X] (E : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) (hX : A318Exclusion X) :
    S.L1 ≤ K := by
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  rw [eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hSQ hK
    (He8.isQuasisimple_of_exclusion E hX) E hX]
  exact S.L1_le_oPrimeResidualOf hH

omit S in
theorem pRank_le_two_of_quotEquiv {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) {K : Subgroup G}
    (hK : K ∈ cComp H) {X : Type} [Group X] [Finite X] (E : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X)
    (hq : quasithinIsQTKECat G) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥K)).exists_card_eq
    rw [hj]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h1 := A6L76B.pRank_map_le (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at h1
  have h2 : CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 H :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_of_mem_cComp hK)
  have h3 := pRank_le_two_of_pCoreOf_ne_bot hq hH Nat.prime_three (by norm_num)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) E]
  omega

omit [Finite G] S in
theorem isPerfect_of_quotEquiv {H K : Subgroup G} (hK : K ∈ cComp H) {X : Type} [Group X]
    (E : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) : Group.IsPerfect X := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective

omit S in
theorem nontrivial_of_quotEquiv {H K : Subgroup G} (hK : K ∈ cComp H) {X : Type} [Group X]
    (E : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) : Nontrivial X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have htop : CFSG.pCore 2 ↥K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    rw [← QuotientGroup.eq_one_iff]
    exact E.injective (Subsingleton.elim _ _)
  have hpg : IsPGroup 2 ↥K := fun k => by
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥K))
      ⟨k, by rw [htop]; exact Subgroup.mem_top k⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 (ne_bot_of_mem_cComp hK)
  have : Group.IsNilpotent ↥K := hpg.isNilpotent
  exact Group.IsPerfect.not_isSolvable ↥K (inferInstance : Group.IsSolvable _)

end Setting4

end CFSG.Quasithin.H13.A6
