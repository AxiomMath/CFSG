module

public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.RankThree.PartOne.KLC.PRankTwo
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd
  quotPCore_subgroupOf_equiv pRank_subgroupOf_eq map_oPrimeResidualOf_top)

section Cube

variable {X : Type*} [Group X]

theorem cube_mul_of_comm_mem_center {x y : X} (hc : y⁻¹ * x⁻¹ * y * x ∈ Subgroup.center X)
    (hc3 : (y⁻¹ * x⁻¹ * y * x) ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  obtain ⟨c, hcdef⟩ : ∃ c : X, c = y⁻¹ * x⁻¹ * y * x := ⟨_, rfl⟩
  rw [← hcdef] at hc hc3
  have hcg : ∀ g : X, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hc g
  have e1 : x⁻¹ * y * x = y * c := by rw [hcdef]; group
  have hxc : x⁻¹ * c * x = c := by
    rw [mul_assoc, ← hcg x, ← mul_assoc, inv_mul_cancel, one_mul]
  have e2 : x⁻¹ * (y * c) * x = y * c * c := by
    calc x⁻¹ * (y * c) * x = (x⁻¹ * y * x) * (x⁻¹ * c * x) := by group
      _ = y * c * c := by rw [e1, hxc]
  have hcy : c * y = y * c := (hcg y).symm
  have e3 : y * c * c * (y * c) * y = (y * c) ^ 3 := by
    calc y * c * c * (y * c) * y = y * c * (c * y) * c * y := by group
      _ = y * c * (y * c) * c * y := by rw [hcy]
      _ = y * c * (y * c) * (c * y) := by group
      _ = y * c * (y * c) * (y * c) := by rw [hcy]
      _ = (y * c) ^ 3 := by rw [pow_three]; group
  have e4 : (y * c) ^ 3 = y ^ 3 * c ^ 3 := (Commute.mul_pow (hcg y) 3)
  calc (x * y) ^ 3 = x ^ 3 * (x⁻¹ * (x⁻¹ * y * x) * x) * (x⁻¹ * y * x) * y := by
        rw [pow_three, pow_three]; group
    _ = x ^ 3 * (y * c * c * (y * c) * y) := by rw [e1, e2]; group
    _ = x ^ 3 * y ^ 3 := by rw [e3, e4, hc3, mul_one]

end Cube

section Rank

theorem two_le_pRank_of_card_center_three {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3)
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X))) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center X with hZdef
  obtain ⟨π, hπ⟩ : ∃ π : X →* X ⧸ Z, π = QuotientGroup.mk' Z := ⟨_, rfl⟩
  have hπs : Function.Surjective π := hπ ▸ QuotientGroup.mk'_surjective Z
  have hπ1 : ∀ g : X, π g = 1 ↔ g ∈ Z := fun g => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
    rw [hZ] at h1
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h1)
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup (X ⧸ Z))
  have h9 : 9 ≤ Nat.card E := by
    rw [hEc]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Z)) := Nat.pow_le_pow_right (by norm_num) hr
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := hE.2
  have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  have hord3 : ∀ e ∈ E, e ≠ 1 → orderOf e = 3 := fun e he he1 =>
    orderOf_eq_prime (hE3 e he) he1
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra h
    push Not at h
    have hle : E ≤ ⊥ := fun e he => Subgroup.mem_bot.mpr (h e he)
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers a := fun e he => h e he
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord3 a haE ha1] at h1
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hab : ∀ m : ℤ, a * b ^ m ≠ 1 := by
    intro m h
    have hamem : a ∈ Subgroup.zpowers b := by
      have : a = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, ← zpow_neg]
      exact Subgroup.zpow_mem_zpowers b (-m)
    exact hba (A320.mem_zpowers_of_mem_zpowers_prime (hord3 b hbE hb1) hamem ha1)
  obtain ⟨a', rfl⟩ := hπs a
  obtain ⟨b', rfl⟩ := hπs b
  have hb3Z : b' ^ 3 ∈ Z := (hπ1 _).mp (by rw [map_pow]; exact hE3 _ hbE)
  have ha3Z : a' ^ 3 ∈ Z := (hπ1 _).mp (by rw [map_pow]; exact hE3 _ haE)
  obtain ⟨x, hx3, hxE, hx1⟩ : ∃ x : X, x ^ 3 = 1 ∧ π x ∈ E ∧ π x ≠ 1 := by
    by_cases hb31 : b' ^ 3 = 1
    · exact ⟨b', hb31, hbE, hb1⟩
    ·
      have hzb : Subgroup.zpowers (b' ^ 3) = Z := by
        have hle : Subgroup.zpowers (b' ^ 3) ≤ Z := Subgroup.zpowers_le.mpr hb3Z
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        rw [hZ, Nat.card_zpowers]
        have : orderOf (b' ^ 3) = 3 := orderOf_eq_prime (hZ3 _ hb3Z) hb31
        omega
      have hainv : (a' ^ 3)⁻¹ ∈ Subgroup.zpowers (b' ^ 3) := by
        rw [hzb]
        exact Z.inv_mem ha3Z
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hainv
      refine ⟨a' * b' ^ m, ?_, ?_, ?_⟩
      · have hcZ : (b' ^ m)⁻¹ * a'⁻¹ * b' ^ m * a' ∈ Z := by
          refine (hπ1 _).mp ?_
          have hba' : π b' ^ m * π a' = π a' * π b' ^ m :=
            hEcomm _ (Subgroup.zpow_mem _ hbE m) _ haE
          simp only [map_mul, map_inv, map_zpow]
          calc (π b' ^ m)⁻¹ * (π a')⁻¹ * π b' ^ m * π a' =
              (π b' ^ m)⁻¹ * (π a')⁻¹ * (π b' ^ m * π a') := by group
            _ = 1 := by rw [hba']; group
        rw [cube_mul_of_comm_mem_center hcZ (hZ3 _ hcZ), ← zpow_natCast (b' ^ m),
          ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, mul_inv_cancel]
      · rw [map_mul, map_zpow]
        exact E.mul_mem haE (Subgroup.zpow_mem _ hbE m)
      · rw [map_mul, map_zpow]
        exact hab m
  have hxo : orderOf (π x) = 3 := hord3 _ hxE hx1
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have hle : Z ≤ ⊥ := fun e he => Subgroup.mem_bot.mpr (h e he)
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot, hZ] at this
    omega
  have hzo : orderOf z = 3 := orderOf_eq_prime (hZ3 z hzZ) hz1
  have hcom : Commute x z := (Subgroup.mem_center_iff.mp hzZ x)
  have h2 := CFSG.RankThree.PartOne.KLC.two_le_pRank_of_two_commuting Nat.prime_three hcom hx3
    (hZ3 z hzZ) (fun i j hij => by
      have hπz : π z = 1 := (hπ1 z).mpr hzZ
      have hi : π x ^ i = 1 := by
        have := congrArg π hij
        rwa [map_mul, map_zpow, map_zpow, hπz, one_zpow, mul_one, map_one] at this
      have hi3 : (3 : ℤ) ∣ i := by
        have := orderOf_dvd_iff_zpow_eq_one.mpr hi
        rwa [hxo] at this
      have hxi : x ^ i = 1 := by
        have hxo' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
        exact orderOf_dvd_iff_zpow_eq_one.mp
          (Int.natCast_dvd_natCast.mpr hxo' |>.trans hi3)
      refine ⟨hi3, ?_⟩
      rw [hxi, one_mul] at hij
      have := orderOf_dvd_iff_zpow_eq_one.mpr hij
      rwa [hzo] at this)
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2

end Rank

section A318

theorem nonempty_starImage_equiv {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : IsPGroup 3 ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Nonempty (↥(starImage 3 L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  set φ₀ : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ₀
  set π₃ := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ₃
  let ρ : ↥L →* ↥(starImage 3 L) :=
    (π₃.comp L.subtype).codRestrict (starImage 3 L) (fun x => ⟨x, x.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : ↥L, x ∈ ρ.ker → (x : H) ∈ CFSG.pPrimeCore 3 H := by
    intro x hx
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change π₃ (x : H) = 1 at h1
    rwa [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hN3 : Nat.Coprime 3 (Nat.card ρ.ker) := by
    have hle : ρ.ker.map L.subtype ≤ CFSG.pPrimeCore 3 H := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hNX : ρ.ker.map φ₀ = ⊥ := by
    have hn : (ρ.ker.map φ₀).Normal :=
      Subgroup.Normal.map inferInstance φ₀ (QuotientGroup.mk'_surjective _)
    have hdvd : Nat.card (ρ.ker.map φ₀) ∣ Nat.card ρ.ker := by
      rw [← MonoidHom.domRestrict_range]
      exact card_range_dvd _
    have hne : ρ.ker.map φ₀ ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.card_top] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hdvd hN3) h3)
        (by norm_num)
    have hle := le_center_of_normal_ne_top hQ hne
    have hP : IsPGroup 3 ↥(ρ.ker.map φ₀) := hZ.to_le hle
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
    have hm0 : m = 0 := by
      by_contra hm0
      have h3m : 3 ∣ Nat.card (ρ.ker.map φ₀) := by
        rw [hm]
        exact dvd_pow_self 3 hm0
      have := (Nat.Coprime.coprime_dvd_right hdvd hN3)
      exact absurd (Nat.Coprime.eq_one_of_dvd this h3m) (by norm_num)
    rw [hm0, pow_zero] at hm
    exact Subgroup.card_eq_one.mp hm
  have hle : ρ.ker ≤ φ₀.ker := by
    intro x hx
    have : φ₀ x ∈ ρ.ker.map φ₀ := Subgroup.mem_map_of_mem φ₀ hx
    rw [hNX, Subgroup.mem_bot] at this
    exact this
  have hle' : φ₀.ker ≤ ρ.ker := by
    intro x hx
    rw [hφ₀, QuotientGroup.ker_mk'] at hx
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    change π₃ (x : H) = 1
    rw [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 : (x : H) ∈ (CFSG.pCore 2 ↥L).map L.subtype := ⟨x, hx, rfl⟩
    exact A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num) (A318.map_pCore_le_pCore L h1)
  have hkereq : ρ.ker = CFSG.pCore 2 ↥L := by
    refine le_antisymm (hle.trans ?_)
      (by rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]; exact hle')
    rw [hφ₀, QuotientGroup.ker_mk']
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hkereq)⟩

theorem map_thetaOf_top {G : Type} [Group G] (I : Subgroup G) :
    (thetaOf (⊤ : Subgroup ↥I)).map I.subtype = thetaOf I := by
  rw [thetaOf, thetaOf, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩
    exact ⟨y.2, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, hy]⟩
  · rintro ⟨hx, hx3⟩
    exact ⟨⟨x, hx⟩, ⟨trivial, by rw [← Subgroup.orderOf_coe]; exact hx3⟩, rfl⟩

theorem card_statedSU_three_of {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
  CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK

theorem sl3_su3_card_ne {q n : ℕ} (hq : 2 ≤ q) (hn : n = 504 ∨ n = 1080 ∨ n = 7560 ∨ n = 18144) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≠ n ∧ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ n := by
  have hn' : n ≤ 18144 := by omega
  have h4 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hbound : ∀ t : ℕ, 1 ≤ t → q ^ 3 * (q ^ 2 - 1) * t = n → q ≤ 26 := by
    intro t ht h
    by_contra hc
    push Not at hc
    have h1 : 19683 ≤ q ^ 3 := by
      calc 19683 = 27 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hc 3
    have h2 : q ^ 3 ≤ q ^ 3 * (q ^ 2 - 1) * t := by
      calc q ^ 3 = q ^ 3 * 1 * 1 := by ring
        _ ≤ q ^ 3 * (q ^ 2 - 1) * t := Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) ht
    omega
  constructor
  · intro h
    have hq26 := hbound _ (by omega) h
    interval_cases q <;> rcases hn with rfl | rfl | rfl | rfl <;> norm_num at h
  · intro h
    have hq26 := hbound _ (by omega) h
    interval_cases q <;> rcases hn with rfl | rfl | rfl | rfl <;> norm_num at h

theorem eq_oPrime_or_theta_of_center_three (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) {G : Type} [Group G] [Finite G] {I L : Subgroup G} (hH : SQTKGroup ↥I)
    (hL : L ∈ cComp I) (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    {S : Type} [Group S] [Finite S] (hS : A318Exclusion S)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S)
    (hord : ∀ q : ℕ, 2 ≤ q → q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≠ 3 * Nat.card S ∧
      q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ 3 * Nat.card S) :
    L = oPrimeResidualOf 3 I ∨ L = thetaOf I := by
  classical
  have hLH : L ≤ I := le_of_mem_cComp hL
  set Lb := ↥L ⧸ CFSG.pCore 2 ↥L with hLb
  have hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Lb) := by
    refine two_le_pRank_of_card_center_three hZ3 ?_
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact hS.rank
  have hcardLb : Nat.card Lb = 3 * Nat.card S := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Lb),
      Nat.card_congr e.toEquiv, hZ3, mul_comm]
  have hSQ := SQTKHyp.of_sqtkGroup ↥I hH
  have hLc := subgroupOf_mem_cComp hL
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr1 : 1 < CFSG.Open.pRank 3 (L.subgroupOf I) := by
    rw [pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num)]
    omega
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr1
  have hLn : (L.subgroupOf I).Normal :=
    A318.normal_of_pRank_gt_one hH (h38 _ hSQ) hLc Nat.prime_three (by norm_num) hr1
  have hcen' : Nat.card (Subgroup.center
      (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I))) = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.centerCongr e₀).toEquiv
  have hZ3' : IsPGroup 3 ↥(Subgroup.center
      (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I))) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hcen']; norm_num)
  have h3X' : 3 ∣ Nat.card (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I)) := by
    rw [Nat.card_congr e₀.toEquiv, hcardLb]
    exact dvd_mul_right 3 _
  obtain ⟨eS⟩ := nonempty_starImage_equiv (L := L.subgroupOf I) hQ' hZ3' h3X'
  let eLX : ↥(starImage 3 (L.subgroupOf I)) ≃* Lb := eS.trans e₀
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3a | h3b⟩
  ·
    left
    rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]
  ·
    exfalso
    obtain ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩ := h2
    subst hq
    let ψ : ↥(starImage 3 (L.subgroupOf I)) →* S :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Lb)).comp eLX.toMonoidHom)
    have hψ : Function.Surjective ψ :=
      e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eLX.surjective)
    exact hS.noImage _ s r k hrp hk1 hPSL hmod ψ hψ
  ·
    right
    rw [← map_thetaOf_top, ← h3a, Subgroup.map_subgroupOf_eq_of_le hLH]
  ·
    exfalso
    obtain ⟨s, q, x, hSL, -⟩ := h3b
    have hSc : Nat.card ↥(starImage 3 (L.subgroupOf I)) = 3 * Nat.card S := by
      rw [Nat.card_congr eLX.toEquiv, hcardLb]
    cases s
    ·
      obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hSL
      have h1 : 1 < q ^ 2 := hK ▸ Finite.one_lt_card
      have hq2 : 2 ≤ q := by
        rcases Nat.lt_or_ge q 2 with hlt | hge
        · interval_cases q <;> simp at h1
        · exact hge
      have h2 := card_statedSU_three_of hK
      rw [← Nat.card_congr eK.toEquiv, hSc] at h2
      exact (hord q hq2).2 h2.symm
    ·
      obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hSL
      have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K)
      rw [← Nat.card_congr eK.toEquiv, hSc, hK] at h2
      exact (hord q (hK ▸ Finite.one_lt_card)).1 h2.symm

end A318

end CFSG.Quasithin.H13.A5
