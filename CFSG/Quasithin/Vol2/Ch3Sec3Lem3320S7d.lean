module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7c
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_of_isL2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W : Type} [Group W]
    (h : F6.IsL2 p 1 W) : p ∣ Nat.card W := by
  obtain ⟨-, F, hF, hFf, hcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv]
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, hcard⟩
  rw [CFSG.GorensteinWalter.psl2_card_formula F hodd, hcard, pow_one]
  have h2 : 2 ∣ p ^ 2 - 1 :=
    (Nat.Odd.sub_odd ((hp.odd_of_ne_two hp2).pow) odd_one).two_dvd
  rw [Nat.mul_div_assoc _ h2]
  exact dvd_mul_right _ _

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem oTwoUpper_Y : oTwoUpper (conjClosure X D) = conjClosure X D := by
  refine le_antisymm (oTwoUpper_le _) (conjClosure_le fun d hd x hx => ?_)
  have key : ∀ y ∈ oTwoUpper X, d * y * d⁻¹ ∈ oTwoUpper (conjClosure X D) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      refine Subgroup.subset_closure ⟨mem_conjClosure hd hz.1, ?_⟩
      have := orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective z
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this]
      exact hz.2
    | one => simp
    | mul y z _ _ ihy ihz =>
      have e : d * (y * z) * d⁻¹ = (d * y * d⁻¹) * (d * z * d⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
      have e : d * y⁻¹ * d⁻¹ = (d * y * d⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ihy
  exact key x (by rw [H.hXX]; exact hx)

omit H in
theorem inf_pCoreOf_le :
    conjClosure X D ⊓ pCoreOf 2 (X ⊔ T ⊔ D) ≤ pCoreOf 2 (conjClosure X D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
  · intro y hy
    exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hy)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Y_le_B hy))
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right

theorem le_pCoreOf_of_chief (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {U V : Subgroup G}
    (hc : IsTwoChiefFactor (conjClosure X D) U V) : U ≤ pCoreOf 2 (conjClosure X D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsB, hnabB⟩ := H.simple_quot hA hB hY hYB₀ htop
  have hUY : U ≤ conjClosure X D := hc.2.1
  have hUB : U ≤ X ⊔ T ⊔ D := hUY.trans Y_le_B
  have hn : (star (X ⊔ T ⊔ D) B₀ U).Normal := by
    refine ⟨fun n hn q => ?_⟩
    have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
      rw [htop]
      exact Subgroup.mem_top q
    obtain ⟨y, hyB, hy, rfl⟩ := mem_star_iff.mp hq
    exact (Subgroup.mem_normalizer_iff.mp (mk_mem_normalizer_star hyB (hc.2.2.1 hy)) n).mp hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (star (X ⊔ T ⊔ D) B₀ U) with h | h
  · rw [star_eq_bot_iff hUB] at h
    intro u hu
    exact inf_pCoreOf_le ⟨hUY hu, hle ⟨hUY hu, h hu⟩⟩
  · exfalso
    apply (not_le_of_gt hc.1)
    refine hc.2.1.trans ?_
    rw [← H.oTwoUpper_Y, oTwoUpper, Subgroup.closure_le]
    rintro z ⟨hzY, hzo⟩
    have hzB : z ∈ X ⊔ T ⊔ D := Y_le_B hzY
    have hz : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨z, hzB⟩ ∈
        star (X ⊔ T ⊔ D) B₀ U := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨u, huB, hu, huz⟩ := mem_star_iff.mp hz
    have h1 : u⁻¹ * z ∈ B₀ := (QuotientGroup.eq (s := B₀.subgroupOf (X ⊔ T ⊔ D))).mp huz
    have h2 : u⁻¹ * z ∈ pCoreOf 2 (conjClosure X D) :=
      inf_pCoreOf_le ⟨(conjClosure X D).mul_mem ((conjClosure X D).inv_mem (hUY hu)) hzY,
        hle ⟨(conjClosure X D).mul_mem ((conjClosure X D).inv_mem (hUY hu)) hzY, h1⟩⟩
    have hzU : z ∈ U := by
      refine mem_of_odd_of_mem_sup (S := pCoreOf 2 (conjClosure X D))
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hc.2.2.1)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_ hzo
      have e : z = u * (u⁻¹ * z) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hu h2
    obtain ⟨k, hk⟩ := hc.2.2.2.2.2 z hzU
    exact Lem3328.mem_of_pow_odd hzo (by rw [pow_orderOf_eq_one]; exact V.one_mem) hk

omit H in
theorem exists_orderOf_eq_p [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) :
    ∃ y ∈ conjClosure X D, orderOf y = p := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := dvd_card_of_isL2 hp hp2 hL
  have h2 : Nat.card ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) ∣ Nat.card ↥(conjClosure X D) := by
    have := Subgroup.card_dvd_of_surjective
      ((QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))).subgroupMap_surjective
        ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Y_le_B).toEquiv] at this
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(conjClosure X D)) p (h1.trans h2)
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem exists_moved (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {U V : Subgroup G}
    (hc : IsTwoChiefFactor (conjClosure X D) U V) (hn : ¬ ⁅U, conjClosure X D⁆ ≤ V) {y : G}
    (hyY : y ∈ conjClosure X D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hy : orderOf y = p) :
    ∃ u ∈ U, u⁻¹ * (y * u * y⁻¹) ∉ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hsB, hnabB⟩ := H.simple_quot hA hB hY hYB₀ htop
  let C : Subgroup G := conjClosure X D ⊓ ⨅ u : ↥U, stabSub V u
  have hmemC : ∀ z, z ∈ C ↔ z ∈ conjClosure X D ∧ ∀ u ∈ U, u⁻¹ * (z * u * z⁻¹) ∈ V := by
    intro z
    rw [Subgroup.mem_inf, Subgroup.mem_iInf]
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun u hu => (mem_stabSub.mp (h ⟨u, hu⟩)).2⟩
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun u => mem_stabSub.mpr ⟨hc.2.2.2.1 hz, h u u.2⟩⟩
  have hyC : y ∈ C := (hmemC y).mpr ⟨hyY, hcon⟩
  have hCY : C ≤ conjClosure X D := inf_le_left
  have hYC : conjClosure X D ≤ Subgroup.normalizer (C : Set G) := by
    refine Main3324.le_normalizer_of_conj fun y' hy' z hz => ?_
    obtain ⟨hzY, hz'⟩ := (hmemC z).mp hz
    refine (hmemC _).mpr ⟨(conjClosure X D).mul_mem ((conjClosure X D).mul_mem hy' hzY)
      ((conjClosure X D).inv_mem hy'), fun u hu => ?_⟩
    have hu' : y'⁻¹ * u * y' ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.2.2.1 ((conjClosure X D).inv_mem hy')) u).mp hu
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.2.2.2.1 hy') _).mp (hz' _ hu')
    have e : u⁻¹ * (y' * z * y'⁻¹ * u * (y' * z * y'⁻¹)⁻¹) =
        y' * ((y'⁻¹ * u * y')⁻¹ * (z * (y'⁻¹ * u * y') * z⁻¹)) * y'⁻¹ := by group
    rw [e]
    exact h1
  have hCB : C ≤ X ⊔ T ⊔ D := hCY.trans Y_le_B
  have hnC : (star (X ⊔ T ⊔ D) B₀ C).Normal := by
    refine ⟨fun n hn q => ?_⟩
    have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
      rw [htop]
      exact Subgroup.mem_top q
    obtain ⟨y', hy'B, hy', rfl⟩ := mem_star_iff.mp hq
    exact (Subgroup.mem_normalizer_iff.mp (mk_mem_normalizer_star hy'B (hYC hy')) n).mp hn
  have hyB₀ : y ∉ B₀ := by
    intro hyB
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T ⊔ D)) ⟨y, hle ⟨hyY, hyB⟩⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    rw [hy] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  have hne : star (X ⊔ T ⊔ D) B₀ C ≠ ⊥ := by
    rw [Ne, star_eq_bot_iff hCB]
    exact fun h => hyB₀ (h hyC)
  have htopC : star (X ⊔ T ⊔ D) B₀ C = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  have hYle : conjClosure X D ≤ C := by
    rw [← H.oTwoUpper_Y, oTwoUpper, Subgroup.closure_le]
    rintro z ⟨hzY, hzo⟩
    have hzB : z ∈ X ⊔ T ⊔ D := Y_le_B hzY
    have hz : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨z, hzB⟩ ∈
        star (X ⊔ T ⊔ D) B₀ C := by
      rw [htopC]
      exact Subgroup.mem_top _
    obtain ⟨c, hcB, hcC, hcz⟩ := mem_star_iff.mp hz
    have h1 : c⁻¹ * z ∈ B₀ := (QuotientGroup.eq (s := B₀.subgroupOf (X ⊔ T ⊔ D))).mp hcz
    have hcY := hCY hcC
    have h3 : c⁻¹ * z ∈ conjClosure X D :=
      (conjClosure X D).mul_mem ((conjClosure X D).inv_mem hcY) hzY
    have h2 : c⁻¹ * z ∈ conjClosure X D ⊓ pCoreOf 2 (X ⊔ T ⊔ D) := ⟨h3, hle ⟨h3, h1⟩⟩
    refine mem_of_odd_of_mem_sup (S := conjClosure X D ⊓ pCoreOf 2 (X ⊔ T ⊔ D))
      (inf_le_left.trans hYC) ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
      ?_ hzo
    have e : z = c * (c⁻¹ * z) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hcC h2
  apply hn
  rw [Subgroup.commutator_le]
  intro u hu z hz
  have h1 := ((hmemC z).mp (hYle hz)).2 u⁻¹ (U.inv_mem hu)
  have e : ⁅u, z⁆ = u⁻¹⁻¹ * (z * u⁻¹ * z⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem two_pow_ten_le (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) {U V : Subgroup G}
    (hc : IsTwoChiefFactor (conjClosure X D) U V) (hn : ¬ ⁅U, conjClosure X D⁆ ≤ V) :
    2 ^ 10 ≤ V.relIndex U := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyY, hy⟩ := exists_orderOf_eq_p (X := X) (T := T) hp hp2 hL
  have hmove := H.exists_moved hA hB hY hYB₀ htop hle hc hn hyY hp hp2 hy
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hc.2.1.trans hc.2.2.2.1
  have : (V.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn'⟩ := (isPGroup_section (p := 2) (U := U) (V := V) hc.2.2.2.2.2).exists_card_eq
  have hrel : V.relIndex U = 2 ^ n := hn'
  obtain ⟨k, hk1, hkn, hpk⟩ := exists_dvd_two_pow_sub_one hp2 hUV (hc.2.2.1 hyY)
    (hc.2.2.2.1 hyY) hy hmove hrel
  rw [hrel]
  by_contra hlt
  push Not at hlt
  have hn9 : n ≤ 9 := by
    by_contra h
    push Not at h
    exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) h))
  exact not_dvd_two_pow_sub_one hp hp24 hk1 (hkn.trans hn9) hpk

theorem pCoreOf_le_commutator : pCoreOf 2 X ≤ ⁅pCoreOf 2 X, X⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxX, hx3, -, hgen⟩ := H.exists_x
  have hPX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXP : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQP : ⁅pCoreOf 2 X, X⁆ ≤ pCoreOf 2 X := commutator_le_of_le_normalizer hXP
  have hXQ : X ≤ Subgroup.normalizer ((⁅pCoreOf 2 X, X⁆ : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXP hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)]
  have hgenP : ∀ x' ∈ X, ∃ j : ℕ, x' * (x ^ j)⁻¹ ∈ pCoreOf 2 X := by
    intro x' hx'
    obtain ⟨j, hj⟩ := hgen x' hx'
    refine ⟨j, CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (N := X ⊓ pCoreOf 2 (X ⊔ T)) inf_le_left ?_ ?_
      ⟨X.mul_mem hx' (X.inv_mem (X.pow_mem hxX j)), hj⟩⟩
    · intro y hy
      exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hy)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T) (Subgroup.mem_sup_left hy))
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right
  set N := ⁅pCoreOf 2 X, X⁆ ⊔ Subgroup.zpowers x with hN
  have hPN : pCoreOf 2 X ≤ Subgroup.normalizer (N : Set G) := by
    refine Main3324.le_normalizer_of_conj fun s hs n hn => ?_
    have hmap : N.map (MulAut.conj s).toMonoidHom ≤ N := by
      rw [hN, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨q, hq, rfl⟩
        refine Subgroup.mem_sup_left ?_
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact (Subgroup.mem_normalizer_iff.mp (hXQ (hPX hs)) q).mp hq
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have e : (MulAut.conj s).toMonoidHom x = ⁅s, x⁆ * x := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator hs hxX)
        (Subgroup.mem_zpowers x)
    exact hmap ⟨n, hn, rfl⟩
  have hXN : X ≤ N ⊔ pCoreOf 2 X := by
    intro x' hx'
    obtain ⟨j, hj⟩ := hgenP x' hx'
    have e : x' = (x' * (x ^ j)⁻¹) * x ^ j := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hj (Subgroup.mem_sup_right (Subgroup.pow_mem _
      (Subgroup.mem_zpowers x) j))
  have hXleN : X ≤ N := le_of_le_sup_pgroup H.hXX hPN
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hXN
  intro s hs
  have hzQ : Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅pCoreOf 2 X, X⁆ : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr (hXQ hxX)
  obtain ⟨q, hq, e, he, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hzQ).mp (hXleN (hPX hs))
  have heP : e ∈ pCoreOf 2 X := by
    have := (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem (hQP hq)) hs
    simpa using this
  have he1 : e = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h3 : (x ^ k) ^ 3 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hx3, one_zpow]
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨_, heP⟩
    have ha' : (x ^ k) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one ha')
    have h2 : Nat.gcd 3 (2 ^ a) = 1 := Nat.Coprime.pow_right a (by norm_num)
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  rw [he1, mul_one]
  exact hq

theorem star_J_eq_top (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    {g : G} (hg : g ∈ D) (hK₀top : star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = ⊤) :
    star (X ⊔ T ⊔ D) B₀ (X ⊔ conjByElt g X) = ⊤ := by
  obtain ⟨hsB, hnabB⟩ := H.simple_quot hA hB hY hYB₀ htop
  have hXgB : conjByElt g X ≤ X ⊔ T ⊔ D :=
    (Subgroup.map_mono le_sup_left).trans (conj_le_B hg)
  have hJB : X ⊔ conjByElt g X ≤ X ⊔ T ⊔ D := sup_le (le_sup_left.trans le_sup_left) hXgB
  have hGJ : gZero X T g ≤ (X ⊔ conjByElt g X) ⊔ T := by
    show X ⊔ T ⊔ conjByElt g (X ⊔ T) ≤ _
    rw [H.conjByElt_sup_eq hg]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hTJ : T ≤ Subgroup.normalizer ((X ⊔ conjByElt g X : Subgroup G) : Set G) := fun t ht =>
    ChiefCount.mem_normalizer_sup (H.hTX ht) (H.T_le_normalizer_conj H.hTX hg ht)
  have hJT : (X ⊔ conjByElt g X) ⊔ T ≤
      Subgroup.normalizer ((X ⊔ conjByElt g X : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hTJ
  have hn : (star (X ⊔ T ⊔ D) B₀ (X ⊔ conjByElt g X)).Normal := by
    refine ⟨fun n hn q => ?_⟩
    have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) := by
      rw [hK₀top]
      exact Subgroup.mem_top q
    obtain ⟨k, hkB, hk, rfl⟩ := mem_star_iff.mp hq
    exact (Subgroup.mem_normalizer_iff.mp
      (mk_mem_normalizer_star hkB (hJT (hGJ (perfectCore_le _ hk)))) n).mp hn
  have hne : star (X ⊔ T ⊔ D) B₀ (X ⊔ conjByElt g X) ≠ ⊥ := by
    rw [Ne, star_eq_bot_iff hJB]
    exact fun h => H.not_X_le_B₀ hB.inf (le_sup_left.trans h)
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne

omit [Finite G] H in
theorem map_conj_fixSub {U V : Subgroup G} {x y : G} (hUV : U ≤ Subgroup.normalizer (V : Set G))
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hx₁V : y * x * y⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    (fixSub U V (Subgroup.zpowers x) hUV).map (MulAut.conj y).toMonoidHom =
      fixSub U V (Subgroup.zpowers (y * x * y⁻¹)) hUV := by
  ext u
  rw [Subgroup.mem_map, mem_fixSub_zpowers hx₁V]
  constructor
  · rintro ⟨u', hu', rfl⟩
    obtain ⟨hu'U, hu'V⟩ := (mem_fixSub_zpowers hxV).mp hu'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hyU u').mp hu'U, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hyV _).mp hu'V
    have e : (y * u' * y⁻¹)⁻¹ * (y * x * y⁻¹ * (y * u' * y⁻¹) * (y * x * y⁻¹)⁻¹) =
        y * (u'⁻¹ * (x * u' * x⁻¹)) * y⁻¹ := by group
    rw [e]
    exact h1
  · rintro ⟨huU, huV⟩
    refine ⟨y⁻¹ * u * y, (mem_fixSub_zpowers hxV).mpr ⟨?_, ?_⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyU) u).mp huU
      simpa using this
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyV) _).mp huV
      have e : (y⁻¹ * u * y)⁻¹ * (x * (y⁻¹ * u * y) * x⁻¹) =
          y⁻¹ * (u⁻¹ * (y * x * y⁻¹ * u * (y * x * y⁻¹)⁻¹)) * y⁻¹⁻¹ := by group
      rw [e]
      exact h1
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem hasSecNC_three (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {g : G} (hg : g ∈ D)
    (hK₀top : star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = ⊤)
    (hO2 : pCoreOf 2 X ≤ pCoreOf 2 (conjClosure X D)) {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) {U V : Subgroup G}
    (hc : IsTwoChiefFactor (conjClosure X D) U V) (hn : ¬ ⁅U, conjClosure X D⁆ ≤ V) :
    HasSecNC X V U 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hc.2.1.trans hc.2.2.2.1
  have hcomm := commutator_le_of_chief hc
  have hsq := sq_mem_of_chief hc
  have hPc := commutator_pCoreOf_le_of_chief hc
  have hSY : pCoreOf 2 (conjClosure X D) ≤ conjClosure X D := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hYS : conjClosure X D ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure X D) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hSfix : ∀ s ∈ pCoreOf 2 (conjClosure X D), ∀ u ∈ U, u⁻¹ * (s * u * s⁻¹) ∈ V := by
    intro s hs u hu
    have h1 := hPc (Subgroup.commutator_mem_commutator (U.inv_mem hu) hs)
    have e : u⁻¹ * (s * u * s⁻¹) = ⁅u⁻¹, s⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h1
  have hXY : X ≤ conjClosure X D := le_conjClosure X D
  obtain ⟨x, hxX, hx3, -, hgen⟩ := H.exists_x
  have hgenS : ∀ x' ∈ X, ∃ j : ℕ, x' * (x ^ j)⁻¹ ∈ pCoreOf 2 (conjClosure X D) := by
    intro x' hx'
    obtain ⟨j, hj⟩ := hgen x' hx'
    refine ⟨j, hO2 (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (N := X ⊓ pCoreOf 2 (X ⊔ T)) inf_le_left ?_ ?_
      ⟨X.mul_mem hx' (X.inv_mem (X.pow_mem hxX j)), hj⟩)⟩
    · intro y hy
      exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hy)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T) (Subgroup.mem_sup_left hy))
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := hc.2.2.1 (hXY hxX)
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := hc.2.2.2.1 (hXY hxX)
  have hSC : ∀ C : Subgroup G, V ≤ C → C ≤ U →
      pCoreOf 2 (conjClosure X D) ≤ Subgroup.normalizer (C : Set G) := by
    intro C hVC hCU
    refine Main3324.le_normalizer_of_conj fun s hs c hc' => ?_
    have h1 := hVC (hSfix s hs c (hCU hc'))
    have e : s * c * s⁻¹ = c * (c⁻¹ * (s * c * s⁻¹)) := by group
    rw [e]
    exact C.mul_mem hc' h1
  have hXC : ∀ C : Subgroup G, V ≤ C → C ≤ U → x ∈ Subgroup.normalizer (C : Set G) →
      X ≤ Subgroup.normalizer (C : Set G) := by
    intro C hVC hCU hxC x' hx'
    obtain ⟨j, hj⟩ := hgenS x' hx'
    have e : x' = (x' * (x ^ j)⁻¹) * x ^ j := by group
    rw [e]
    exact Subgroup.mul_mem _ (hSC C hVC hCU hj) (Subgroup.pow_mem _ hxC j)
  have hgB : g ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_right hg
  have hq : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨g, hgB⟩ ∈
      star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y₁, hy₁B, hy₁Y, hy₁g⟩ := mem_star_iff.mp hq
  have hXy₁ : conjByElt y₁ X ≤ conjClosure X D := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy₁Y) z).mp (hXY hz)
  have hJ : star (X ⊔ T ⊔ D) B₀ (X ⊔ conjByElt y₁ X) = ⊤ := by
    have h1 := H.star_J_eq_top hA hB hY hYB₀ htop hg hK₀top
    have hXB : X ≤ X ⊔ T ⊔ D := le_sup_left.trans le_sup_left
    have hXgB : conjByElt g X ≤ X ⊔ T ⊔ D :=
      (Subgroup.map_mono le_sup_left).trans (conj_le_B hg)
    rw [star_sup hXB (hXy₁.trans Y_le_B), ← star_conj hy₁B, hy₁g, star_conj hgB,
      ← star_sup hXB hXgB]
    exact h1
  have hYJ : conjClosure X D ≤ (X ⊔ conjByElt y₁ X) ⊔ (conjClosure X D ⊓ B₀) := by
    intro z hz
    have hzB : z ∈ X ⊔ T ⊔ D := Y_le_B hz
    have hz' : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨z, hzB⟩ ∈
        star (X ⊔ T ⊔ D) B₀ (X ⊔ conjByElt y₁ X) := by
      rw [hJ]
      exact Subgroup.mem_top _
    obtain ⟨j, hjB, hjJ, hjz⟩ := mem_star_iff.mp hz'
    have h1 : j⁻¹ * z ∈ B₀ := (QuotientGroup.eq (s := B₀.subgroupOf (X ⊔ T ⊔ D))).mp hjz
    have hjY : j ∈ conjClosure X D := sup_le hXY hXy₁ hjJ
    have e : z = j * (j⁻¹ * z) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hjJ ⟨(conjClosure X D).mul_mem ((conjClosure X D).inv_mem hjY) hz,
      h1⟩
  have hx₁V : y₁ * x * y₁⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    hc.2.2.2.1 ((conjClosure X D).mul_mem ((conjClosure X D).mul_mem hy₁Y (hXY hxX))
      ((conjClosure X D).inv_mem hy₁Y))
  have hinter : fixSub U V (Subgroup.zpowers x) hUV ⊓
      fixSub U V (Subgroup.zpowers (y₁ * x * y₁⁻¹)) hUV ≤ V := by
    rintro u ⟨hu₁, hu₂⟩
    obtain ⟨huU, hux⟩ := (mem_fixSub_zpowers hxV).mp hu₁
    obtain ⟨-, hux₁⟩ := (mem_fixSub_zpowers hx₁V).mp hu₂
    have hzx : Subgroup.zpowers x ≤ stabSub V u :=
      (Subgroup.zpowers_le).mpr (mem_stabSub.mpr ⟨hxV, hux⟩)
    have hzx₁ : Subgroup.zpowers (y₁ * x * y₁⁻¹) ≤ stabSub V u :=
      (Subgroup.zpowers_le).mpr (mem_stabSub.mpr ⟨hx₁V, hux₁⟩)
    have hSst : pCoreOf 2 (conjClosure X D) ≤ stabSub V u := fun s hs =>
      mem_stabSub.mpr ⟨hc.2.2.2.1 (hSY hs), hSfix s hs u huU⟩
    have hst : conjClosure X D ≤ stabSub V u := by
      refine hYJ.trans (sup_le (sup_le ?_ ?_) ?_)
      · intro x' hx'
        obtain ⟨j, hj⟩ := hgenS x' hx'
        have e : x' = (x' * (x ^ j)⁻¹) * x ^ j := by group
        rw [e]
        exact Subgroup.mul_mem _ (hSst hj) (hzx (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j))
      · rintro _ ⟨x', hx', rfl⟩
        obtain ⟨j, hj⟩ := hgenS x' hx'
        have hs' : y₁ * (x' * (x ^ j)⁻¹) * y₁⁻¹ ∈ pCoreOf 2 (conjClosure X D) :=
          (Subgroup.mem_normalizer_iff.mp (hYS hy₁Y) _).mp hj
        have e : (MulAut.conj y₁).toMonoidHom x' =
            (y₁ * (x' * (x ^ j)⁻¹) * y₁⁻¹) * (y₁ * x * y₁⁻¹) ^ j := by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow]
          group
        rw [e]
        exact Subgroup.mul_mem _ (hSst hs')
          (hzx₁ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j))
      · intro z hz
        exact hSst (inf_pCoreOf_le ⟨hz.1, hle hz⟩)
    have hfix : u ∈ fixSub U V (conjClosure X D) hUV :=
      mem_fixSub.mpr ⟨huU, fun z hz => (mem_stabSub.mp (hst hz)).2⟩
    have heq : fixSub U V (conjClosure X D) hUV = V := by
      by_contra hne
      apply hn
      exact commutator_le_of_fixSub_eq (chief_eq hc (le_fixSub hUV hc.1.le hc.2.2.2.1)
        (fixSub_le hUV) ((le_inf (le_inf hc.2.2.1 hc.2.2.2.1) Subgroup.le_normalizer).trans
          (le_normalizer_fixSub hUV)) hne)
    rw [← heq]
    exact hfix
  have hconj := map_conj_fixSub hUV (hc.2.2.1 hy₁Y) (hc.2.2.2.1 hy₁Y) hxV hx₁V
  have hUmap : U.map (MulAut.conj y₁).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hc.2.2.1 hy₁Y)
  have hidx₂ : (fixSub U V (Subgroup.zpowers (y₁ * x * y₁⁻¹)) hUV).relIndex U =
      (fixSub U V (Subgroup.zpowers x) hUV).relIndex U := by
    have h1 := Subgroup.relIndex_map_map_of_injective (fixSub U V (Subgroup.zpowers x) hUV) U
      (f := (MulAut.conj y₁).toMonoidHom) (MulAut.conj y₁).injective
    rw [hUmap, hconj] at h1
    exact h1
  have hV := le_antisymm hinter (le_inf (le_fixSub hUV hc.1.le
    ((Subgroup.zpowers_le).mpr hxV)) (le_fixSub hUV hc.1.le ((Subgroup.zpowers_le).mpr hx₁V)))
  have h10 := H.two_pow_ten_le hA hB hY hYB₀ htop hle hp hp24 hL hc hn
  have hle' := Subgroup.relIndex_inf_le (H := fixSub U V (Subgroup.zpowers x) hUV)
    (K := fixSub U V (Subgroup.zpowers (y₁ * x * y₁⁻¹)) hUV) (L := U)
  rw [hV, hidx₂] at hle'
  have hidx : 4 ^ 2 < (fixSub U V (Subgroup.zpowers x) hUV).relIndex U := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul h h
    omega
  exact hasSecNC_of_lt hx3 hxU hxX hcomm hsq hXC 2 V le_rfl hc.1.le hUV
    (hXY.trans hc.2.2.2.1) hidx

theorem hasNoncentralTwoChief_Y (hB : IsB₀ X T D B₀) (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) : HasNoncentralTwoChief (conjClosure X D) 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnc
  have hQY : pCoreOf 2 (conjClosure X D) ≤ conjClosure X D := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have h0 : NCAtMost (conjClosure X D) ⊥ (pCoreOf 2 (conjClosure X D)) 0 := fun h =>
    hnc (Chief3323.hasNoncentralTwoChief_iff.mpr (h.mono le_rfl hQY))
  have hbot : conjClosure X D ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun _ _ =>
    Subgroup.mem_normalizer_iff.mpr fun z => by simp
  have hQc := Gen3324.commutator_le_of_ncAtMost H.oTwoUpper_Y bot_le hQY hbot
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    h0
  have hYP : ⁅conjClosure X D, pCoreOf 2 (X ⊔ T ⊔ D)⁆ ≤ pCoreOf 2 (conjClosure X D) := by
    refine (le_inf (commutator_le_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans H.hBY)) ?_).trans
      (inf_pCoreOf_le (X := X) (T := T) (D := D))
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer
      (Y_le_B.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have h1 : ⁅⁅conjClosure X D, pCoreOf 2 (X ⊔ T ⊔ D)⁆, conjClosure X D⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hYP le_rfl).trans hQc)
  have h2 : ⁅⁅pCoreOf 2 (X ⊔ T ⊔ D), conjClosure X D⁆, conjClosure X D⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (pCoreOf 2 (X ⊔ T ⊔ D))]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [perfect_of_mem_cComp hY] at h3
  have hchar := charTwo_of_inH' H.h.qtke H.h.sylow H.hB
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  apply hYB₀
  intro y hy
  have hyC : y ∈ Subgroup.centralizer (pCoreOf 2 (X ⊔ T ⊔ D) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3) hy
  have h4 := hchar ⟨Y_le_B hy, hyC⟩
  rw [← hT₀] at h4
  exact h4.2

omit H in
theorem pCoreOf_Y_le (hBY : X ⊔ T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G)) :
    pCoreOf 2 (conjClosure X D) ≤ pCoreOf 2 (X ⊔ T ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans Y_le_B)
    (hBY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem le_normalizer_X_of_chief (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {U V : Subgroup G}
    (hc : IsTwoChiefFactor (conjClosure X D) U V) : U ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  refine (H.le_pCoreOf_of_chief hA hB hY hYB₀ htop hle hc).trans ((pCoreOf_Y_le H.hBY).trans ?_)
  rw [← hT₀]
  exact inf_le_left.trans H.hTX

theorem concl4 (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D)) (hYB₀ : ¬ conjClosure X D ≤ B₀)
    (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {g : G} (hg : g ∈ D)
    (hK₀top : star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = ⊤)
    (hO2 : pCoreOf 2 X ≤ pCoreOf 2 (conjClosure X D)) {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) :
    HasNoncentralTwoChief X 3 := by
  obtain ⟨A, B', hAB, -⟩ := H.hasNoncentralTwoChief_Y hB hY hYB₀
  exact hasNoncentralTwoChief_of_hasSecNC
    (H.hasSecNC_three hA hB hY hYB₀ htop hle hg hK₀top hO2 hp hp24 hL (hAB 0).1 (hAB 0).2)
    (H.le_normalizer_X_of_chief hA hB hY hYB₀ htop hle (hAB 0).1)

end Hyp3320

end S3320

end CFSG.Quasithin.H13
