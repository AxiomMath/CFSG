module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSevenTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ug
public import CFSG.GroupTheory.CoprimeCovering

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_eq_one_commute_of_commute_bar {M : Subgroup G} {b : ↥M}
    (hb : Odd (orderOf b)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : Bar2 M} (hx : x ≠ 1)
    (hxq : x ^ q = 1)
    (hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) b * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥M) b) :
    ∃ z : ↥M, z * b = b * z ∧ z ^ q = 1 ∧ z ≠ 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) z ∈ Subgroup.zpowers x := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥M := CFSG.pCore 2 ↥M
  have hNnormal : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hN2.exists_card_eq
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N x
  have hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(Subgroup.zpowers b)) := by
    rw [hk, Nat.card_zpowers]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hb)
  have hxR : ∀ r ∈ Subgroup.zpowers b, ⁅y, r⁆ ∈ N := by
    rintro r ⟨j, rfl⟩
    refine (QuotientGroup.eq_one_iff ⁅y, b ^ j⁆).1 ?_
    change (QuotientGroup.mk' N) ⁅y, b ^ j⁆ = 1
    rw [map_commutatorElement, map_zpow, hy, commutatorElement_eq_one_iff_mul_comm]
    exact (Commute.zpow_right hxb.symm j).eq
  haveI : Group.IsNilpotent ↥N := hN2.isNilpotent
  obtain ⟨y', -, hy'comm, hy'N⟩ :=
    CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem (X := ⊤) (N := N)
      (R := Subgroup.zpowers b) le_top (Subgroup.Normal.subgroupOf hNnormal ⊤)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hNnormal]; exact le_top) inferInstance hcop
      (x := y) (Subgroup.mem_top y) hxR
  have hπy' : QuotientGroup.mk' N y' = x := by
    have h1 : QuotientGroup.mk' N (y⁻¹ * y') = 1 := (QuotientGroup.eq_one_iff _).2 hy'N
    rw [map_mul, map_inv, hy] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hy'qN : y' ^ q ∈ N := by
    refine (QuotientGroup.eq_one_iff (y' ^ q)).1 ?_
    change (QuotientGroup.mk' N) (y' ^ q) = 1
    rw [map_pow, hπy', hxq]
  have hpow : (y' ^ q) ^ (2 ^ k) = 1 := by
    have h1 : (⟨y' ^ q, hy'qN⟩ : ↥N) ^ Nat.card ↥N = 1 := pow_card_eq_one'
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have hπz : QuotientGroup.mk' N (y' ^ (2 ^ k)) = x ^ (2 ^ k) := by
    rw [map_pow, hπy']
  have hπzne : QuotientGroup.mk' N (y' ^ (2 ^ k)) ≠ 1 := by
    rw [hπz]
    intro hpowx
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hpowx
    rw [orderOf_eq_prime hxq hx] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  refine ⟨y' ^ (2 ^ k), ?_, ?_, ?_, ?_⟩
  · exact (show Commute y' b from hy'comm b (Subgroup.mem_zpowers b)).pow_left (2 ^ k)
  · rw [pow_right_comm y' (2 ^ k) q, hpow]
  · exact fun hz => hπzne (by rw [hz]; simp)
  · rw [hπz]
    exact Subgroup.npow_mem_zpowers x (2 ^ k)

theorem natCard_barPreimage_coprime {M : Subgroup G} {Y : Subgroup (Bar2 M)} {q p : ℕ}
    (hYq : IsPGroup q ↥Y) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2) :
    Nat.Coprime p (Nat.card ↥(barPreimage M Y)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22p22u_card_barPreimage M Y]
  obtain ⟨k, hk⟩ := (uc22p21c_isPGroup_pCoreOf M).exists_card_eq
  obtain ⟨l, hl⟩ := hYq.exists_card_eq
  rw [hk, hl]
  exact Nat.Coprime.mul_right
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k)
    (((Nat.coprime_primes hp hq).mpr hpq).pow_right l)

theorem barPreimage_le_relPPrimeCore {M : Subgroup G} {Y : Subgroup (Bar2 M)} {q p : ℕ}
    (hY : Y.Normal) (hYq : IsPGroup q ↥Y) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) : barPreimage M Y ≤ CFSG.Open.relPPrimeCore p M := by
  haveI : Y.Normal := hY
  change barPreimage M Y ≤
    sSup {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧ Nat.Coprime p (Nat.card N)}
  refine le_sSup ⟨uc22p21c_barPreimage_le M Y, ?_,
    natCard_barPreimage_coprime hYq hp hq hpq hp2⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (uc22p21c_barPreimage_le M Y)).mpr
    uc22p22u_barPreimage_normalizes

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem mem_uniqueSet_of_le_barPreimage (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h71 : S23_7_1 D Ch) {p : ℕ}
    (hp : p ∈ D.sig) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqsig : q ∉ D.sig)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) {X : Subgroup G} (hXne : X ≠ ⊥) (hXq : IsPGroup q ↥X)
    (hXP : X ≤ barPreimage D.M Dbar) : X ∈ uniqueSet D.M := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Dbar.Normal := hDn
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hpq : p ≠ q := fun h => hqsig (h ▸ hp)
  let P : Subgroup G := barPreimage D.M Dbar
  have hPM : P ≤ D.M := uc22p21c_barPreimage_le D.M Dbar
  have hPn : (P.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr
      (uc22p22u_barPreimage_normalizes (M := D.M) (D := Dbar))
  have hPO : P ≤ CFSG.Open.relPPrimeCore p D.M :=
    barPreimage_le_relPPrimeCore hDn hDq hpp hq hpq hp2
  have hXPq : IsPGroup q ↥(X.subgroupOf P) :=
    hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXP).symm
  obtain ⟨Q, hXQ⟩ := hXPq.exists_le_sylow
  let Q0 : Subgroup G := (Q : Subgroup ↥P).map P.subtype
  have hQ0syl : CFSG.ABGLocalTools.IsSylowOf q Q0 P := ⟨Q, rfl⟩
  have hXQ0 : X ≤ Q0 := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hXP hy⟩, hXQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  obtain ⟨hQ0bar, hQ0inf⟩ := uc22p22u_sylow_barPreimage hq hq2 hDq hQ0syl
  have hQ0M : Q0 ≤ D.M := hQ0syl.le.trans hPM
  have hprops := uc22p22u_lift_props (r := q) hQ0bar hQ0inf hQ0M
  have hQ0nc : ¬ IsCyclic ↥Q0 := hprops.2.2 hDnc
  have hQ0exp : ∀ y ∈ Q0, y ^ q = 1 := hprops.1 hDexp
  have hQ0cl : ⁅⁅Q0, Q0⁆, Q0⁆ = ⊥ := hprops.2.1 hDcl
  have hQ0le : Q0 ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) :=
    le_inf hQ0M Subgroup.le_normalizer
  have hQ0n : (Q0.subgroupOf (D.M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0le).mpr inf_le_right
  have h71' := h71 h1930 c q hq hq2 Q0 hQ0M hQ0syl.isPGroup hQ0nc hQ0exp hQ0cl
    p hp P hPM hPn hPO Q0 hQ0syl hQ0le hQ0n
  exact mem_uniqueSet_of_le_of_inf_conj_eq_bot hXQ0 (hXP.trans hPM) hXne h71'

theorem exists_zpowers_of_commute_bar (c : Ctx23L D Ch) {b : ↥D.M} (hb : (b : G) ∈ c.B)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : Bar2 D.M} (hx1 : x ≠ 1)
    (hxq : x ^ q = 1)
    (hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b) :
    ∃ z : ↥D.M, QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z ∈ Subgroup.zpowers x ∧
      Subgroup.zpowers (z : G) ≠ ⊥ ∧ IsPGroup q (Subgroup.zpowers (z : G)) ∧
      Subgroup.zpowers (z : G) ≤ D.M ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hboddG : Odd (orderOf (b : G)) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 (c.hle hb)
  have hbodd : Odd (orderOf b) := by simpa only [Subgroup.orderOf_coe] using hboddG
  obtain ⟨z, hzb, hzq, hzne, hzmem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar hbodd hq hq2 hx1 hxq hxb
  have hXne : Subgroup.zpowers (z : G) ≠ ⊥ := by
    intro hbot
    have hmem : (z : G) ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers (z : G)
    exact hzne (Subtype.ext (by simpa using hmem))
  have hXq : IsPGroup q (Subgroup.zpowers (z : G)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    have hcard : Nat.card ↥(Subgroup.zpowers (z : G)) = orderOf (z : G) :=
      Nat.card_zpowers (z : G)
    rw [hcard, Subgroup.orderOf_coe]
    simpa using orderOf_dvd_of_pow_eq_one hzq
  have hXle : Subgroup.zpowers (z : G) ≤
      D.M ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨z.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (congrArg Subtype.val hzb).symm
  exact ⟨z, hzmem, hXne, hXq, hXle⟩

theorem eq_one_of_commute_bar_of_mem_sig (h1930 : H1930 D) (h54 : S23_5_4 D Ch)
    (h6 : S23_6 D Ch) {b : ↥D.M} (hb : (b : G) ∈ c.B)
    (hbZ : (b : G) ∉ Subgroup.centralizer (D.Z : Set G)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqsig : q ∈ D.sig) {x : Bar2 D.M} (hxq : x ^ q = 1)
    (hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b) :
    x = 1 := by
  classical
  by_cases hx1 : x = 1
  · exact hx1
  obtain ⟨z, hzmem, hXne, hXq, hXle⟩ := exists_zpowers_of_commute_bar c hb hq hq2 hx1 hxq hxb
  have hfacts := (h54 h1930 c (b : G) hb hbZ).2 q hq
    (Subgroup.zpowers (z : G)) hXne hXq hXle
  exact absurd ((h6 h1930 c) ▸ hqsig) hfacts.2

theorem pCore_inf_centralizer_bar_eq_bot_of_mem_sig (h1930 : H1930 D) (h54 : S23_5_4 D Ch)
    (h6 : S23_6 D Ch) {b : ↥D.M} (hb : (b : G) ∈ c.B)
    (hbZ : (b : G) ∉ Subgroup.centralizer (D.Z : Set G)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqsig : q ∈ D.sig) :
    CFSG.pCore q (Bar2 D.M) ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b} : Set (Bar2 D.M)) = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b :=
    (Subgroup.mem_centralizer_iff.mp hx.2) _ (Set.mem_singleton _)
  have hq_dvd : q ∣ orderOf x := by
    simpa only [Subgroup.orderOf_mk] using
      (CFSG.pCore_isPGroup (p := q) (G := Bar2 D.M)).dvd_orderOf
        (g := (⟨x, hx.1⟩ : ↥(CFSG.pCore q (Bar2 D.M))))
        (fun h => hxne (congrArg Subtype.val h))
  let y : Bar2 D.M := x ^ (orderOf x / q)
  have hyord : orderOf y = q := orderOf_pow_orderOf_div (orderOf_pos x).ne' hq_dvd
  have hyfacts := (orderOf_eq_prime_iff (x := y) (p := q)).mp hyord
  have hyq : y ^ q = 1 := hyfacts.1
  have hyne : y ≠ 1 := hyfacts.2
  have hyb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b :=
    (Commute.pow_right (show Commute _ x from hxb) _).eq
  exact hyne (eq_one_of_commute_bar_of_mem_sig c h1930 h54 h6 hb hbZ hq hq2 hqsig hyq hyb)

theorem eq_one_of_commute_bar (h1930 : H1930 D) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) {b : ↥D.M} (hb : (b : G) ∈ c.B)
    (hbZ : (b : G) ∉ Subgroup.centralizer (D.Z : Set G)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) {x : Bar2 D.M} (hx : x ∈ Dbar)
    (hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b) :
    x = 1 := by
  classical
  by_cases hqsig : q ∈ D.sig
  · exact eq_one_of_commute_bar_of_mem_sig c h1930 h54 h6 hb hbZ hq hq2 hqsig
      (hDexp x hx) hxb
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hx1
  obtain ⟨z, hzmem, hXne, hXq, hXle⟩ :=
    exists_zpowers_of_commute_bar c hb hq hq2 hx1 (hDexp x hx) hxb
  have hXfacts := (h54 h1930 c (b : G) hb hbZ).2 q hq
    (Subgroup.zpowers (z : G)) hXne hXq hXle
  have hXU : Subgroup.zpowers (z : G) ∉ uniqueSet D.M := hXfacts.1
  obtain ⟨p, hp⟩ := hsig
  have hzP : (z : G) ∈ barPreimage D.M Dbar :=
    uc22p21c_mem_barPreimage.2 ⟨z.2, (Subgroup.zpowers_le.mpr hx) hzmem⟩
  have hXP : Subgroup.zpowers (z : G) ≤ barPreimage D.M Dbar := Subgroup.zpowers_le.mpr hzP
  exact hXU (mem_uniqueSet_of_le_barPreimage c h1930 h71 hp hq hq2 hqsig hDn hDq hDnc hDexp
    hDcl hXne hXq hXP)

theorem centralizer_bar_inf_eq_bot (h1930 : H1930 D) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) {b : ↥D.M} (hb : (b : G) ∈ c.B)
    (hbZ : (b : G) ∉ Subgroup.centralizer (D.Z : Set G)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) :
    Dbar ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b} : Set (Bar2 D.M)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute_bar c h1930 h54 h6 h71 hsig hb hbZ hq hq2 hDn hDq hDnc hDexp hDcl
    hx.1 ((Subgroup.mem_centralizer_iff.mp hx.2) (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b)
      (Set.mem_singleton _))

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
