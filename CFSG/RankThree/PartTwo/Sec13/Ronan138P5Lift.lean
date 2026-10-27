module

import CFSG.RankThree.PartTwo.Sec8.Hering88FCoprime
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev rho (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)

theorem false_of_mem_partTwoE_lt (hEF : partTwoF G = partTwoE G) {B B' : Subgroup G}
    (hB : B ∈ partTwoE G) (hB' : CFSG.Assembly.IsElemAbelian 3 B') (hBB' : B ≤ B')
    (hne : B ≠ B') : False := by
  rw [← hEF] at hB
  exact hne (hB.2.1 B' hB' hBB').symm

theorem exists_mem_not_mem_zpowers {P₀ : Subgroup G} (hP₀9 : Nat.card P₀ = 9) {c : G}
    (hc3 : c ^ 3 = 1) : ∃ x ∈ P₀, x ∉ Subgroup.zpowers c := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hle : Nat.card P₀ ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le h
  rw [Nat.card_zpowers] at hle
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
  omega

theorem forall_commute_of_commute {P₀ : Subgroup G} (hP₀e : CFSG.Assembly.IsElemAbelian 3 P₀)
    (hP₀9 : Nat.card P₀ = 9) {c x : G} (hc : orderOf c = 3) (hcP : c ∈ P₀) (hxP : x ∈ P₀)
    (hxc : x ∉ Subgroup.zpowers c) {g : G} (hgc : g * c = c * g) (hgx : g * x = x * g) :
    ∀ p ∈ P₀, g * p = p * g := by
  have hx3 : x ^ 3 = 1 := hP₀e.2 x hxP
  have hx1 : x ≠ 1 := fun h => hxc (h ▸ Subgroup.one_mem _)
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers c ⊓ Subgroup.zpowers x : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Subgroup.zpowers c ⊓ Subgroup.zpowers x ≤
        Subgroup.zpowers x)
      rwa [Nat.card_zpowers, hx] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hx])
      have hxm : x ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxc hxm.1
  have hcomm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hxc' : x * c = c * x :=
      congrArg Subtype.val (hP₀e.1.is_comm.comm ⟨x, hxP⟩ ⟨c, hcP⟩)
    exact (Commute.zpow_left (show Commute c x from hxc'.symm) k).eq
  have hcard := Sec6.card_sup_mul_card_inf hcomm
  rw [inf_comm, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hx, hc]
    at hcard
  set H : Subgroup G := P₀ ⊓ Subgroup.centralizer ({g} : Set G) with hH
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hgx.symm⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨hcP, Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm⟩
  have hHP : H = P₀ :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by
      rw [hP₀9]
      calc 9 = Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers c : Subgroup G) := by omega
        _ ≤ Nat.card H := Subgroup.card_le_of_le hle)
  intro p hp
  have hpH : p ∈ H := hHP ▸ hp
  exact (Subgroup.mem_centralizer_singleton_iff.mp hpH.2).symm

theorem exists_pow_lift_three {L : Subgroup G} (m : L) {d : L ⧸ aschbacherSolvableCore 3 L}
    (hm : (m : L ⧸ aschbacherSolvableCore 3 L) = d) (hd3 : d ^ 3 = 1) :
    ∃ k : ℕ, ((m ^ k : L) : L ⧸ aschbacherSolvableCore 3 L) = d ∧ (m ^ k) ^ 3 = 1 := by
  set n := orderOf m with hn
  have hn0 : n ≠ 0 := (orderOf_pos m).ne'
  have hnab : 3 ^ n.factorization 3 * (n / 3 ^ n.factorization 3) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 3
  have hcop : Nat.Coprime 3 (n / 3 ^ n.factorization 3) :=
    Nat.coprime_ordCompl Nat.prime_three hn0
  set a := n.factorization 3 with ha
  set b := n / 3 ^ a with hb
  have h3b : ¬ 3 ∣ b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hbb : b * b % 3 = 1 := by
    have : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  refine ⟨b * b, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, hm, ← Nat.mod_add_div (b * b) 3, pow_add, pow_mul, hd3, one_pow,
      mul_one, hbb, pow_one]
  · set t : L := (m ^ (b * b)) ^ 3 with ht
    have htθ : t ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, ht, QuotientGroup.mk_pow, QuotientGroup.mk_pow, hm,
        ← pow_mul, mul_comm, pow_mul, hd3, one_pow]
    have ht3a : t ^ (3 ^ a) = 1 := by
      rw [ht, ← pow_mul, ← pow_mul]
      have : b * b * (3 * 3 ^ a) = n * (3 * b) := by rw [← hnab]; ring
      rw [this, pow_mul, hn, pow_orderOf_eq_one, one_pow]
    have h1 : orderOf t ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ht3a
    have h2 : orderOf t ∣ Nat.card (aschbacherSolvableCore 3 L) := by
      have := orderOf_dvd_natCard (⟨t, htθ⟩ : aschbacherSolvableCore 3 L)
      rwa [Subgroup.orderOf_mk] at this
    have hcop2 : Nat.Coprime (3 ^ a) (Nat.card (aschbacherSolvableCore 3 L)) :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (KFacts.not_three_dvd_card_aschbacherSolvableCore L))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 h1 h2)

theorem mem_normalizer_inf_centralizer {L : Subgroup G} {x y : G}
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hxy : x * y = y * x) :
    y ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ h : G, h * x = x * h ↔ y * h * y⁻¹ * x = x * (y * h * y⁻¹) := by
    intro h
    have hx' : y⁻¹ * x * y = x := by
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [hxy]
        _ = x := by group
    constructor
    · intro hh
      calc y * h * y⁻¹ * x = y * (h * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * (h * x) * y⁻¹ := by rw [hx']
        _ = y * (x * h) * y⁻¹ := by rw [hh]
        _ = y * ((y⁻¹ * x * y) * h) * y⁻¹ := by rw [hx']
        _ = x * (y * h * y⁻¹) := by group
    · intro hh
      calc h * x = h * (y⁻¹ * x * y) := by rw [hx']
        _ = y⁻¹ * (y * h * y⁻¹ * x) * y := by group
        _ = y⁻¹ * (x * (y * h * y⁻¹)) * y := by rw [hh]
        _ = (y⁻¹ * x * y) * h := by group
        _ = x * h := by rw [hx']
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr ((Subgroup.mem_normalizer_iff.mp hyN) h) (key h)

noncomputable abbrev preimageIn (L : Subgroup G) (V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    Subgroup G :=
  (V.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map L.subtype

theorem mem_preimageIn {L : Subgroup G} {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} {g : G} :
    g ∈ preimageIn L V ↔ ∃ hg : g ∈ L,
      ((⟨g, hg⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈ V := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hg, hV⟩
    exact ⟨⟨g, hg⟩, hV, rfl⟩

theorem mem_normalizer_preimageIn {L : Subgroup G} {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hV : ∀ v, v ∈ V ↔ rho L ⟨g, hg⟩ v ∈ V) :
    g ∈ Subgroup.normalizer (preimageIn L V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_preimageIn, mem_preimageIn]
  constructor
  · rintro ⟨hhL, hhV⟩
    have hL' : g * h * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg h).mp hhL
    refine ⟨hL', ?_⟩
    have hrho : rho L ⟨g, hg⟩ ((⟨h, hhL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨g * h * g⁻¹, hL'⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := rfl
    rw [← hrho]
    exact (hV _).mp hhV
  · rintro ⟨hL', hV'⟩
    have hhL : h ∈ L := (Subgroup.mem_normalizer_iff.mp hg h).mpr hL'
    refine ⟨hhL, ?_⟩
    have hrho : rho L ⟨g, hg⟩ ((⟨h, hhL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨g * h * g⁻¹, hL'⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := rfl
    rw [← hrho] at hV'
    exact (hV _).mpr hV'

theorem card_preimageIn {L : Subgroup G} {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hV2 : IsPGroup 2 V) :
    ¬ 3 ∣ Nat.card (preimageIn L V) ∧ (V ≠ ⊥ → 2 ∣ Nat.card (preimageIn L V)) := by
  have hcard : Nat.card (preimageIn L V) =
      Nat.card (V.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) :=
    Subgroup.card_map_of_injective L.subtype_injective
  set H := V.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) with hH
  set f : H →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp H.subtype with hf
  have hrange : f.range = V := by
    ext v
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hv
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) v
      exact ⟨⟨l, hv⟩, rfl⟩
  have hker : f.ker.map H.subtype ≤ aschbacherSolvableCore 3 L := by
    rintro _ ⟨h, hh, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hh
  have hk : ¬ 3 ∣ Nat.card f.ker := by
    intro h3
    apply KFacts.not_three_dvd_card_aschbacherSolvableCore L
    refine h3.trans ?_
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le hker
  have hr : ¬ 3 ∣ Nat.card f.range := by
    rw [hrange]
    intro h3
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hmul := Subgroup.card_ker_mul_card_range f
  refine ⟨?_, fun hV1 => ?_⟩
  · rw [hcard, ← hmul]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hk h
    · exact hr h
  · rw [hcard, ← hmul]
    refine Dvd.dvd.mul_left ?_ _
    rw [hrange]
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hk
      exact hV1 (Subgroup.eq_bot_of_card_eq V hk)
    · exact dvd_pow_self 2 hpos.ne'

theorem false_of_lift (hEF : partTwoF G = partTwoE G) {c : G} {L P₀ : Subgroup G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc : orderOf c = 3) (hcP : c ∈ P₀)
    (hP₀L : P₀ ≤ Sec4.thetaQuotCentralizer L) (hP₀e : CFSG.Assembly.IsElemAbelian 3 P₀)
    (hP₀9 : Nat.card P₀ = 9) {y : G} (hyP : ∀ p ∈ P₀, p * y = y * p)
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hy3 : y ^ 3 = 1)
    (hy1 : rho L ⟨y, hyN⟩ ≠ 1)
    {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hyV : ∀ v ∈ V, rho L ⟨y, hyN⟩ v ∈ V)
    {d : L ⧸ aschbacherSolvableCore 3 L} (hd3 : d ^ 3 = 1) (hdy : rho L ⟨y, hyN⟩ d = d)
    (hdn : ∀ k : ℕ, rho L ⟨y, hyN⟩ ^ k ≠ MulAut.conj d) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₀N : ∀ p ∈ P₀, p ∈ Subgroup.normalizer (L : Set G) := fun p hp => by
    obtain ⟨q, -, rfl⟩ := hP₀L hp
    exact q.2
  have hP₀1 : ∀ p (hp : p ∈ P₀), rho L ⟨p, hP₀N p hp⟩ = 1 := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := hP₀L hp
    exact hq
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  obtain ⟨x, hxP, hxc⟩ := exists_mem_not_mem_zpowers hP₀9 hc3
  have hx3 : x ^ 3 = 1 := hP₀e.2 x hxP
  have hxN := hP₀N x hxP
  have hxy : x * y = y * x := hyP x hxP
  have hrho3 : rho L ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective d
  obtain ⟨m₁, hm₁x, hm₁⟩ := Sec8.Hering88F.exists_mem_centralizer_of_fixed (Y := L) (M := L)
    le_rfl hxN hxN hx3 m₀.2 (by
      have h1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩) = 1 := hP₀1 x hxP
      rw [h1]
      rfl)
  have hm₁d : ((⟨m₁, m₁.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = d := by
    rw [← hm₀]
    exact hm₁
  obtain ⟨m₂, hm₂y, hm₂⟩ := Sec8.Hering88F.exists_mem_centralizer_of_fixed
    (Y := L) (M := L ⊓ Subgroup.centralizer ({x} : Set G)) inf_le_left hyN
    (mem_normalizer_inf_centralizer hyN hxy) hy3 (m := (m₁ : G)) ⟨m₁.2, hm₁x⟩ (by
      change rho L ⟨y, hyN⟩ ((⟨m₁, m₁.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = _
      rw [hm₁d, hdy])
  set m : L := ⟨m₂, m₂.2.1⟩ with hmdef
  have hmd : (m : L ⧸ aschbacherSolvableCore 3 L) = d := by
    rw [← hm₁d]
    exact hm₂
  obtain ⟨k, hkd, hk3⟩ := exists_pow_lift_three m hmd hd3
  set dt : G := ((m ^ k : L) : G) with hdt
  have hdtL : dt ∈ L := (m ^ k).2
  have hdt3 : dt ^ 3 = 1 := by
    rw [hdt, ← Subgroup.coe_pow, hk3, OneMemClass.coe_one]
  have hm₂x : (m₂ : G) * x = x * m₂ := Subgroup.mem_centralizer_singleton_iff.mp m₂.2.2
  have hm₂y' : (m₂ : G) * y = y * m₂ := Subgroup.mem_centralizer_singleton_iff.mp hm₂y
  have hdtx : dt * x = x * dt := by
    rw [hdt, Subgroup.coe_pow]
    exact (Commute.pow_left (show Commute (m₂ : G) x from hm₂x) k).eq
  have hdty : dt * y = y * dt := by
    rw [hdt, Subgroup.coe_pow]
    exact (Commute.pow_left (show Commute (m₂ : G) y from hm₂y') k).eq
  have hdtc : dt * c = c * dt := Subgroup.mem_centralizer_singleton_iff.mp (hLc hdtL)
  have hdtP : ∀ p ∈ P₀, dt * p = p * dt :=
    forall_commute_of_commute hP₀e hP₀9 hc hcP hxP hxc hdtc hdtx
  have hyB : Subgroup.zpowers y ≤ Subgroup.normalizer (P₀ : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun p hp => ?_)
    exact hyP p hp
  have hyP' : ∀ p ∈ P₀, ∀ z ∈ Subgroup.zpowers y, p * z = z * p := by
    intro p hp z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute p y from hyP p hp) j).eq
  set B : Subgroup G := P₀ ⊔ Subgroup.zpowers y with hBdef
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    CFSG.Open.IsElemAbelian.sup_of_commute hP₀e (CFSG.Open.isElemAbelian_zpowers hy3) hyP'
  have hyP₀ : y ∉ P₀ := fun hy => hy1 (hP₀1 y hy)
  have hy1' : y ≠ 1 := fun h => hyP₀ (h ▸ P₀.one_mem)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1'
  have hinf : Subgroup.zpowers y ⊓ P₀ = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers y ⊓ P₀ : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers y ⊓ P₀ ≤ Subgroup.zpowers y)
      rwa [Nat.card_zpowers, hyo] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers y ⊓ P₀ = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hyo])
      have hym : y ∈ Subgroup.zpowers y ⊓ P₀ := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact hyP₀ hym.2
  have hB27 : Nat.card B = 27 := by
    have h := Sec6.card_sup_mul_card_inf hyB
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hyo, hP₀9, sup_comm] at h
    rw [hBdef]
    omega
  have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun p hp => hP₀N p hp) ((Subgroup.zpowers_le).mpr hyN)
  set Y := preimageIn L V with hYdef
  have hyVinv : ∀ v, v ∈ V ↔ rho L ⟨y, hyN⟩ v ∈ V := by
    intro v
    refine ⟨hyV v, fun hv => ?_⟩
    have h2 : rho L ⟨y, hyN⟩ (rho L ⟨y, hyN⟩ (rho L ⟨y, hyN⟩ v)) = v := by
      have := congrArg (fun σ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => σ v) hrho3
      simpa [pow_succ, MulAut.mul_apply] using this
    rw [← h2]
    exact hyV _ (hyV _ hv)
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le (fun p hp => mem_normalizer_preimageIn (hP₀N p hp) ?_) ?_
    · intro v
      rw [hP₀1 p hp]
      rfl
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_preimageIn hyN hyVinv
  obtain ⟨hY3, hY2⟩ := card_preimageIn (L := L) hV2
  have hB3 : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hBe.2 g g.2)⟩
  obtain ⟨S, hSyl, -, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    (r := 3) (q := 2) Nat.prime_three Nat.prime_two hB3 hY3 hBY bot_le IsPGroup.of_bot
    (by intro b _; exact Subgroup.mem_normalizer_iff.mpr fun h => by simp)
  have hSne : S ≠ ⊥ := by
    intro hS
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 (hY2 hV)
    have hP : Subgroup.zpowers (t : G) = S := by
      refine hSyl.2.2 _ ?_ ?_ (hS ▸ bot_le)
      · rw [Subgroup.zpowers_le]
        exact t.2
      · refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
    have ht1 : (t : G) ∈ (⊥ : Subgroup G) := hS ▸ hP ▸ Subgroup.mem_zpowers (t : G)
    have : t = 1 := Subtype.ext (Subgroup.mem_bot.mp ht1)
    rw [this, orderOf_one] at ht
    omega
  have hBE : B ∈ partTwoE G := ⟨hBe, hB27, S, hSne, hSyl.2.1, hBS⟩
  set B' : Subgroup G := B ⊔ Subgroup.zpowers dt with hB'def
  have hBdt : ∀ b ∈ B, ∀ z ∈ Subgroup.zpowers dt, b * z = z * b := by
    have hBC : B ≤ Subgroup.centralizer ({dt} : Set G) := by
      refine sup_le (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hdtP p hp).symm) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hdty.symm
    intro b hb z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hbd : b * dt = dt * b := Subgroup.mem_centralizer_singleton_iff.mp (hBC hb)
    exact (Commute.zpow_right (show Commute b dt from hbd) j).eq
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' :=
    CFSG.Open.IsElemAbelian.sup_of_commute hBe (CFSG.Open.isElemAbelian_zpowers hdt3) hBdt
  refine false_of_mem_partTwoE_lt hEF hBE hB'e le_sup_left fun hBB' => ?_
  have hdtB : dt ∈ B := hBB' ▸ (le_sup_right : Subgroup.zpowers dt ≤ B') (Subgroup.mem_zpowers dt)
  have hmem : dt ∈ (P₀ : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P₀ (Subgroup.zpowers y) hyB]
    exact hdtB
  obtain ⟨p, hp, z, hz, hpz⟩ := hmem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hzN : y ^ j ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hyN j
  have hdtN : dt ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdtL
  have hprod : (⟨dt, hdtN⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨p, hP₀N p hp⟩ * ⟨y, hyN⟩ ^ j := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hpz.symm
  have hconj : rho L ⟨dt, hdtN⟩ = MulAut.conj d := by
    have := KFacts.thetaQuotMulAut_compAction_of_mem hdtL hdtN
    change Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨dt, hdtN⟩) = _
    rw [this, ← hkd]
    rfl
  rw [hprod, map_mul, hP₀1 p hp, one_mul, map_zpow] at hconj
  have hmod : rho L ⟨y, hyN⟩ ^ j = rho L ⟨y, hyN⟩ ^ (j % 3).toNat := by
    have h0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    exact zpow_eq_zpow_emod' j hrho3
  exact hdn _ (hmod ▸ hconj)

theorem false_of_inner (hEF : partTwoF G = partTwoE G) {c : G} {L P₀ : Subgroup G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc : orderOf c = 3) (hcP : c ∈ P₀)
    (hP₀L : P₀ ≤ Sec4.thetaQuotCentralizer L) (hP₀e : CFSG.Assembly.IsElemAbelian 3 P₀)
    (hP₀9 : Nat.card P₀ = 9) (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {j d : L ⧸ aschbacherSolvableCore 3 L} (hj3 : j ^ 3 = 1) (hj1 : j ≠ 1) (hd3 : d ^ 3 = 1)
    (hjd : j * d = d * j) (hdj : d ∉ Subgroup.zpowers j)
    {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hjV : j ∈ Subgroup.normalizer (V : Set (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  have hP₀N : ∀ p ∈ P₀, p ∈ Subgroup.normalizer (L : Set G) := fun p hp => by
    obtain ⟨q, -, rfl⟩ := hP₀L hp
    exact q.2
  have hP₀1 : ∀ p (hp : p ∈ P₀), rho L ⟨p, hP₀N p hp⟩ = 1 := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := hP₀L hp
    exact hq
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  obtain ⟨x, hxP, hxc⟩ := exists_mem_not_mem_zpowers hP₀9 hc3
  have hx3 : x ^ 3 = 1 := hP₀e.2 x hxP
  have hxN := hP₀N x hxP
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective j
  obtain ⟨m₁, hm₁x, hm₁⟩ := Sec8.Hering88F.exists_mem_centralizer_of_fixed (Y := L) (M := L)
    le_rfl hxN hxN hx3 m₀.2 (by
      have h1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩) = 1 := hP₀1 x hxP
      rw [h1]
      rfl)
  have hm₁j : ((⟨m₁, m₁.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = j := by
    rw [← hm₀]
    exact hm₁
  obtain ⟨k, hkj, hk3⟩ := exists_pow_lift_three (⟨m₁, m₁.2⟩ : L) hm₁j hj3
  set y : G := ((⟨m₁, m₁.2⟩ ^ k : L) : G) with hydef
  have hyL : y ∈ L := (⟨m₁, m₁.2⟩ ^ k : L).2
  have hy3 : y ^ 3 = 1 := by
    rw [hydef, ← Subgroup.coe_pow, hk3, OneMemClass.coe_one]
  have hm₁x' : (m₁ : G) * x = x * m₁ := Subgroup.mem_centralizer_singleton_iff.mp hm₁x
  have hyx : y * x = x * y := by
    rw [hydef, Subgroup.coe_pow]
    exact (Commute.pow_left (show Commute (m₁ : G) x from hm₁x') k).eq
  have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hLc hyL)
  have hyP : ∀ p ∈ P₀, p * y = y * p := fun p hp =>
    (forall_commute_of_commute hP₀e hP₀9 hc hcP hxP hxc hyc hyx p hp).symm
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hrho : rho L ⟨y, hyN⟩ = MulAut.conj j := by
    have := KFacts.thetaQuotMulAut_compAction_of_mem hyL hyN
    change Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨y, hyN⟩) = _
    rw [this, ← hkj]
    rfl
  have hconj_inj : ∀ a b : L ⧸ aschbacherSolvableCore 3 L, MulAut.conj a = MulAut.conj b → a = b := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := congrArg (fun σ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => σ w) hab
      simp only [MulAut.conj_apply] at h
      calc w * (b⁻¹ * a) = b⁻¹ * (b * w * b⁻¹) * a := by group
        _ = b⁻¹ * (a * w * a⁻¹) * a := by rw [← h]
        _ = b⁻¹ * a * w := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  refine false_of_lift hEF hLc hc hcP hP₀L hP₀e hP₀9 hyP hyN hy3 ?_ hV hV2 ?_ hd3 ?_ ?_
  · rw [hrho]
    intro h
    apply hj1
    apply hconj_inj
    rw [h, map_one]
  · intro v hv
    rw [hrho, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hjV v).mp hv
  · rw [hrho, MulAut.conj_apply, hjd, mul_inv_cancel_right]
  · intro k hk
    rw [hrho, ← map_pow] at hk
    exact hdj (hconj_inj _ _ hk ▸ Subgroup.npow_mem_zpowers j k)

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
