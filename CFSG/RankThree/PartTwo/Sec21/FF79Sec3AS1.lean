module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.Open.FusionDefs

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Exp32
import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.AS

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem mem_of_sylowOf_of_mem_nor {H Q : Subgroup G} (hQ : IsSylowOf 3 Q H) {y : G}
    (hyH : y ∈ H) (hyN : y ∈ Nor Q) (hy : IsPGroup 3 (Subgroup.zpowers y)) : y ∈ Q := by
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le).mpr hyN
  have hK : IsPGroup 3 ↥(Subgroup.zpowers y ⊔ Q) := hy.to_sup_of_normal_right' hQ.2.1 hle
  have hKH : Subgroup.zpowers y ⊔ Q ≤ H := sup_le ((Subgroup.zpowers_le).mpr hyH) hQ.1
  have := eq_of_sylowOf_three_le hQ hK hKH le_sup_right
  rw [this]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

theorem eq_or_eq_of_card_three_mul {K L M : Subgroup G} (hKL : K ≤ L) (hLM : L ≤ M)
    (hc : Nat.card M = 3 * Nat.card K) : L = K ∨ L = M := by
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hKL
  obtain ⟨e, he⟩ := Subgroup.card_dvd_of_le hLM
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have hde : d * e = 3 := by
    have : Nat.card K * 3 = Nat.card K * (d * e) := by rw [← mul_assoc, ← hd, ← he, hc]; ring
    exact (Nat.eq_of_mul_eq_mul_left hK0 this).symm
  have hd3 : d ∣ 3 := ⟨e, hde.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
  · left
    exact (Subgroup.eq_of_le_of_card_ge hKL (by rw [hd, h1, mul_one])).symm
  · right
    refine Subgroup.eq_of_le_of_card_ge hLM ?_
    rw [hc, hd, h3, mul_comm]

theorem inf_zpowers_eq_bot {b : G} (hb : orderOf b = 3) {H : Subgroup G} (hbH : b ∉ H) :
    H ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxH, hxz⟩ := hx
  have hxo : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := by rw [← hb]; exact orderOf_dvd_of_mem_zpowers hxz
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have heq : Subgroup.zpowers x = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hxz) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hb]
  have : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
  exact hbH ((Subgroup.zpowers_le).mpr hxH this)

theorem mem_zpowers_of_mem {b c : G} (hb : orderOf b = 3) (hc : c ∈ Subgroup.zpowers b)
    (hc1 : c ≠ 1) : b ∈ Subgroup.zpowers c := by
  by_contra h
  have := inf_zpowers_eq_bot hb h
  have hc' : c ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers b := ⟨Subgroup.mem_zpowers c, hc⟩
  rw [this, Subgroup.mem_bot] at hc'
  exact hc1 hc'

theorem card_sup_zpowers {b : G} (hb : orderOf b = 3) {H : Subgroup G} (hbN : b ∈ Nor H)
    (hbH : b ∉ H) : Nat.card ↥(H ⊔ Subgroup.zpowers b) = Nat.card H * 3 := by
  have hZ : Subgroup.zpowers b ≤ Subgroup.normalizer (H : Set G) := (Subgroup.zpowers_le).mpr hbN
  rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZ (inf_zpowers_eq_bot hb hbH),
    Nat.card_zpowers, hb]

theorem mem_nor_sup {g : G} {H K : Subgroup G} (hH : g ∈ Nor H) (hK : g ∈ Nor K) :
    g ∈ Nor (H ⊔ K) := by
  refine L41.mem_nor_of_forall fun y hy => ?_
  have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hH x).mp hx)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hK x).mp hx)
  simpa using hle hy

theorem mem_nor_inf {g : G} {H K : Subgroup G} (hH : g ∈ Nor H) (hK : g ∈ Nor K) :
    g ∈ Nor (H ⊓ K) :=
  L41.mem_nor_of_forall fun _ hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp hH _).mp hy.1, (Subgroup.mem_normalizer_iff.mp hK _).mp hy.2⟩

theorem mem_nor_cenS {g : G} {A : Subgroup G} (hg : g ∈ Nor A) : g ∈ Nor (CenS A) := by
  refine L41.mem_nor_of_forall fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : g⁻¹ * a * g⁻¹⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).inv_mem hg) a).mp ha
  have h2 := Subgroup.mem_centralizer_iff.mp hc _ h1
  calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g⁻¹⁻¹) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * a * g⁻¹⁻¹)) * g⁻¹ := by rw [h2]
    _ = g * c * g⁻¹ * a := by group

theorem mem_nor_cen {g x : G} (hg : g * x = x * g) : g ∈ Nor (Cen x) := by
  refine L41.mem_nor_of_forall fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hc' : y * c = c * y := Subgroup.mem_centralizer_iff.mp hc y rfl
  have hg' : g⁻¹ * y = y * g⁻¹ := by
    calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hg]
      _ = y * g⁻¹ := by group
  calc y * (g * c * g⁻¹) = (y * g) * c * g⁻¹ := by group
    _ = g * (y * c) * g⁻¹ := by rw [← hg]; group
    _ = g * (c * y) * g⁻¹ := by rw [hc']
    _ = g * c * (y * g⁻¹) := by group
    _ = g * c * (g⁻¹ * y) := by rw [← hg']
    _ = g * c * g⁻¹ * y := by group

theorem isSylowOf_of_fusion {S M : Subgroup G} (h : CFSG.Open.fusionIsSylowIn 3 S M) :
    IsSylowOf 3 S M := by
  obtain ⟨R, hR, hSR⟩ := exists_sylowOf_three_ge h.1 h.2.1
  have := h.2.2 R hR.1 hR.2.1 hSR
  rwa [this] at hR

theorem le_zpowers_of_cen {b : G} (hb : orderOf b = 3) {T : Subgroup G} (hT : IsPGroup 3 T)
    (hbT : b ∈ T) (h : ∀ t ∈ T, t * b = b * t → t ∈ Subgroup.zpowers b) :
    T ≤ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hb; omega
  haveI : Nontrivial T := ⟨⟨⟨b, hbT⟩, 1, fun e => hb1 (congrArg Subtype.val e)⟩⟩
  haveI := hT.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center T)
  have hcen : ∀ t : T, t * (c : T) = (c : T) * t := fun t =>
    (Subgroup.mem_center_iff.mp c.2 t)
  set c' : G := ((c : T) : G) with hc'
  have hcT : c' ∈ T := (c : T).2
  have hc1 : c' ≠ 1 := by
    intro e
    apply hc
    exact Subtype.ext (Subtype.ext e)
  have hcb : c' * b = b * c' := (congrArg Subtype.val (hcen ⟨b, hbT⟩)).symm
  have hcz : c' ∈ Subgroup.zpowers b := h c' hcT hcb
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_mem hb hcz hc1)
  intro t ht
  refine h t ht ?_
  have htc : Commute t c' := congrArg Subtype.val (hcen ⟨t, ht⟩)
  rw [← hn]
  exact (htc.zpow_right n).eq

theorem exists_conj_eq_of_odd {w z : G} (hw : w * w = 1) (hz : z * z = 1)
    (ho : Odd (orderOf (w * z))) : ∃ k : ℕ, (w * z) ^ k * w * ((w * z) ^ k)⁻¹ = z := by
  set u := w * z with hu
  obtain ⟨k, hk⟩ := ho
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hzu : z * u * z⁻¹ = u⁻¹ := by
    rw [hu, mul_inv_rev, hzi, hwi]
    calc z * (w * z) * z = z * w * (z * z) := by group
      _ = z * w := by rw [hz, mul_one]
  have hwu : w = u * z := by
    rw [hu, mul_assoc, hz, mul_one]
  refine ⟨k, ?_⟩
  have h1 : z * (u ^ k)⁻¹ * z⁻¹ = u ^ k := by
    have : z * u ^ k * z⁻¹ = (u⁻¹) ^ k := by rw [← hzu, conj_pow]
    calc z * (u ^ k)⁻¹ * z⁻¹ = (z * u ^ k * z⁻¹)⁻¹ := by group
      _ = u ^ k := by rw [this, inv_pow, inv_inv]
  have h2 : u ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one u
  calc u ^ k * w * (u ^ k)⁻¹ = u ^ k * u * (z * (u ^ k)⁻¹ * z⁻¹) * z := by rw [hwu]; group
    _ = u ^ (2 * k + 1) * z := by rw [h1, ← pow_succ, ← pow_add]; ring_nf
    _ = z := by rw [h2, one_mul]

theorem four_le_localRank_of {S A : Subgroup G} (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hA : IsElemAb 3 4 A) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    4 ≤ localRank 3 G := by
  have hle : ∀ H : Subgroup G, ∀ k ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}, k ≤ Nat.card G := by
    rintro H k ⟨E, -, -, hk⟩
    have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  have h1 : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (S : Set G)) := by
    unfold CFSG.Open.pRank
    refine le_csSup ⟨Nat.card G, hle _⟩ ⟨A, hAS, ?_, hA.2⟩
    exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hA.1
  unfold localRank CFSG.Open.twoLocalPrimeRank
  refine h1.trans (le_csSup ⟨Nat.card G, ?_⟩ ⟨_, ⟨S, hS, hS2, rfl⟩, rfl⟩)
  rintro k ⟨H, -, rfl⟩
  unfold CFSG.Open.pRank
  exact csSup_le ⟨0, ⊥, bot_le, CFSG.Open.isElemAbelian_bot 3, by simp⟩ (hle H)

theorem odd_card_cenS_of_localRank {A : Subgroup G} (hA : IsElemAb 3 4 A)
    (hr : localRank 3 G ≤ 3) : Odd (Nat.card (CenS A)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := CenS A) 2 h2
  have hto : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hS2 : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
  have hS : Subgroup.zpowers (t : G) ≠ ⊥ := by
    intro hb
    have : (t : G) ∈ (⊥ : Subgroup G) := hb ▸ Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hto
    omega
  have hAS : A ≤ Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := by
    intro a ha
    have hta : a * (t : G) = (t : G) * a := Subgroup.mem_centralizer_iff.mp t.2 a ha
    have hmem : a ∈ Nor (Cen (t : G)) := mem_nor_cen hta
    refine L41.mem_nor_of_forall fun y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : a * (t : G) ^ n * a⁻¹ = (t : G) ^ n := by
      rw [(Commute.zpow_right hta n).eq]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
  have := four_le_localRank_of hS hS2 hA hAS
  omega

theorem isSylowOf_top_of_sylowOf_nor {P : Subgroup G} (h : IsSylowOf 3 P (Nor P)) :
    IsSylowOf 3 P ⊤ := by
  haveI hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨le_top, h.2.1, ?_⟩
  obtain ⟨n, hn⟩ := h.2.1.exists_card_eq
  rw [Subgroup.relIndex_top_right]
  by_contra hc
  have hdvd : 3 ∣ P.index := (Nat.Prime.coprime_iff_not_dvd hp.out).not_left.mp hc
  have h1 : 3 ^ (n + 1) ∣ Nat.card G := by
    rw [← P.card_mul_index, hn, pow_succ]
    exact Nat.mul_dvd_mul_left _ hdvd
  have h2 := Sylow.prime_dvd_card_quotient_normalizer h1 hn
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp h.2.2 h2

end CFSG.RankThree.PartTwo.Sec21.FF79.AS
