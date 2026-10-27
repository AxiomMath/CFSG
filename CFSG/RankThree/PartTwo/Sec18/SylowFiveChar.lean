module

public import CFSG.RankThree.PartTwo.Sec18.SylowFiveDelta
import CFSG.RankThree.PartTwo.Sec18.SylowFiveAbelian
import CFSG.RankThree.PartTwo.Sec18.SylowFiveOmega
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace SylowFive

variable {G : Type} [Group G]

def cubes (H : Type*) [Group H] : Subgroup H := Subgroup.closure {y | ∃ x : H, x ^ 3 = y}

instance cubes_characteristic (H : Type*) [Group H] : (cubes H).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  rw [cubes, Subgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  exact Subgroup.subset_closure ⟨φ x, by simp⟩

theorem commutatorElement_mem (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem eq_subgroupOf_of_map_eq {P : Subgroup G} {X' : Subgroup P} {X : Subgroup G}
    (h : X'.map P.subtype = X) : X' = X.subgroupOf P := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← h]
  exact (Subgroup.mem_map_iff_mem P.subtype_injective).symm

theorem centralizer_subgroupOf {P X : Subgroup G} (hXP : X ≤ P) :
    Subgroup.centralizer ((X.subgroupOf P : Subgroup P) : Set P) =
      (Subgroup.centralizer (X : Set G)).subgroupOf P := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact congrArg Subtype.val (h ⟨b, hXP hb⟩ hb)
  · intro h b hb
    exact Subtype.ext (h b hb)

theorem eq_of_le_of_le_of_card_eq [Finite G] {H X K : Subgroup G} (hHX : H ≤ X) (hXK : X ≤ K)
    (hK : Nat.card K = 3 * Nat.card H) (hne : X ≠ H) : X = K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHX
  obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le hXK
  have hH0 : 0 < Nat.card H := Nat.card_pos
  have h1 : Nat.card H * (m * n) = Nat.card H * 3 := by
    rw [← mul_assoc, ← hm, ← hn, hK, mul_comm]
  have hmn : m * n = 3 := Nat.eq_of_mul_eq_mul_left hH0 h1
  have hm3 : m = 1 ∨ m = 3 := (Nat.dvd_prime Nat.prime_three).mp ⟨n, hmn.symm⟩
  rcases hm3 with rfl | rfl
  · exact absurd (Subgroup.eq_of_le_of_card_ge hHX (by rw [hm, mul_one])).symm hne
  · have hn1 : n = 1 := by omega
    subst hn1
    exact Subgroup.eq_of_le_of_card_ge hXK (by rw [hn, mul_one])

namespace CaseTwo

variable {P A B : Subgroup G} {c : G} (hS : CaseTwo P A B c)
include hS

theorem centralizer_subgroupOf_eq :
    Subgroup.centralizer ((B.subgroupOf P : Subgroup P) : Set P) = (qOf P B).subgroupOf P := by
  rw [centralizer_subgroupOf hS.plane_le]
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

variable [Finite G]

theorem plane_eq_sup_of {d₁ d₂ : G} (hd₁ : d₁ ∈ B) (hd₁1 : d₁ ≠ 1) (hd₂ : d₂ ∈ B)
    (hd₂n : d₂ ∉ Subgroup.zpowers d₁) : B = Subgroup.zpowers d₂ ⊔ Subgroup.zpowers d₁ := by
  have hle : Subgroup.zpowers d₂ ⊔ Subgroup.zpowers d₁ ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hd₂) (Subgroup.zpowers_le.mpr hd₁)
  have hd₂1 : d₂ ≠ 1 := fun h => hd₂n (h ▸ Subgroup.one_mem _)
  have hn : Subgroup.zpowers d₂ ≤ Subgroup.normalizer (Subgroup.zpowers d₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (hS.comm (hS.le hd₁) (hS.le hd₂)) k).eq
  have h1 := Sec6.card_sup_mul_card_inf hn
  rw [zpowers_inf_eq_bot (hS.pow_three_of_mem_plane hd₂) hd₂n, Subgroup.card_bot, mul_one,
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hS.pow_three_of_mem_plane hd₂) hd₂1,
    orderOf_eq_prime (hS.pow_three_of_mem_plane hd₁) hd₁1] at h1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hS.card_plane])).symm

theorem eq_qOf_of_mem {X : Subgroup G} (hAX : A ≤ X) (hXQ : X ≤ qOf P B) {m q : G}
    (hm : m ∈ X) (hq : q ∈ X) (hm1 : ⁅m, c⁆ ≠ 1) (hqm : ⁅q, c⁆ ∉ Subgroup.zpowers ⁅m, c⁆) :
    X = qOf P B := by
  have hD : hS.dImage X = B := by
    refine le_antisymm (hS.dImage_le_plane X) ?_
    refine (hS.plane_eq_sup_of (hS.commutator_mem (hXQ hm).1) hm1
      (hS.commutator_mem (hXQ hq).1) hqm).le.trans (sup_le ?_ ?_)
    · exact Subgroup.zpowers_le.mpr (hS.mem_dImage.mpr ⟨q, hq, hXQ hq, rfl⟩)
    · exact Subgroup.zpowers_le.mpr (hS.mem_dImage.mpr ⟨m, hm, hXQ hm, rfl⟩)
  have h := hS.card_eq_of_le_qOf hXQ
  rw [inf_eq_right.mpr hAX, hD, hS.card_eq, hS.card_plane] at h
  exact Subgroup.eq_of_le_of_card_ge hXQ (by rw [h, hS.card_qOf])

def cSub (s : G) : Subgroup G where
  carrier := {x | x ∈ qOf P B ∧ ⁅x, s⁆ ∈ B}
  mul_mem' := by
    rintro x y ⟨hx, hxs⟩ ⟨hy, hys⟩
    refine ⟨(qOf P B).mul_mem hx hy, ?_⟩
    have e : ⁅x * y, s⁆ = x * ⁅y, s⁆ * x⁻¹ * ⁅x, s⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hS.commute_of_mem_qOf hx hys, mul_inv_cancel_right]
    exact B.mul_mem hys hxs
  one_mem' := ⟨(qOf P B).one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxs⟩
    refine ⟨(qOf P B).inv_mem hx, ?_⟩
    have e : ⁅x⁻¹, s⁆ = x⁻¹ * ⁅x, s⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e, mul_assoc, ← hS.commute_of_mem_qOf hx (B.inv_mem hxs), inv_mul_cancel_left]
    exact B.inv_mem hxs

theorem mem_cSub {s x : G} : x ∈ hS.cSub s ↔ x ∈ qOf P B ∧ ⁅x, s⁆ ∈ B := Iff.rfl

theorem le_cSub {s : G} (hs : s ∈ qOf P B) : A ≤ hS.cSub s := by
  intro a ha
  refine (hS.mem_cSub).mpr ⟨hS.le_qOf ha, ?_⟩
  obtain ⟨i, -, b, hb, rfl⟩ := Sec13.exists_pow_mul_of_mem hS.isElemAbelian hS.mem hS.eq_sup ha
  rw [← commutatorElement_inv, hS.commutator_pow_mul hs hb]
  exact B.inv_mem (B.pow_mem (hS.commutator_mem hs.1) i)

theorem cSub_le {s : G} : hS.cSub s ≤ qOf P B := fun _ hx => ((hS.mem_cSub).mp hx).1

theorem commutator_not_mem_plane (hna : ∃ x ∈ qOf P B, ∃ y ∈ qOf P B, ⁅x, y⁆ ∉ B)
    {q m : G} (hq : q ∈ qOf P B) (hm : m ∈ qOf P B) (hm1 : ⁅m, c⁆ ≠ 1)
    (hqm : ⁅q, c⁆ ∉ Subgroup.zpowers ⁅m, c⁆) : ⁅q, m⁆ ∉ B := by
  intro hqmB
  have hswap : ∀ {x y : G}, ⁅x, y⁆ ∈ B → ⁅y, x⁆ ∈ B := fun h => by
    rw [← commutatorElement_inv]; exact B.inv_mem h
  have hCm : hS.cSub m = qOf P B := hS.eq_qOf_of_mem (hS.le_cSub hm) hS.cSub_le
    ((hS.mem_cSub).mpr ⟨hm, by simp⟩) ((hS.mem_cSub).mpr ⟨hq, hqmB⟩) hm1 hqm
  have hCq : hS.cSub q = qOf P B := hS.eq_qOf_of_mem (hS.le_cSub hq) hS.cSub_le
    ((hS.mem_cSub).mpr ⟨hm, hswap hqmB⟩) ((hS.mem_cSub).mpr ⟨hq, by simp⟩) hm1 hqm
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  have hmy : ⁅m, y⁆ ∈ B := hswap ((hS.mem_cSub).mp (hCm.ge hy)).2
  have hqy : ⁅q, y⁆ ∈ B := hswap ((hS.mem_cSub).mp (hCq.ge hy)).2
  have hCy : hS.cSub y = qOf P B := hS.eq_qOf_of_mem (hS.le_cSub hy) hS.cSub_le
    ((hS.mem_cSub).mpr ⟨hm, hmy⟩) ((hS.mem_cSub).mpr ⟨hq, hqy⟩) hm1 hqm
  exact hxy ((hS.mem_cSub).mp (hCy.ge hx)).2

theorem commutator_qOf_le : ⁅qOf P B, qOf P B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine (hS.commutator_eq_one_iff (commutatorElement_mem _ hx hy)).mp ?_
  have h := map_commutatorElement hS.deltaG ⟨x, hx⟩ ⟨y, hy⟩
  simp only [hS.deltaG_apply] at h
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hS.comm (hS.le (hS.commutator_mem hx.1))
    (hS.le (hS.commutator_mem hy.1)))] at h
  exact h

theorem commutator_qOf_eq (hna : ∃ x ∈ qOf P B, ∃ y ∈ qOf P B, ⁅x, y⁆ ∉ B) :
    ⁅qOf P B, qOf P B⁆ = A := by
  have hBle : B ≤ ⁅qOf P B, qOf P B⁆ := fun b hb => by
    obtain ⟨x, hx, rfl⟩ := hS.exists_commutator_eq hb
    exact Subgroup.commutator_mem_commutator hx (hS.le_qOf hS.mem)
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  refine eq_of_le_of_le_of_card_eq hBle hS.commutator_qOf_le
    (by rw [hS.card_eq, hS.card_plane]) fun h => ?_
  exact hxy (h.le (Subgroup.commutator_mem_commutator hx hy))

theorem inf_centralizer_eq {X : Subgroup G} (hAX : A ≤ X) (hXQ : X ≤ qOf P B) (hne : X ≠ A) :
    X ⊓ Subgroup.centralizer (X : Set G) = B := by
  obtain ⟨m, hmX, hmA⟩ : ∃ m ∈ X, m ∉ A := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hAX)
  have hm1 : ⁅m, c⁆ ≠ 1 := fun h => hmA ((hS.commutator_eq_one_iff (hXQ hmX)).mp h)
  apply le_antisymm
  · rintro z ⟨hzX, hzC⟩
    have hzc : ∀ x ∈ X, x * z = z * x := fun x hx => (Subgroup.mem_centralizer_iff.mp hzC) x hx
    have hzA : z ∈ A := hS.mem_of_commute z (hXQ hzX).1 fun a ha => (hzc a (hAX ha)).symm
    obtain ⟨i, hi, b, hb, rfl⟩ :=
      Sec13.exists_pow_mul_of_mem hS.isElemAbelian hS.mem hS.eq_sup hzA
    have h := hS.commutator_pow_mul (hXQ hmX) hb i
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hzc m hmX)] at h
    interval_cases i
    · simpa using hb
    · exact absurd (by simpa using h.symm) hm1
    · exact absurd (eq_one_of_pow_three_of_pow_two
        (hS.pow_three_of_mem_plane (hS.commutator_mem (hXQ hmX).1)) h.symm) hm1
  · intro b hb
    exact ⟨hAX (hS.le hb), Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hS.commute_of_mem_qOf (hXQ hx) hb⟩

theorem characteristic : (A.subgroupOf P).Characteristic := by
  obtain ⟨b₀, b₁, hF⟩ := hS.exists_flag
  have hQP : qOf P B ≤ P := inf_le_left
  have hQchar : ∀ X' : Subgroup P, X' = B.subgroupOf P → X'.Characteristic →
      ((qOf P B).subgroupOf P).Characteristic := by
    intro X' hX' hc
    subst hX'
    rw [← hS.centralizer_subgroupOf_eq]
    exact Subgroup.characteristic_centralizer (hH := hc)
  by_cases hab : ∀ x ∈ qOf P B, ∀ y ∈ qOf P B, ⁅x, y⁆ ∈ B
  ·
    have hBY : B ≤ (cubes P).map P.subtype := fun b hb => by
      obtain ⟨t, ht, rfl⟩ := hS.exists_pow_three_eq hab hb
      exact ⟨⟨t, ht.1⟩ ^ 3, Subgroup.subset_closure ⟨_, rfl⟩, by simp⟩
    have hYA : (cubes P).map P.subtype ≤ A := by
      rw [Subgroup.map_le_iff_le_comap, cubes, Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      simpa using hS.pow_three_mem hF x.2
    by_cases hYeq : (cubes P).map P.subtype = A
    · rw [← eq_subgroupOf_of_map_eq hYeq]
      infer_instance
    · have hYB : (cubes P).map P.subtype = B := by
        by_contra hne
        exact hYeq (eq_of_le_of_le_of_card_eq hBY hYA (by rw [hS.card_eq, hS.card_plane]) hne)
      have hQc := hQchar _ (eq_subgroupOf_of_map_eq hYB) inferInstance
      rw [Subgroup.characteristic_iff_le_comap]
      intro φ a ha
      have ha' : (a : G) ∈ A := ha
      have haQ : a ∈ (qOf P B).subgroupOf P := hS.le_qOf ha'
      have hφQ : φ a ∈ (qOf P B).subgroupOf P :=
        (Subgroup.characteristic_iff_le_comap.mp hQc φ) haQ
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hS.pow_three ha')
      have hφ3 : (φ a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
      have h3 : ((φ a : P) : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hφ3
      exact hS.mem_of_pow_three_eq_one hab hφQ h3
  · push Not at hab
    have hT : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).map P.subtype = ⁅P, P⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hAT : A ≤ ⁅P, P⁆ :=
      (hS.commutator_qOf_eq hab).ge.trans (Subgroup.commutator_mono hQP hQP)
    have hTQ : ⁅P, P⁆ ≤ qOf P B :=
      Subgroup.commutator_le.mpr fun x hx y hy => hS.commutator_mem_qOf hF hx hy
    by_cases hTA : ⁅P, P⁆ = A
    · rw [← eq_subgroupOf_of_map_eq (hT.trans hTA)]
      infer_instance
    · have hB := hS.inf_centralizer_eq hAT hTQ hTA
      have hB'eq : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) ⊓
          Subgroup.centralizer ((⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) : Set P) =
            B.subgroupOf P := by
        rw [eq_subgroupOf_of_map_eq hT, centralizer_subgroupOf (hTQ.trans hQP), ← hB]
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      have hQc := hQchar _ hB'eq inferInstance
      have hA' : (⁅(qOf P B).subgroupOf P, (qOf P B).subgroupOf P⁆ : Subgroup P).map P.subtype =
          A := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQP,
          hS.commutator_qOf_eq hab]
      rw [← eq_subgroupOf_of_map_eq hA']
      infer_instance

end CaseTwo

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
