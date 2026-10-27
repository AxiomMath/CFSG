module

public import CFSG.Sporadic.MI301Five.RowI
public import CFSG.Sporadic.MI301.RowMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
import CFSG.Sporadic.MI301Five.RowB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Open CFSG.Monster.Existence CFSG.Monster.GMS CFSG.EvenSporadicStandard.HNRecog
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301 Subgroup

variable {G : Type} [Group G] {α d z : G}

private theorem rowR0_eq_map (hL : GMSLeechCentralizer z)
    (hrk : GLATwoLocalRank 5 CFSG.Blueprint.NativeSporadic.Co1 < 3) {X : Subgroup G}
    (hXd : X ≤ cent d) (hXz : X ≤ cent z) (hdz : d ∈ cent z)
    (hRX : ∀ x ∈ rowR0Of d (leechQ z), x ∈ X) {Q : Subgroup ↥X} [Q.Normal]
    (hQ : IsExtraspecialPlusByA5WrTwoWith ↥X Q) {B₁ : Subgroup G}
    (hB : IsElemAbelian 5 B₁ ∧ Nat.card B₁ = 5 ^ 3) (hBX : B₁ ≤ zpowers d ⊔ X) :
    rowR0Of d (leechQ z) = Q.map X.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ ((map_subtype_le Q).trans hXd))
  · have hN : ((leechQ z).subgroupOf X).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact conj_mem_leechQ (hXz g.2) hn⟩
    have hp : IsPGroup 2 (leechQ z) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(centralizer ({z} : Set G)))).map _
    have hle : (leechQ z).subgroupOf X ≤ Q := by
      rw [← Section3.IsExtraspecialPlusByA5WrTwoWith.pCore_eq hQ]
      exact le_sSup ⟨hN, hp.comap_of_injective X.subtype X.subtype_injective⟩
    exact mem_map.2 ⟨⟨x, hRX x hx⟩, hle (mem_subgroupOf.2 (mem_inf.1 hx).1), rfl⟩
  · have hQs : (Q.map X.subtype).subgroupOf X = Q :=
      comap_map_eq_self_of_injective X.subtype_injective Q
    have hXN : X ≤ normalizer (Q.map X.subtype : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (map_subtype_le Q)).1 (by rw [hQs]; infer_instance)
    have hdN : zpowers d ≤ normalizer (Q.map X.subtype : Set G) := by
      refine zpowers_le.2 (centralizer_le_normalizer _ (mem_centralizer_iff.2 fun q hq => ?_))
      exact mem_centralizer_singleton_iff.1 (hXd (map_subtype_le Q hq))
    exact CFSG.Sporadic.MI301.le_leechQ_of_le_normalizer hL Nat.prime_five (by norm_num) hrk
      hB.1 hB.2 (hBX.trans (sup_le (zpowers_le.2 hdz) hXz))
      ((IsPGroup.of_card hQ.plus.2.1).map X.subtype) ((map_subtype_le Q).trans hXz)
      (hBX.trans (sup_le hdN hXN))

section HN


private theorem mem_X_of_mem_rowR0 [Finite G] (F : FiveFrame α d z) {x : G}
    (hx : x ∈ rowR0Of d (leechQ z)) : x ∈ cent2 α d ⊓ cent z := by
  obtain ⟨hxQ, hxd⟩ := mem_inf.1 hx
  have hxz := leechQ_le_centralizer z hxQ
  obtain ⟨i, h, hh, rfl⟩ := F.exists_eq_mul _ hxd
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_mem_leechQ hxQ
  have hc : Commute (d ^ i) h :=
    Commute.pow_left (mem_centralizer_singleton_iff.1 hh.2).symm i
  have h1 : (d ^ i * h) ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  rw [hc.mul_pow] at h1
  have h2 : (d ^ i) ^ 2 ^ k = 1 := by
    refine F.eq_one_of_mem_zpowers_of_mem_cent (pow_mem (npow_mem_zpowers d i) _) ?_
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem hh.1 _)
  have h5 : orderOf (d ^ i) ∣ 5 := (orderOf_pow_dvd i).trans (dvd_of_eq F.orderOf_d)
  have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) h5
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  rw [h3, one_mul] at hxz ⊢
  exact mem_inf.2 ⟨hh, hxz⟩

theorem FiveFrame.rowR0 [Finite G] (F : FiveFrame α d z) (hL : GMSLeechCentralizer z)
    (hrk : GLATwoLocalRank 5 CFSG.Blueprint.NativeSporadic.Co1 < 3)
    (hX : IsExtraspecialPlusByA5WrTwo ↥(cent2 α d ⊓ cent z)) {B₁ : Subgroup G}
    (hB : IsElemAbelian 5 B₁ ∧ Nat.card B₁ = 5 ^ 3)
    (hBX : B₁ ≤ zpowers d ⊔ (cent2 α d ⊓ cent z)) :
    Nat.card (rowR0Of d (leechQ z)) = 2 ^ 9 ∧ IsExtraSpec2 (rowR0Of d (leechQ z)) ∧
      centerOf (rowR0Of d (leechQ z)) = zpowers z := by
  obtain ⟨Q, _, hQ⟩ := hX
  have hR := rowR0_eq_map hL hrk (inf_le_left.trans inf_le_right) inf_le_right
    (mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 F.mem_z.2).symm)
    (fun x hx => mem_X_of_mem_rowR0 F hx) hQ hB hBX
  have hE : IsExtraSpec2 (rowR0Of d (leechQ z)) := by
    rw [hR]
    exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      (equivMapOfInjective Q _ (cent2 α d ⊓ cent z).subtype_injective)
      ((CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).2
        (CFSG.IsExtraspecial.isExtraspecialPGroup (hE := hQ.plus.1)))
  have hzQ : z ∈ leechQ z := by
    have h : z ∈ LocalAnalysis.GLTheoremA.S8.centerOf (leechQ z) := by
      rw [CFSG.Sporadic.MI301.centerOf_leechQ hL]
      exact mem_zpowers z
    exact map_subtype_le _ h
  have hzc : z ∈ LocalAnalysis.GLTheoremA.S8.centerOf (rowR0Of d (leechQ z)) :=
    CFSG.Monster.mem_map_center_iff.2 ⟨mem_inf.2 ⟨hzQ, F.mem_z.2⟩, fun y hy =>
      mem_centralizer_singleton_iff.1 (leechQ_le_centralizer z (mem_inf.1 hy).1)⟩
  refine ⟨?_, hE, (eq_of_le_of_card_ge (zpowers_le.2 hzc) ?_).symm⟩
  · rw [hR, card_map_of_injective (cent2 α d ⊓ cent z).subtype_injective, hQ.plus.2.1]
  · rw [Nat.card_zpowers, F.orderOf_z]
    exact ((card_map_of_injective (subtype_injective _)).trans hE.2.2.2).le

end HN

end CFSG.Sporadic.MI301Five
