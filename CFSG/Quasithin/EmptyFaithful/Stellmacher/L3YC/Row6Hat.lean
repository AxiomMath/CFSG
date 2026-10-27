module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row6Common
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

theorem row6_hat_false {K : Type} [Group K] [Finite K] {N Lb : Subgroup K} [N.Normal]
    (hLb : Lb ≤ N) (hrank : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hHat : IsHat ↥N (alternatingGroup (Fin 7)))
    (hLbZ : ∀ z ∈ Lb, (∀ a ∈ Lb, z * a = a * z) → z = 1)
    (h6c : ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
      ∀ E : Subgroup X, Nat.card E = 9 → E ⊓ Subgroup.center X ≠ ⊥)
    {e x : K} (he : e ∈ Lb) (he3 : orderOf e = 3) (hx3 : orderOf x = 3)
    (hex : e * x = x * e) (hxL : x ∉ Subgroup.normalizer (Lb : Set K)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he3; omega
  have hxe : x ∉ Subgroup.zpowers e := fun h =>
    hxL (Subgroup.le_normalizer ((Subgroup.zpowers_le.mpr he) h))
  have hZc : Nat.card ↥(Subgroup.center ↥N) = 3 := hHat.2.1
  have hZne : Subgroup.center ↥N ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZc
    omega
  obtain ⟨z', hz'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
  have hz'ord : orderOf z' = 3 := by
    have hd : orderOf z' ∣ 3 := hZc ▸ orderOf_dvd_natCard z'
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz'1
    · exact h
  have hzc : ∀ a ∈ N, (((z' : ↥N) : K)) * a = a * (((z' : ↥N) : K)) := by
    intro a ha
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp z'.2 ⟨a, ha⟩)).symm
  have hz3 : orderOf (((z' : ↥N) : K)) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz'ord
  have hZtop : Subgroup.zpowers z' = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hz'ord, hZc]
  have hZ : ∀ w ∈ N, (∀ a ∈ N, w * a = a * w) → w ∈ Subgroup.zpowers (((z' : ↥N) : K)) := by
    intro w hw hwc
    have hmem : (⟨⟨w, hw⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (hwc g g.2).symm⟩ : ↥(Subgroup.center ↥N)) ∈ Subgroup.zpowers z' := by
      rw [hZtop]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg (fun u : ↥(Subgroup.center ↥N) => ((u : ↥N) : K)) hk
    simpa using this
  have hez : e ∉ Subgroup.zpowers (((z' : ↥N) : K)) :=
    row6_not_mem_zpowers_of_central hLb hLbZ he he1 hzc
  have hxN : x ∈ N :=
    lemma2_center_three hrank (z := ((z' : ↥N) : K)) z'.1.2 hzc hz3 hZ (hLb he) he3 hez hx3 hex
  obtain ⟨hE, hE9⟩ := row6_exists_E9 he3 hx3 hex hxe
  have hE₀N : Subgroup.zpowers e ⊔ Subgroup.zpowers x ≤ N :=
    sup_le (Subgroup.zpowers_le.mpr (hLb he)) (Subgroup.zpowers_le.mpr hxN)
  have h9 : Nat.card ((Subgroup.zpowers e ⊔ Subgroup.zpowers x).subgroupOf N) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀N).toEquiv).trans hE9
  obtain ⟨w', hw'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (h6c ↥N hHat _ h9)
  have hwE : (((w' : ↥N) : K)) ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers x := w'.2.1
  have hwc : ∀ a ∈ N, (((w' : ↥N) : K)) * a = a * (((w' : ↥N) : K)) := by
    intro a ha
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp w'.2.2 ⟨a, ha⟩)).symm
  have hw1 : (((w' : ↥N) : K)) ≠ 1 := fun h => hw'1 (Subtype.ext (Subtype.ext h))
  have hw3 : orderOf (((w' : ↥N) : K)) = 3 := by
    apply orderOf_eq_prime _ hw1
    exact hE.2 _ hwE
  have hwe : (((w' : ↥N) : K)) ∉ Subgroup.zpowers e := by
    intro h
    have heq : Subgroup.zpowers (((w' : ↥N) : K)) = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, he3, hw3])
    exact row6_not_mem_zpowers_of_central hLb hLbZ he he1 hwc (by rw [heq]; exact Subgroup.mem_zpowers e)
  obtain ⟨-, hAc⟩ := exists_elemAbelian_sup_zpowers (isElemAbelian_zpowers_order_three he3).1 hw3
    (fun u hu => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ((show Commute e (((w' : ↥N) : K)) from (hwc e (hLb he)).symm).zpow_left k)) hwe
  have hAE : Subgroup.zpowers e ⊔ Subgroup.zpowers (((w' : ↥N) : K)) ≤
      Subgroup.zpowers e ⊔ Subgroup.zpowers x :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers e)))
      (Subgroup.zpowers_le.mpr hwE)
  have hAeq : Subgroup.zpowers e ⊔ Subgroup.zpowers (((w' : ↥N) : K)) =
      Subgroup.zpowers e ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hAE (by rw [hAc, hE9, Nat.card_zpowers, he3])
  have hxA : x ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers (((w' : ↥N) : K)) := by
    rw [hAeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hwnorm : (((w' : ↥N) : K)) ∈ Subgroup.normalizer (Lb : Set K) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have haLb : a ∈ Lb := ha
    have : (((w' : ↥N) : K)) * a * (((w' : ↥N) : K))⁻¹ = a := by
      rw [hwc a (hLb haLb)]; group
    rw [this]
    exact haLb
  have hAnorm : Subgroup.zpowers e ⊔ Subgroup.zpowers (((w' : ↥N) : K)) ≤
      Subgroup.normalizer (Lb : Set K) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer he))
      (Subgroup.zpowers_le.mpr hwnorm)
  exact hxL (hAnorm hxA)

end Stellmacher.L3YC

end CFSG.Quasithin
