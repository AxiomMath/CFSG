module

public import CFSG.RankThree.GF2n.Tim79aOddTranspRoot
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Basic
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.RootInvolutionCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

abbrev RootShape (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∃ n : ℕ, 1 < n ∧ ∃ W : Subgroup X, S ≤ W ∧ IsElemAbelian 2 W ∧ Nat.card W = 2 ^ n ∧
    (∃ g : X, SevenK.IsL2OrSz ↥(W ⊔ conjSubgroup W g) n) ∧ IsRootGroupShape X n W ∧
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (Group.conjugatesOfSet ((W : Set X) \ {1}))

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem isOddTransp_dSet (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4) :
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (dSet S) := by
  refine ⟨fun d hd => h.root.orderOf_eq_two hd, fun d hd e he => ?_⟩
  rcases h.root.orderOf_mul hd he with h2 | h4 | hodd
  · exact Or.inl (h2 ▸ dvd_rfl)
  · exact absurd h4 (hdeg d hd e he)
  · exact Or.inr hodd

theorem le_rootGroup (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4)
    {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) : S ≤ CFSG.Timmesfeld.rootGroup (dSet S) s := by
  intro t ht
  rcases eq_or_ne t 1 with rfl | ht1
  · exact Subgroup.one_mem _
  rcases eq_or_ne t s with rfl | hts
  · exact Subgroup.subset_closure (CFSG.Timmesfeld.mem_rootSet_self (mem_dSet_of_mem hs hs1))
  · have hs2 : s * s = 1 := h.root.mul_self_eq_one (mem_dSet_of_mem hs hs1)
    have hst1 : s * t ≠ 1 := by
      intro h1
      apply hts
      calc t = s⁻¹ * (s * t) := by group
        _ = s⁻¹ * 1 := by rw [h1]
        _ = s⁻¹ := by rw [mul_one]
        _ = s := inv_eq_of_mul_eq_one_right hs2
    have hcomm : Commute s t := by
      have h2 := h.elem.1.is_comm.comm (⟨s, hs⟩ : S) ⟨t, ht⟩
      exact congrArg Subtype.val h2
    exact Subgroup.subset_closure
      (CFSG.RankThree.GF2n.Tim79a.mem_rootSet_of_mul_mem (h.isOddTransp_dSet hdeg)
        (mem_dSet_of_mem hs hs1) (mem_dSet_of_mem ht ht1) hcomm
        (mem_dSet_of_mem (S.mul_mem hs ht) hst1))

theorem isElemAbelian_rootGroup (h : Hyp X S) {d : X} (hd : d ∈ dSet S) :
    IsElemAbelian 2 (CFSG.Timmesfeld.rootGroup (dSet S) d) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (CFSG.Timmesfeld.commute_of_mem_rootGroup hd a.2 b.2).eq
  · rw [pow_two]
    exact CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup h.root hd hx

theorem commute_mk_iff (h : Hyp X S) {d e : X} (hd : d ∈ dSet S) (he : e ∈ dSet S) :
    Commute (QuotientGroup.mk' (Subgroup.center X) d) (QuotientGroup.mk' (Subgroup.center X) e) ↔
      Commute d e := by
  constructor
  · intro hc
    have hπ : QuotientGroup.mk' (Subgroup.center X) (d * e) =
        QuotientGroup.mk' (Subgroup.center X) (e * d) := by
      rw [map_mul, map_mul]
      exact hc.eq
    have hzmem : (d * e) * (d * e) ∈ Subgroup.center X := by
      have hmem := QuotientGroup.eq.mp hπ
      have hinv : ((d * e)⁻¹ * (e * d))⁻¹ ∈ Subgroup.center X := Subgroup.inv_mem _ hmem
      rwa [mul_inv_rev, mul_inv_rev, inv_inv, h.root.inv_eq hd, h.root.inv_eq he] at hinv
    rcases h.root.orderOf_mul hd he with h2 | h4 | hodd
    · rw [commute_iff_eq]
      have hsq : (d * e) * (d * e) = 1 := by rw [← pow_two, ← h2, pow_orderOf_eq_one]
      calc d * e = (d * e)⁻¹ := (inv_eq_of_mul_eq_one_right hsq).symm
        _ = e⁻¹ * d⁻¹ := mul_inv_rev _ _
        _ = e * d := by rw [h.root.inv_eq he, h.root.inv_eq hd]
    · exfalso
      have hz2 : orderOf ((d * e) * (d * e)) = 2 := by
        apply orderOf_eq_prime
        · rw [show ((d * e) * (d * e)) = (d * e) ^ 2 by rw [pow_two]]
          rw [← pow_mul, show 2 * 2 = 4 from rfl, ← h4, pow_orderOf_eq_one]
        · intro hx1
          have hpow : (d * e) ^ 2 = 1 := by rw [pow_two]; exact hx1
          have hdvd : orderOf (d * e) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
          rw [h4] at hdvd
          exact absurd hdvd (by norm_num)
      have hdvdZ : orderOf ((d * e) * (d * e)) ∣ Nat.card (Subgroup.center X) :=
        Subgroup.orderOf_dvd_natCard _ hzmem
      rw [hz2] at hdvdZ
      exact (Nat.not_even_iff_odd.mpr h.odd_card_center) (even_iff_two_dvd.mpr hdvdZ)
    · obtain ⟨k, hk⟩ := hodd
      have hwZ : d * e ∈ Subgroup.center X := by
        have hpow : d * e = ((d * e) ^ 2) ^ (k + 1) := by
          calc d * e = (d * e) ^ (orderOf (d * e) + 1) := by
                rw [pow_succ, pow_orderOf_eq_one, one_mul]
            _ = (d * e) ^ (2 * (k + 1)) := by
                rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
            _ = ((d * e) ^ 2) ^ (k + 1) := by rw [pow_mul]
        rw [hpow, pow_two]
        exact Subgroup.pow_mem _ hzmem (k + 1)
      have hcomm : Commute d (d * e) := Subgroup.mem_center_iff.mp hwZ d
      have he_eq : e = d * (d * e) := by rw [← mul_assoc, h.root.mul_self_eq_one hd, one_mul]
      have hw2 : (d * e) * (d * e) = 1 := by
        have he2 : e * e = 1 := h.root.mul_self_eq_one he
        have hsq : e * e = (d * e) * (d * e) := by
          have h1 : e * e = (d * (d * e)) * (d * (d * e)) :=
            congrArg (fun x => x * x) he_eq
          rw [h1]
          calc (d * (d * e)) * (d * (d * e)) = (d * d) * ((d * e) * (d * e)) :=
                (hcomm.mul_mul_mul_comm d (d * e)).symm
            _ = (d * e) * (d * e) := by rw [h.root.mul_self_eq_one hd, one_mul]
        rw [← hsq]
        exact he2
      have hdvd : orderOf (d * e) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hw2)
      have hw1 : d * e = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact orderOf_eq_one_iff.mp h1
        · exfalso
          rw [h2] at hk
          omega
      have heq : e = d := by rw [he_eq, hw1, mul_one]
      rw [commute_iff_eq, heq]
  · intro hc
    exact hc.map (QuotientGroup.mk' (Subgroup.center X))

theorem map_rootGroup (h : Hyp X S) {d : X} (hd : d ∈ dSet S) :
    (CFSG.Timmesfeld.rootGroup (dSet S) d).map (QuotientGroup.mk' (Subgroup.center X)) =
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) d) := by
  simp only [CFSG.Timmesfeld.rootGroup]
  have hset : QuotientGroup.mk' (Subgroup.center X) ''
      CFSG.Timmesfeld.rootSet (dSet S) d =
      CFSG.Timmesfeld.rootSet (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) d) := by
    ext g
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨⟨e, he.1, rfl⟩, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      rw [commute_mk_iff h he.1 hf, commute_mk_iff h hd hf]
      exact he.2 f hf
    · rintro ⟨⟨e, he, rfl⟩, hg⟩
      refine ⟨e, ⟨he, ?_⟩, rfl⟩
      intro f hf
      have hh := hg (QuotientGroup.mk' (Subgroup.center X) f) ⟨f, hf, rfl⟩
      rwa [commute_mk_iff h he hf, commute_mk_iff h hd hf] at hh
  rw [MonoidHom.map_closure, hset]

theorem card_map_rootGroup (h : Hyp X S) {d : X} (hd : d ∈ dSet S) :
    Nat.card ((CFSG.Timmesfeld.rootGroup (dSet S) d).map
      (QuotientGroup.mk' (Subgroup.center X))) =
      Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) d) := by
  let W := CFSG.Timmesfeld.rootGroup (dSet S) d
  change Nat.card (W.map (QuotientGroup.mk' (Subgroup.center X))) = Nat.card W
  let φ : W →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp W.subtype
  have hpg : IsPGroup 2 W := CFSG.Timmesfeld.isPGroup_rootGroup h.root hd
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff φ, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff (x : X)).1 hx
    have hodd : Odd (orderOf (x : X)) :=
      Odd.of_dvd_nat h.odd_card_center (Subgroup.orderOf_dvd_natCard _ hxZ)
    obtain ⟨k, hk⟩ := hpg x
    have hdvd : orderOf (x : X) ∣ 2 ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j = 0 := by
      by_contra hjne
      rw [hj] at hodd
      exact (Nat.not_odd_iff_even.mpr (even_two.pow_of_ne_zero hjne)) hodd
    exact Subtype.ext (orderOf_eq_one_iff.mp (by rw [hj, hj0, pow_zero]))
  have hmap : (⊤ : Subgroup W).map φ = W.map (QuotientGroup.mk' (Subgroup.center X)) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hcard := Subgroup.card_map_of_injective (K := (⊤ : Subgroup W)) (f := φ) hφinj
  rw [hmap, Subgroup.card_top] at hcard
  exact hcard

theorem mem_dSet_of_mk_mem (h : Hyp X S) {w : X} (hw2 : w * w = 1)
    (hw : QuotientGroup.mk' (Subgroup.center X) w ∈
      QuotientGroup.mk' (Subgroup.center X) '' dSet S) : w ∈ dSet S := by
  obtain ⟨d, hd, hdw⟩ := hw
  have hz : d⁻¹ * w ∈ Subgroup.center X := QuotientGroup.eq.mp hdw
  have hdz : Commute d (d⁻¹ * w) := Subgroup.mem_center_iff.mp hz d
  have hdd : d * d = 1 := h.root.mul_self_eq_one hd
  have hz2 : (d⁻¹ * w) * (d⁻¹ * w) = 1 := by
    have hw' : w * w = (d * (d⁻¹ * w)) * (d * (d⁻¹ * w)) := by
      rw [show d * (d⁻¹ * w) = w by group]
    rw [hw'] at hw2
    calc (d⁻¹ * w) * (d⁻¹ * w) = (d * d) * ((d⁻¹ * w) * (d⁻¹ * w)) := by
          rw [hdd, one_mul]
      _ = (d * (d⁻¹ * w)) * (d * (d⁻¹ * w)) :=
          hdz.mul_mul_mul_comm d (d⁻¹ * w)
      _ = 1 := hw2
  have hz1 : d⁻¹ * w = 1 := by
    have hodd : Odd (orderOf (d⁻¹ * w)) :=
      Odd.of_dvd_nat h.odd_card_center (Subgroup.orderOf_dvd_natCard _ hz)
    have hdvd : orderOf (d⁻¹ * w) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hz2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      obtain ⟨j, hj⟩ := hodd
      rw [h2] at hj
      omega
  rw [← show d * (d⁻¹ * w) = w by group, hz1, mul_one]
  exact hd

theorem setup_quot (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4) :
    CFSG.Timmesfeld.Bridge.Asc72.Setup (X ⧸ Subgroup.center X)
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) :=
  ⟨CFSG.Timmesfeld.image_isClass_center h.exists_isClass,
   CFSG.Timmesfeld.image_isOddTransp_center h.root (fun d hd => h.not_mem_center hd) hdeg,
   CFSG.Timmesfeld.image_closure_eq_top_center h.closure_dSet⟩

theorem meetsSq_quot (h : Hyp X S) :
    ∃ u ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S,
      ∃ v ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S, u ≠ v ∧ Commute u v ∧
        u * v ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S := by
  obtain ⟨u, hu, v, hv, -, hc, huv⟩ := h.meetsSq
  refine ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, fun hh => h.not_mem_center huv ?_,
    hc.map (QuotientGroup.mk' (Subgroup.center X)), ⟨u * v, huv, map_mul _ _ _⟩⟩
  have hz : u⁻¹ * v ∈ Subgroup.center X := QuotientGroup.eq.mp hh
  rwa [h.root.inv_eq hu] at hz

theorem isOddTransp_conj_rootGroup (h : Hyp X S)
    (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4) {s : X}
    (hW : ∀ w ∈ CFSG.Timmesfeld.rootGroup (dSet S) s, w ≠ 1 → w ∈ dSet S) :
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp
      (Group.conjugatesOfSet ((CFSG.Timmesfeld.rootGroup (dSet S) s : Set X) \ {1})) := by
  have hsub : Group.conjugatesOfSet
      ((CFSG.Timmesfeld.rootGroup (dSet S) s : Set X) \ {1}) ⊆ dSet S := by
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨w, ⟨hwW, hw1⟩, hwy⟩ := hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hwy
    rw [← hc]
    exact conj_mem_dSet c (hW w hwW (by simpa using hw1))
  have hodd := h.isOddTransp_dSet hdeg
  exact ⟨fun d hd => hodd.1 d (hsub hd), fun d hd e he => hodd.2 d (hsub hd) e (hsub he)⟩

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
