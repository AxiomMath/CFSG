module

public import CFSG.Sporadic.SuzRecog.Generation
public import CFSG.Sporadic.SuzRecog.EndSEGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification
  CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.RankTwoStandard
  CFSG.OddStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem card_centralizer_conj (c t : G) :
    Nat.card (centralizer ({c * t * c⁻¹} : Set G)) = Nat.card (centralizer ({t} : Set G)) :=
  (card_centralizer_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩)).symm

omit [Finite G] in
private theorem card_centralizer_subgroup {Y : Subgroup G} (t : Y) :
    Nat.card (centralizer ({t} : Set Y)) =
      Nat.card ↥(Y ⊓ centralizer ({(t : G)} : Set G)) := by
  have h : (centralizer ({t} : Set Y)).map Y.subtype = Y ⊓ centralizer ({(t : G)} : Set G) := by
    ext x
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hxY, hx⟩
      exact ⟨⟨x, hxY⟩, Subtype.ext hx, rfl⟩
  rw [← h, card_map_of_injective Y.subtype_injective]

private theorem isConj_and_le {Y : Subgroup G} {a b : Y}
    (hcls : ∀ y : Y, orderOf y = 2 → IsConj a y ∨ IsConj b y)
    (hCa : Nat.card (centralizer ({a} : Set Y)) = 3317760)
    (hCb : Nat.card (centralizer ({b} : Set Y)) = 161280) {t : G} (htY : t ∈ Y)
    (ht : orderOf t = 2) (hC : Nat.card (centralizer ({t} : Set G)) = 3317760) :
    IsConj a ⟨t, htY⟩ ∧ centralizer ({t} : Set G) ≤ Y := by
  have ht' : orderOf (⟨t, htY⟩ : Y) = 2 := by rwa [Subgroup.orderOf_mk]
  have hcard := card_centralizer_subgroup (⟨t, htY⟩ : Y)
  have hdvd : Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) ∣ 3317760 :=
    hC ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases hcls _ ht' with h | h
  · rw [← card_centralizer_eq_of_isConj h, hCa] at hcard
    refine ⟨h, fun x hx => ?_⟩
    have heq : Y ⊓ centralizer ({t} : Set G) = centralizer ({t} : Set G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [← hcard, hC])
    exact (heq.ge hx).1
  · rw [← card_centralizer_eq_of_isConj h, hCb] at hcard
    rw [← hcard] at hdvd
    norm_num at hdvd

omit [Finite G] in
private theorem le_of_inf_centralizer_le {A Y : Subgroup G}
    (hodd : Odd (Nat.card (center A))) (eA : rankTwoQuot A ≃* PSL3Four.S) {z : G}
    (hzA : z ∈ A) (hzY : z ∈ Y) (hz : orderOf z = 2)
    (hC : ∀ t ∈ A, t ∈ Y → orderOf t = 2 → A ⊓ centralizer ({t} : Set G) ≤ Y) : A ≤ Y := by
  set q : A →* PSL3Four.S := eA.toMonoidHom.comp (QuotientGroup.mk' (center A)) with hqdef
  have hq : Function.Surjective q := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ k : A, q k = 1 ↔ k ∈ center A := fun k => by
    simp [hqdef, QuotientGroup.eq_one_iff]
  have hkodd : ∀ k ∈ center A, Odd (orderOf k) := fun k hk => by
    have h := orderOf_dvd_natCard (⟨k, hk⟩ : center A)
    rw [Subgroup.orderOf_mk] at h
    exact hodd.of_dvd_nat h
  have hZY : ∀ k ∈ center A, (k : G) ∈ Y := fun k hk =>
    hC z hzA hzY hz ⟨k.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hk ⟨z, hzA⟩)).symm⟩
  have hord : ∀ t : A, orderOf t = 2 → orderOf (q t) = 2 := by
    intro t ht
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    refine orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) fun h1 => ?_
    have h := hkodd t ((hker t).mp h1)
    rw [ht] at h
    exact (Nat.not_even_iff_odd.mpr h) even_two
  set H : Subgroup A := Y.subgroupOf A with hHdef
  have htop : H.map q = ⊤ := by
    refine EndSEGen.eq_top_of_involution_centralizers
      ⟨q ⟨z, hzA⟩, ⟨⟨z, hzA⟩, hzY, rfl⟩, hord _ (by rwa [Subgroup.orderOf_mk])⟩ ?_
    rintro _ ⟨h, hhH, rfl⟩ hx2 yb hyb
    obtain ⟨y, rfl⟩ := hq yb
    set m := Nat.card (center A) with hm
    have hh2 : h ^ 2 ∈ center A := (hker _).mp (by rw [map_pow, ← hx2, pow_orderOf_eq_one])
    have hpow : (h ^ 2) ^ m = 1 := by
      have hd := orderOf_dvd_natCard (⟨h ^ 2, hh2⟩ : center A)
      rw [Subgroup.orderOf_mk] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hqt : q (h ^ m) = q h := by
      obtain ⟨j, hj⟩ := hodd
      rw [hj, map_pow, pow_succ, pow_mul, ← hx2, pow_orderOf_eq_one, one_pow, one_mul]
    have ht2 : orderOf (h ^ m) = 2 := by
      refine orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul, hpow]) fun h1 => ?_
      rw [h1, map_one] at hqt
      rw [← hqt, orderOf_one] at hx2
      omega
    have htH : h ^ m ∈ H := H.pow_mem hhH m
    have hcomm : y * h ^ m = h ^ m * y := by
      have hc := mem_centralizer_singleton_iff.mp hyb
      have hk : (y * h ^ m * y⁻¹)⁻¹ * h ^ m ∈ center A := by
        refine (hker _).mp ?_
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, hqt, hc]
        group
      have hv2 : orderOf (y * h ^ m * y⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact ht2
      have h1 := Seitz77.L34.eq_one_of_two_power_of_odd (y := h ^ m) (v := y * h ^ m * y⁻¹)
        (k := (y * h ^ m * y⁻¹)⁻¹ * h ^ m) (by group) ⟨1, by rw [hv2, pow_one]⟩
        ⟨1, by rw [ht2, pow_one]⟩ (Subgroup.mem_center_iff.mp hk _) (hkodd _ hk)
      rw [inv_mul_eq_one] at h1
      calc y * h ^ m = y * h ^ m * y⁻¹ * y := by group
        _ = h ^ m * y := by rw [h1]
    have hyY : (y : G) ∈ Y := by
      refine hC _ (h ^ m).2 htH ?_
        ⟨y.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)⟩
      rw [Subgroup.orderOf_coe]
      exact ht2
    exact ⟨y, hyY, rfl⟩
  intro x hx
  obtain ⟨h, hhH, hh⟩ : q ⟨x, hx⟩ ∈ H.map q := htop ▸ mem_top _
  have hk : h⁻¹ * ⟨x, hx⟩ ∈ center A := (hker _).mp (by rw [map_mul, map_inv, hh, inv_mul_cancel])
  have h1 := Y.mul_mem hhH (hZY _ hk)
  simpa using h1

theorem eq_top_of_component_of_card [IsSimpleGroup G]
    {z : G} (hz : orderOf z = 2)
    (hcard : Nat.card (centralizer ({z} : Set G)) = 3317760) {Y : Subgroup G} (e : Y ≃* suzM)
    (hzY : z ∈ Y) {A R : Subgroup G} (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center A))) (hzA : z ∈ A) (hRA : R ≤ centralizer (A : Set G))
    (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    (hN : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G)) : Y = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hcls, -, hCa, hCb, -⟩ := exists_involution_classes_suz e
  obtain ⟨eA⟩ := PSL3Four.nonempty_equiv_of_stated _ hL
  have hA2 : ∀ t ∈ A, orderOf t = 2 → Nat.card (centralizer ({t} : Set G)) = 3317760 := by
    intro t htA ht
    obtain ⟨c, -, rfl⟩ := Seitz77.involutions_conj_of_mem hodd eA hzA htA hz ht
    rw [card_centralizer_conj, hcard]
  have hAY : ∀ t ∈ A, t ∈ Y → orderOf t = 2 → centralizer ({t} : Set G) ≤ Y :=
    fun t htA htY ht => (isConj_and_le hcls hCa hCb htY ht (hA2 t htA ht)).2
  have hCz : centralizer ({z} : Set G) ≤ Y := hAY z hzA hzY hz
  have hza : IsConj a ⟨z, hzY⟩ := (isConj_and_le hcls hCa hCb hzY hz hcard).1
  have hAle : A ≤ Y := le_of_inf_centralizer_le hodd eA hzA hzY hz
    fun t htA htY ht => inf_le_right.trans (hAY t htA htY ht)
  have h7 : 7 ∣ Nat.card A := by
    have h := (center A).card_eq_card_quotient_mul_card_subgroup
    rw [show Nat.card (↥A ⧸ center ↥A) = 20160 by
      rw [Nat.card_congr eA.toEquiv, PSL3Four.card_S]] at h
    rw [h]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp fun h : R = ⊥ => by
    rw [h, card_bot] at hR4
    omega
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hr2 : orderOf r = 2 := orderOf_eq_prime (hRe.2 r hrR) hr1'
  have hrA := mem_centralizer_iff.mp (hRA hrR)
  have hAr : A ≤ centralizer ({r} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hrA x hx)
  have hrY : r ∈ Y := hCz (mem_centralizer_singleton_iff.mpr (hrA z hzA).symm)
  have hzr : ∀ g : G, g * z * g⁻¹ ≠ r := by
    intro g hg
    have hd := Subgroup.card_dvd_of_le hAr
    rw [← hg, card_centralizer_conj, hcard] at hd
    exact absurd (h7.trans hd) (by norm_num)
  have hrb : IsConj b ⟨r, hrY⟩ := by
    rcases hcls ⟨r, hrY⟩ (by rwa [Subgroup.orderOf_mk]) with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.mp (hza.symm.trans h)
      exact absurd (congrArg Subtype.val hc) (hzr c)
    · exact h
  have hCr : centralizer ({r} : Set G) ≤ Y := by
    intro x hx
    have hxz : x * z * x⁻¹ ∈ A := (mem_normalizer_iff.mp (hN r hrR hr1' hx) z).mp hzA
    have hxz2 : orderOf (x * z * x⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hz
    obtain ⟨c, hcA, hc⟩ := Seitz77.involutions_conj_of_mem hodd eA hxz hzA hxz2 hz
    have hcx : c * x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * x * z = c * (x * z * x⁻¹) * c⁻¹ * (c * x) := by group
        _ = z * (c * x) := by rw [hc]
    have h := Y.mul_mem (Y.inv_mem (hAle hcA)) (hCz hcx)
    rwa [inv_mul_cancel_left] at h
  set T : Set G := {z, r} with hTdef
  have hCT : ∀ t ∈ T, centralizer ({t} : Set G) ≤ Y := by
    intro t ht
    simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hCz
    · exact hCr
  have hT : ∀ u ∈ Y, orderOf u = 2 → ∃ t ∈ T, ∃ c ∈ Y, c * u * c⁻¹ = t := by
    intro u hu hu2
    rcases hcls ⟨u, hu⟩ (by rwa [Subgroup.orderOf_mk]) with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.mp (h.symm.trans hza)
      exact ⟨z, Set.mem_insert z _, c, c.2, congrArg Subtype.val hc⟩
    · obtain ⟨c, hc⟩ := isConj_iff.mp (h.symm.trans hrb)
      exact ⟨r, Set.mem_insert_of_mem z (Set.mem_singleton r), c, c.2, congrArg Subtype.val hc⟩
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, ∀ g : G, g * t * g⁻¹ = t' → ∃ c ∈ Y, c * t * c⁻¹ = t' := by
    intro t ht t' ht' g hg
    simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ht ht'
    rcases ht with ht | ht <;> rcases ht' with ht' | ht'
    · exact ⟨1, Y.one_mem, by rw [ht, ht']; group⟩
    · rw [ht, ht'] at hg
      exact absurd hg (hzr g)
    · rw [ht, ht'] at hg
      refine absurd ?_ (hzr g⁻¹)
      rw [← hg]
      group
    · exact ⟨1, Y.one_mem, by rw [ht, ht']; group⟩
  have hcent : ∀ u ∈ Y, orderOf u = 2 → centralizer ({u} : Set G) ≤ Y := by
    intro u hu hu2 y hy
    obtain ⟨t, ht, c, hc, h⟩ := hT u hu hu2
    have hy' : c * y * c⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hy ⊢
      rw [← h]
      calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
        _ = c * (u * y) * c⁻¹ := by rw [hy]
        _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
    have h1 := Y.mul_mem (Y.mul_mem (Y.inv_mem hc) (hCT t ht hy')) hc
    simpa [mul_assoc] using h1
  have hev : Even (Nat.card Y) := by
    refine even_iff_two_dvd.mpr ?_
    rw [← hz, ← Subgroup.orderOf_mk z hzY]
    exact orderOf_dvd_natCard _
  have : IsSimpleGroup Y := e.isSimpleGroup_congr.mpr suzM_isSimpleGroup
  refine HeSE.eq_top_of_fusion inferInstance hRe hR4 Y hev (HeSE.fusion_of_reps Y T hT hTT)
    hcent ?_
  intro P _ hPcard hPY hYN
  have hPn : (P.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hPY).mpr hYN
  have h2G : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
  have hpos : 0 < (Nat.card G).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' h2G
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf Y) with h | h
  · have hP1 : Nat.card P = 1 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hPY).toEquiv, h, card_bot]
    rw [hPcard] at hP1
    have := Nat.one_lt_two_pow hpos.ne'
    omega
  · have hYP : Y ≤ P := subgroupOf_eq_top.mp h
    have hd := Subgroup.card_dvd_of_le (hAle.trans hYP)
    rw [hPcard] at hd
    have h72 := (show Nat.Prime 7 by norm_num).dvd_of_dvd_pow (h7.trans hd)
    norm_num at h72

theorem eq_top_of_component [IsSimpleGroup G]
    (S : CFSG.LargeExtraspecial.Setting G) (hcard : Nat.card S.M = 3317760)
    {Y : Subgroup G} (e : Y ≃* suzM) (hzY : S.z ∈ Y) {A R : Subgroup G}
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center A))) (hzA : S.z ∈ A)
    (hRA : R ≤ centralizer (A : Set G)) (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    (hN : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G)) : Y = ⊤ :=
  eq_top_of_component_of_card S.orderOf_z hcard e hzY hL hodd hzA hRA hRe hR4 hN

end CFSG.Sporadic.SuzRecog
