module

public import CFSG.Adapters.Involutions
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_of_ne_one_of_card_two (U : Subgroup G) (hcard : Nat.card U = 2)
    {z x : G} (hz : z ∈ U) (hzne : z ≠ 1) (hx : x ∈ U) (hxne : x ≠ 1) : x = z := by
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : U)).mp hcard
  have hx' : (⟨x, hx⟩ : U) ≠ 1 := fun h => hxne (congrArg Subtype.val h)
  have hz' : (⟨z, hz⟩ : U) ≠ 1 := fun h => hzne (congrArg Subtype.val h)
  exact congrArg Subtype.val ((hw _ hx').trans (hw _ hz').symm)

omit [Finite G] in
theorem weak_closure_of_order_two (T : Sylow 2 G) (z : G) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    ∀ g : G, g⁻¹ * z * g ∈ (T : Subgroup G) → g⁻¹ * z * g = z := by
  intro g hg
  apply eq_of_ne_one_of_card_two (Subgroup.zpowers z)
    (by simpa only [Nat.card_zpowers] using hz) (Subgroup.mem_zpowers z)
    (by intro h; simp [h] at hz) (hclosed z (Subgroup.mem_zpowers z) g hg)
  intro h
  have heq : (MulAut.conj g⁻¹) z = (MulAut.conj g⁻¹) 1 := by
    simpa only [MulAut.conj_apply, inv_inv, map_one] using h
  have hone := (MulAut.conj g⁻¹).injective heq
  simp [hone] at hz

omit [Finite G] in
theorem central_in_sylow_of_order_two (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) := by
  apply Subgroup.mem_center_iff.mpr
  intro t
  apply Subtype.ext
  have hfixed := weak_closure_of_order_two T z hz hclosed (t : G)
    ((T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem t.property) hzT) t.property)
  change (t : G) * z = z * (t : G)
  calc
    (t : G) * z = (t : G) * ((t : G)⁻¹ * z * t) := by rw [hfixed]
    _ = z * (t : G) := by group

theorem zStar_of_order_two (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    (∀ g : G, ∃ c ∈ Subgroup.centralizer ({z} : Set G), ∃ k ∈ oddCore G, g = c * k) ∧
      (QuotientGroup.mk z : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) := by
  exact CFSG.Adapters.glauberman_zStar T ⟨z, hzT⟩
    (central_in_sylow_of_order_two T z hzT hz hclosed)
    (by simpa only [Subgroup.orderOf_mk] using hz)
    (weak_closure_of_order_two T z hz hclosed)

theorem order_two_hull_image (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    (Subgroup.normalClosure (Subgroup.zpowers z : Set G)).map
      (QuotientGroup.mk' (oddCore G)) =
        Subgroup.zpowers (QuotientGroup.mk z : G ⧸ oddCore G) := by
  let π := QuotientGroup.mk' (oddCore G)
  have hcentral := (zStar_of_order_two T z hzT hz hclosed).2
  have hle : Subgroup.zpowers (π z) ≤ Subgroup.center (G ⧸ oddCore G) :=
    Subgroup.zpowers_le.mpr hcentral
  let : (Subgroup.zpowers (π z)).Normal := Subgroup.normal_of_le_center hle
  have himage : π '' (Subgroup.zpowers z : Set G) =
      (Subgroup.zpowers (π z) : Set (G ⧸ oddCore G)) := by
    rw [← Subgroup.coe_map, MonoidHom.map_zpowers]
  change (Subgroup.normalClosure (Subgroup.zpowers z : Set G)).map π =
    Subgroup.zpowers (π z)
  rw [Subgroup.map_normalClosure _ π (QuotientGroup.mk'_surjective _), himage]
  exact Subgroup.normalClosure_eq_self _

theorem quotient_order_two {z : G} (hz : orderOf z = 2) :
    orderOf (QuotientGroup.mk z : G ⧸ oddCore G) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · have hpow : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    change (QuotientGroup.mk' (oddCore G)) z ^ 2 = 1
    simpa only [map_pow, map_one] using congrArg (QuotientGroup.mk' (oddCore G)) hpow
  · intro hone
    exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz
      ((QuotientGroup.eq_one_iff z).mp hone)

theorem order_two_odd_core_hull (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    let L := Subgroup.normalClosure (Subgroup.zpowers z : Set G)
    (oddCore L).map L.subtype = L ⊓ oddCore G ∧
      L = (oddCore L).map L.subtype ⊔ Subgroup.zpowers z ∧ (oddCore L).index = 2 := by
  dsimp only
  let L := Subgroup.normalClosure (Subgroup.zpowers z : Set G)
  let R := oddCore G
  let π := QuotientGroup.mk' R
  have hcore : (oddCore L).map L.subtype = L ⊓ R := by
    exact CFSG.ComponentClassification.OddCore.normal_intersection G L
  have hcoreInternal : oddCore L = R.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hcore, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hUL : Subgroup.zpowers z ≤ L := Subgroup.subset_normalClosure
  have himage : L.map π = Subgroup.zpowers (π z) :=
    order_two_hull_image T z hzT hz hclosed
  have hcover : L = (oddCore L).map L.subtype ⊔ Subgroup.zpowers z := by
    rw [hcore]
    apply le_antisymm
    · intro x hx
      have hπx : π x ∈ (Subgroup.zpowers z).map π := by
        rw [MonoidHom.map_zpowers, ← himage]
        exact Subgroup.mem_map_of_mem π hx
      obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hπx
      have hwR : u⁻¹ * x ∈ R := by
        have hkernel : u⁻¹ * x ∈ π.ker := by
          change π (u⁻¹ * x) = 1
          rw [map_mul, map_inv, heq, inv_mul_cancel]
        simpa only [π, QuotientGroup.ker_mk'] using hkernel
      have hwL : u⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hUL hu)) hx
      have hujoin : u ∈ L ⊓ R ⊔ Subgroup.zpowers z :=
        (show Subgroup.zpowers z ≤ L ⊓ R ⊔ Subgroup.zpowers z from le_sup_right) hu
      have hwjoin : u⁻¹ * x ∈ L ⊓ R ⊔ Subgroup.zpowers z :=
        (show L ⊓ R ≤ L ⊓ R ⊔ Subgroup.zpowers z from le_sup_left) ⟨hwL, hwR⟩
      have hprod := (L ⊓ R ⊔ Subgroup.zpowers z).mul_mem hujoin hwjoin
      simpa only [mul_inv_cancel_left] using hprod
    · exact sup_le inf_le_left hUL
  have hindex : (oddCore L).index = 2 := by
    have hrel := Subgroup.relIndex_ker L π
    rw [show π.ker = R from QuotientGroup.ker_mk' R, himage, Nat.card_zpowers] at hrel
    change (R.subgroupOf L).index = orderOf (π z) at hrel
    rw [← hcoreInternal] at hrel
    exact hrel.trans (quotient_order_two hz)
  exact ⟨hcore, hcover, hindex⟩

theorem no_order_two_strongly_closed [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G))
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) : Nat.card U ≠ 2 := by
  intro hcard
  have hUne : U ≠ ⊥ := by intro h; simp [h] at hcard
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  have hzU : (z : G) ∈ U := z.property
  have hzneG : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  let zG : G := z
  have hz : orderOf zG = 2 := by
    have hdiv : orderOf zG ∣ 2 := hcard ▸ Subgroup.orderOf_dvd_natCard U hzU
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact False.elim (hzneG (orderOf_eq_one_iff.mp h))
    · exact h
  have hUeq : Subgroup.zpowers zG = U :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzU)
      (by rw [Nat.card_zpowers, hz, hcard])
  have hclosedZ : fusionStronglyClosed (Subgroup.zpowers zG : Set G) (T : Subgroup G) :=
    hUeq.symm ▸ hclosed
  have hstar := zStar_of_order_two T zG (hUT hzU) hz hclosedZ
  have hcore : oddCore G = ⊥ := by
    rcases (inferInstance : (oddCore G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz
        (h.symm ▸ Subgroup.mem_top zG))
  have hzcenter : zG ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hstar.1 g
    have hkone : k = 1 := Subgroup.mem_bot.mp (hcore ▸ hk)
    simpa only [hkone, mul_one] using Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcenter : Subgroup.center G = ⊤ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact False.elim (hzneG (Subgroup.mem_bot.mp (h ▸ hzcenter)))
    · exact h
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (Subgroup.mem_center_iff.mp (hcenter.symm ▸ Subgroup.mem_top b) a)

end CFSG.ShultStronglyClosedTI
