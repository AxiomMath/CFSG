module

public import CFSG.Quasithin.H13.L32A520b
public import CFSG.Quasithin.H13.L32A520a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_card_quot (Y : Subgroup G) :
    (pCoreOf 2 Y).relIndex Y = Nat.card (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) := by
  rw [relIndex_eq_card_map le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.card_top]

theorem comm_mem_of_relIndex_le {Y K : Subgroup G} (hKY : K ≤ Y)
    (h3 : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 Y) (h9 : (pCoreOf 2 Y).relIndex K ≤ 9) :
    ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := (pCoreOf 2 Y).subgroupOf Y with hN
  set K' := (K.subgroupOf Y).map (QuotientGroup.mk' N) with hK'
  have hcard : Nat.card K' ≤ 3 ^ 2 := by rw [hK', ← relIndex_eq_card_map hKY]; exact h9
  have hp : IsPGroup 3 K' := by
    rintro ⟨q, hq⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h3 _ (Subgroup.mem_subgroupOf.mp hk))
  have hcomm := commutative_of_card_le_prime_sq hp hcard
  intro x hx y hy
  have hxK' : QuotientGroup.mk' N ⟨x, hKY hx⟩ ∈ K' := ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hyK' : QuotientGroup.mk' N ⟨y, hKY hy⟩ ∈ K' := ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have h1 := congrArg Subtype.val (hcomm ⟨_, hxK'⟩ ⟨_, hyK'⟩)
  simp only [Subgroup.coe_mul] at h1
  have h2 : QuotientGroup.mk' N
      (⟨x, hKY hx⟩ * ⟨y, hKY hy⟩ * ⟨x, hKY hx⟩⁻¹ * ⟨y, hKY hy⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact Subgroup.mem_subgroupOf.mp h2

omit [Finite G] in
theorem le_normalizer_of_comm_mem {Φ K Y : Subgroup G} (hΦK : Φ ≤ K)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ Φ) (hKY : K ≤ Y) :
    Y ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun y hy k hk => by
    rw [show y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k by group]
    exact mul_mem (hΦK (hcomm y hy k (hKY hk))) hk
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact key y hy k
  · intro hk
    have := key y⁻¹ (inv_mem hy) _ hk
    simpa [mul_assoc] using this

omit [Finite G] in
theorem center_eq_commutator_of_isPOnePlusTwo {X : Type*} [Group X] (h : IsPOnePlusTwo 3 X) :
    Subgroup.center X = commutator X := by
  obtain ⟨hex, hcard, -⟩ := h
  have hZ3 : Nat.card (Subgroup.center X) = 3 := CFSG.IsExtraspecial.center_order_p 3 X
  have hab := (CFSG.IsExtraspecial.quotient_elementary_abelian 3 X).toIsMulCommutative
  have hle : commutator X ≤ Subgroup.center X := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      mul_comm' (x : X ⧸ Subgroup.center X) (y : X ⧸ Subgroup.center X)]
    group
  have hne : commutator X ≠ ⊥ := by
    intro hb
    have hc : Subgroup.center X = ⊤ := by
      refine eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => ?_
      have : ⁅y, x⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    rw [hc, Subgroup.card_top, hcard] at hZ3
    norm_num at hZ3
  have : Fact (Nat.card ↥(Subgroup.center X)).Prime := ⟨by rw [hZ3]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((commutator X).subgroupOf (Subgroup.center X))
    with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(Subgroup.center X)) ∈
        (commutator X).subgroupOf (Subgroup.center X) := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · refine le_antisymm (fun z hz => ?_) hle
    have : (⟨z, hz⟩ : ↥(Subgroup.center X)) ∈ (commutator X).subgroupOf (Subgroup.center X) := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem o2z_le_of_comm_mem {Y K : Subgroup G}
    (hP : IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)) (hQK : pCoreOf 2 Y ≤ K)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ K) : o2z Y ≤ K := by
  set N := (pCoreOf 2 Y).subgroupOf Y with hN
  have hYK : commutator ↥Y ≤ K.subgroupOf Y := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using hcomm x x.2 y y.2)
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hc : QuotientGroup.mk' N w ∈ commutator (↥Y ⧸ N) := by
    rw [← center_eq_commutator_of_isPOnePlusTwo hP]
    exact Subgroup.mem_comap.mp hw
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
    ← Subgroup.map_commutator] at hc
  obtain ⟨c, hcY, hcw⟩ := Subgroup.mem_map.mp hc
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcw
  have h1 : (c : G) ∈ K := Subgroup.mem_subgroupOf.mp (hYK (by rwa [commutator_def]))
  have h2 : ((c⁻¹ * w : ↥Y) : G) ∈ K := hQK (Subgroup.mem_subgroupOf.mp hcw)
  have e : (w : G) = (c : G) * ((c⁻¹ * w : ↥Y) : G) := by simp
  show (w : G) ∈ K
  rw [e]
  exact mul_mem h1 h2

omit [Finite G] in
theorem comm_mem_o2z {Y : Subgroup G}
    (hP : IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)) :
    ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ o2z Y := by
  intro x hx y hy
  set N := (pCoreOf 2 Y).subgroupOf Y with hN
  refine ⟨⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹, Subgroup.mem_comap.mpr ?_, rfl⟩
  rw [center_eq_commutator_of_isPOnePlusTwo hP, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

omit [Finite G] in
theorem relIndex_o2z {Y : Subgroup G}
    (hP : IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)) :
    (pCoreOf 2 Y).relIndex (o2z Y) = 3 := by
  have := hP.1
  rw [relIndex_eq_card_map (o2z_le Y)]
  have e : (o2z Y).subgroupOf Y = (Subgroup.center (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)).comap
      (QuotientGroup.mk' ((pCoreOf 2 Y).subgroupOf Y)) :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  rw [e, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  exact CFSG.IsExtraspecial.center_order_p 3 _

end CFSG.Quasithin.H13.L32A
