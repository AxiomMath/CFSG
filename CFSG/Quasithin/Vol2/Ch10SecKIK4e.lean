module

public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative Pointwise

variable {G : Type} [Group G]

theorem blockZ_le (J : Subgroup G) : blockZ J ≤ blockU J := inf_le_left

theorem le_normalizer_blockZ (J : Subgroup G) :
    J ≤ Subgroup.normalizer ((blockZ J : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.1 hz.2 g hg).symm

theorem blockU_comm {J : Subgroup G} (hs : IsShort2 J) {x y : G} (hx : x ∈ blockU J)
    (hy : y ∈ blockU J) : x * y = y * x := by
  have h := hs.2.2.1.1 hx
  exact (Subgroup.mem_centralizer_iff.mp h.2 y (hs.2.2.1.1 hy).1).symm

theorem le_blockU {J W : Subgroup G} (hWQ : W ≤ pCoreOf 2 J) (hcomm : ⁅W, J⁆ = W) :
    W ≤ blockU J := by
  rw [← hcomm]
  exact Subgroup.commutator_mono hWQ le_rfl

theorem inf_blockZ_eq_bot {J W : Subgroup G} [IsMulCommutative ↥W]
    (hfix : fixV (autOn J W) = ⊥) : W ⊓ blockZ J = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hle := InternalSec.le_fixV_autOn (U := W) (L := J)
    (Cg := Subgroup.centralizer (J : Set G)) inf_le_right
  rw [hfix] at hle
  have hmem : (⟨x, hx.1⟩ : ↥W) ∈ (Subgroup.centralizer (J : Set G)).subgroupOf W :=
    Subgroup.mem_subgroupOf.2 hx.2.2
  have h1 := hle hmem
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

theorem sup_blockZ_eq {J W : Subgroup G} (hs : IsShort2 J) (hWU : W ≤ blockU J)
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) (hJC : ¬ J ≤ Subgroup.centralizer (W : Set G)) :
    W ⊔ blockZ J = blockU J := by
  rcases hs.2.2.2.2.2 (W ⊔ blockZ J) le_sup_right (sup_le hWU (blockZ_le J))
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨hJW hg, le_normalizer_blockZ J hg⟩) with h | h
  · exfalso
    apply hJC
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwZ : w ∈ blockZ J := h ▸ Subgroup.mem_sup_left hw
    exact (Subgroup.mem_centralizer_iff.mp hwZ.2 j hj).symm
  · exact h

theorem blockU_le (J : Subgroup G) : blockU J ≤ J := by
  unfold blockU blockQ
  rw [Subgroup.commutator_le]
  intro q hq j hj
  have hqJ : q ∈ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J hq
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem hqJ hj) (J.inv_mem hqJ)) (J.inv_mem hj)

instance blockZ_subgroupOf_normal (J : Subgroup G) :
    ((blockZ J).subgroupOf (blockU J)).Normal := by
  refine ⟨fun z hz u => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 (u : G) (blockU_le J u.2)
  have e : ((u * z * u⁻¹ : ↥(blockU J)) : G) = (z : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, mul_inv_cancel_right]
  rw [e]
  exact hz

noncomputable def quotMap {J X : Subgroup G} (hXU : X ≤ blockU J) :
    ↥X →* ↥(blockU J) ⧸ (blockZ J).subgroupOf (blockU J) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion hXU)

theorem quotMap_bijective {J X : Subgroup G} (hs : IsShort2 J) (hXU : X ≤ blockU J)
    (hinf : X ⊓ blockZ J = ⊥) (hsup : X ⊔ blockZ J = blockU J) :
    Function.Bijective (quotMap hXU) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion hXU x ∈ (blockZ J).subgroupOf (blockU J) :=
      (QuotientGroup.eq_one_iff _).1 hx
    have h2 : (x : G) ∈ X ⊓ blockZ J := ⟨x.2, Subgroup.mem_subgroupOf.1 h1⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  · intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    have hXN : X ≤ Subgroup.normalizer ((blockZ J : Subgroup G) : Set G) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact blockU_comm hs (blockZ_le J hz) (hXU hx)
    have hu : (u : G) ∈ (X : Set G) * (blockZ J : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right X (blockZ J) hXN, hsup]
      exact u.2
    obtain ⟨x, hx, z, hz, hxz⟩ := hu
    refine ⟨⟨x, hx⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hXU ⟨x, hx⟩) = QuotientGroup.mk u
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((Subgroup.inclusion hXU ⟨x, hx⟩)⁻¹ * u : ↥(blockU J)) : G) = z := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hxz, inv_mul_cancel_left]
    rw [e]
    exact hz

theorem card_eq_index {J X : Subgroup G} (hs : IsShort2 J) (hXU : X ≤ blockU J)
    (hinf : X ⊓ blockZ J = ⊥) (hsup : X ⊔ blockZ J = blockU J) :
    Nat.card ↥X = ((blockZ J).subgroupOf (blockU J)).index :=
  (Nat.card_congr (Equiv.ofBijective _ (quotMap_bijective hs hXU hinf hsup))).trans
    (Subgroup.index_eq_card _).symm

theorem eq_bot_or_eq_of_le [Finite G] {J W : Subgroup G} (hs : IsShort2 J) (hWU : W ≤ blockU J)
    (hinf : W ⊓ blockZ J = ⊥) (hsup : W ⊔ blockZ J = blockU J) {X : Subgroup G} (hXW : X ≤ W)
    (hJX : J ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ ∨ X = W := by
  have hXU := hXW.trans hWU
  have hXinf : X ⊓ blockZ J = ⊥ := le_bot_iff.1 (hinf ▸ inf_le_inf_right _ hXW)
  rcases hs.2.2.2.2.2 (X ⊔ blockZ J) le_sup_right (sup_le hXU (blockZ_le J))
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨hJX hg, le_normalizer_blockZ J hg⟩) with h | h
  · left
    rw [eq_bot_iff, ← hXinf]
    exact le_inf le_rfl (h ▸ le_sup_left)
  · right
    refine Subgroup.eq_of_le_of_card_ge hXW ?_
    rw [card_eq_index hs hWU hinf hsup, card_eq_index hs hXU hXinf h]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
