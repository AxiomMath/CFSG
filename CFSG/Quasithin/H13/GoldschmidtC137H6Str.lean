module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Alg
public import CFSG.Quasithin.H13.GoldschmidtC137H6Frm2

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem mem_o2Z_gc {L : Subgroup G} {z : G} :
    z ∈ A6.o2Z L ↔ ∃ hz : z ∈ L,
      (QuotientGroup.mk (⟨z, hz⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center _ := by
  unfold A6.o2Z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, h, rfl⟩

theorem o2Z_le_gc (L : Subgroup G) : A6.o2Z L ≤ L := Subgroup.map_subtype_le _

theorem comm_o2Z_gc {L : Subgroup G} {z y : G} (hz : z ∈ A6.o2Z L) (hy : y ∈ L) :
    z * y * z⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨hzL, hzc⟩ := mem_o2Z_gc.1 hz
  have h1 := Subgroup.mem_center_iff.1 hzc (QuotientGroup.mk ⟨y, hy⟩)
  have h2 : (QuotientGroup.mk (⟨z * y * z⁻¹ * y⁻¹, L.mul_mem (L.mul_mem (L.mul_mem hzL hy)
      (L.inv_mem hzL)) (L.inv_mem hy)⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
    have e : (⟨z * y * z⁻¹ * y⁻¹, L.mul_mem (L.mul_mem (L.mul_mem hzL hy)
        (L.inv_mem hzL)) (L.inv_mem hy)⟩ : ↥L) = ⟨z, hzL⟩ * ⟨y, hy⟩ * ⟨z, hzL⟩⁻¹ * ⟨y, hy⟩⁻¹ :=
      rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h1.symm
  exact coe_mem_pCoreOf_iff.2 ((QuotientGroup.eq_one_iff _).1 h2)

theorem mem_oTwoPhi_gc (L : Subgroup G) (x : G) :
    x ∈ oTwoPhi L ↔ ∃ hx : x ∈ L,
      (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.Open.pCore 2 ↥L) ∈
        frattini (↥L ⧸ CFSG.Open.pCore 2 ↥L) := by
  unfold oTwoPhi
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem o2Z_subgroupOf_le_oTwoPhi_gc {X L : Subgroup G} (hLX : L ≤ X)
    (hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (A6.o2Z L).subgroupOf X ≤ oTwoPhi (L.subgroupOf X) := by
  intro x hx
  obtain ⟨hxL, hxc⟩ := mem_o2Z_gc.1 (Subgroup.mem_subgroupOf.1 hx)
  have hxK : x ∈ L.subgroupOf X := hxL
  rw [mem_oTwoPhi_gc]
  refine ⟨hxK, ?_⟩
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  have hpc : CFSG.pCore 2 ↥L ≤
      (CFSG.Open.pCore 2 ↥(L.subgroupOf X)).comap e.symm.toMonoidHom := by
    intro w hw
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e.symm
    exact this ▸ ⟨w, hw, rfl⟩
  let φ := QuotientGroup.map (CFSG.pCore 2 ↥L) (CFSG.Open.pCore 2 ↥(L.subgroupOf X))
    e.symm.toMonoidHom hpc
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk (e y), by simp [φ]⟩
  have h1 := frattini_le_comap_frattini_of_surjective hφs (center_le_frattini_gc hperf hxc)
  exact h1

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem card_autI_L : Nat.card ↥(autI h.hVe L) = 360 := by
  obtain ⟨F⟩ := h.nonempty_frame
  rw [← F.hA, Subgroup.card_map_of_injective F.inj, card_alt6]

theorem relIndex_D : (L ⊓ centralizer (V : Set G)).relIndex L = 360 := by
  rw [← card_autI_eq h.hVe (h.hLX.trans h.hXN)]
  exact h.card_autI_L

theorem relIndex_o2Z : (A6.o2Z L).relIndex L = 360 := by
  have e : (A6.o2Z L).subgroupOf L = (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  unfold Subgroup.relIndex
  rw [e, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h1 := Subgroup.card_mul_index (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [h.hhat.2.1, card_of_hatA6 h.hhat] at h1
  omega

theorem o2Z_le_D : A6.o2Z L ≤ L ⊓ centralizer (V : Set G) := by
  obtain ⟨F⟩ := h.nonempty_frame
  intro z hz
  have hzL : z ∈ L := o2Z_le_gc L hz
  refine ⟨hzL, ?_⟩
  have hzN : z ∈ normalizer (V : Set G) := h.hXN (h.hLX hzL)
  have hφ : convI h.hVe ⟨z, hzN⟩ ∈ autI h.hVe L := convI_mem_autI h.hVe hzL hzN
  rw [← F.hA] at hφ
  obtain ⟨σ, hσ, hσφ⟩ := hφ
  have hcomm : ∀ τ ∈ alternatingGroup (Fin 6), σ * τ = τ * σ := by
    intro τ hτ
    have hτL : F.ρ τ ∈ autI h.hVe L := by
      rw [← F.hA]
      exact ⟨τ, hτ, rfl⟩
    obtain ⟨y, hyL, hy⟩ := (mem_autI h.hVe).1 hτL
    have hyN : (y : G) ∈ normalizer (V : Set G) := y.2
    have hk : z * y * z⁻¹ * y⁻¹ ∈ centralizer (V : Set G) :=
      h.pCoreOf_le_centralizer (comm_o2Z_gc hz hyL)
    set c : ↥(normalizer (V : Set G)) := ⟨z, hzN⟩ * y * ⟨z, hzN⟩⁻¹ * y⁻¹ with hc
    have hc1 : convI h.hVe c = 1 := (convI_eq_one_iff h.hVe c).2 hk
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, ← hσφ, hy, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at hc1
    rw [← map_mul, ← map_mul] at hc1
    exact F.inj hc1
  have hσ1 : σ = 1 := by
    have hcen : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 6))) ∈
        Subgroup.center ↥(alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g.1 g.2).symm
    rw [alternatingGroup.center_eq_bot (α := Fin 6) (by simp)] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
  have h1 : convI h.hVe ⟨z, hzN⟩ = 1 := by rw [← hσφ, hσ1, map_one]
  exact (convI_eq_one_iff h.hVe _).1 h1

theorem D_eq_o2Z : L ⊓ centralizer (V : Set G) = A6.o2Z L := by
  apply le_antisymm _ h.o2Z_le_D
  have h1 := Subgroup.relIndex_mul_relIndex (A6.o2Z L) (L ⊓ centralizer (V : Set G)) L
    h.o2Z_le_D inf_le_left
  rw [h.relIndex_D, h.relIndex_o2Z] at h1
  have h2 : (A6.o2Z L).relIndex (L ⊓ centralizer (V : Set G)) = 1 := by omega
  exact Subgroup.relIndex_eq_one.1 h2

theorem hB : (L ⊓ centralizer (V : Set G)).subgroupOf X ≤ oTwoPhi (L.subgroupOf X) := by
  rw [h.D_eq_o2Z]
  exact o2Z_subgroupOf_le_oTwoPhi_gc h.hLX h.hhat.1

end H6Ctx

end CFSG.Quasithin.H13.U3.GC137
