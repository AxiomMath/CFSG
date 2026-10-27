module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRep

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.GroupTheory
open CFSG.QuasithinUnique.Setup.X7
open CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H : Subgroup G} {N N₀ : Subgroup G}
variable [(N₀.subgroupOf N).Normal]

section Lattice

variable (hs : QuotMod.Hyp H N N₀)
variable [Module (ZMod 2) (SecMod hs)]

theorem subSec_inf_subSec_eq_bot {E F : Subgroup G} (hEF : E ⊓ (F ⊔ N₀) ≤ N₀) :
    subSec hs E ⊓ subSec hs F = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨hvE, hvF⟩ := Submodule.mem_inf.mp hv
  obtain ⟨n₁, hn₁⟩ := (mem_subSec_iff hs).1 hvE
  obtain ⟨n₂, hn₂⟩ := (mem_subSec_iff hs).1 hvF
  have heq : SecMod.mk hs (Subgroup.inclusion inf_le_right n₁) =
      SecMod.mk hs (Subgroup.inclusion inf_le_right n₂) := by rw [hn₁, hn₂]
  have hzero : SecMod.mk hs ((Subgroup.inclusion inf_le_right n₁ : ↥N)⁻¹ *
      Subgroup.inclusion inf_le_right n₂) = 0 := by
    rw [SecMod.mk_mul, SecMod.mk_inv, heq, neg_add_cancel]
  have hN₀ : (((Subgroup.inclusion inf_le_right n₁ : ↥N)⁻¹ *
      Subgroup.inclusion inf_le_right n₂ : ↥N) : G) ∈ N₀ :=
    (SecMod.mk_eq_zero_iff hs _).mp hzero
  have hcoe : (((Subgroup.inclusion inf_le_right n₁ : ↥N)⁻¹ *
      Subgroup.inclusion inf_le_right n₂ : ↥N) : G) = (n₁ : G)⁻¹ * (n₂ : G) := rfl
  rw [hcoe] at hN₀
  have hmem : (n₁ : G) ∈ E ⊓ (F ⊔ N₀) := by
    refine Subgroup.mem_inf.mpr ⟨n₁.2.1, ?_⟩
    have hrepr : (n₁ : G) = (n₂ : G) * ((n₁ : G)⁻¹ * (n₂ : G))⁻¹ := by group
    rw [hrepr]
    exact Subgroup.mul_mem_sup n₂.2.1 (N₀.inv_mem hN₀)
  have h1 : SecMod.mk hs (Subgroup.inclusion inf_le_right n₁) = 0 :=
    (SecMod.mk_eq_zero_iff hs _).mpr (by simpa using hEF hmem)
  rwa [← hn₁]

theorem natCard_subSec_mul_natCard_inf {E : Subgroup G} (hEN : E ≤ N)
    (hE : E ≤ Subgroup.normalizer (N₀ : Set G)) :
    Nat.card ↥(subSec hs E) * Nat.card ↥(E ⊓ N₀) = Nat.card ↥E := by
  have hN₀N : N₀ ≤ N := hs.le
  have hsub : subSec hs (E ⊔ N₀) = subSec hs E := by
    rw [subSec_sup hs hEN hN₀N, subSec_eq_bot_of_le hs le_rfl, sup_bot_eq]
  have h1 := natCard_subSec hs (le_sup_right : N₀ ≤ E ⊔ N₀) (sup_le hEN hN₀N)
  rw [hsub] at h1
  have h2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := E) (B := N₀) hE
  have h3 : Nat.card ↥(subSec hs E) * Nat.card ↥(E ⊓ N₀) * Nat.card N₀ =
      Nat.card E * Nat.card N₀ := by
    calc Nat.card ↥(subSec hs E) * Nat.card ↥(E ⊓ N₀) * Nat.card N₀
        = Nat.card ↥(subSec hs E) * Nat.card N₀ * Nat.card ↥(E ⊓ N₀) := by ring
      _ = Nat.card E * Nat.card N₀ := by rw [h1, h2]
  haveI : Nonempty ↥N₀ := ⟨⟨1, N₀.one_mem⟩⟩
  exact Nat.mul_right_cancel Nat.card_pos h3

end Lattice

end CFSG.RankThree.GF2n.Tim81
