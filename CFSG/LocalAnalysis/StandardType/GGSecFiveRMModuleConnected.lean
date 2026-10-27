module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

section Module

private lemma ggLinMove_le_of_mem
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {W : Submodule (ZMod p) V} {a : V ≃ₗ[ZMod p] V}
    (ha : GGLinRefl a) {x : V} (hx : x ∈ ggLinMove a) (hx0 : x ≠ 0) (hxW : x ∈ W) :
    ggLinMove a ≤ W := by
  have hspan : ggLinMove a = Submodule.span (ZMod p) ({x} : Set V) :=
    eq_span_singleton_of_mem_of_finrank_eq_one ha.2 hx hx0
  rw [hspan]
  exact (Submodule.span_singleton_le_iff_mem x W).mpr hxW

private lemma ggLinMove_le_of_move
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {S : Set (V ≃ₗ[ZMod p] V)} {W : Submodule (ZMod p) V}
    (hS : ∀ r ∈ S, GGLinRefl r)
    (hW : ∀ a ∈ Subgroup.closure S, ∀ w ∈ W, a w ∈ W)
    {r : V ≃ₗ[ZMod p] V} (hr : r ∈ S) {w : V} (hw : w ∈ W) (hrw : r w ≠ w) :
    ggLinMove r ≤ W := by
  have hrW : r w ∈ W := hW r (Subgroup.subset_closure hr) w hw
  have hmem' : r w - w ∈ ggLinMove r :=
    LinearMap.mem_range_self (r.toLinearMap - LinearMap.id) w
  have hmem : w - r w ∈ ggLinMove r := by
    simpa only [neg_sub] using neg_mem hmem'
  exact ggLinMove_le_of_mem (hS r hr) hmem (sub_ne_zero.mpr (Ne.symm hrw)) (sub_mem hw hrW)

private lemma ggLinMove_le_of_adj
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {S : Set (V ≃ₗ[ZMod p] V)} {W : Submodule (ZMod p) V}
    (hS : ∀ r ∈ S, GGLinRefl r)
    (hW : ∀ a ∈ Subgroup.closure S, ∀ w ∈ W, a w ∈ W)
    {a b : V ≃ₗ[ZMod p] V} (ha : a ∈ S) (hb : b ∈ S) (hab : GGLinAdj a b)
    (haW : ggLinMove a ≤ W) : ggLinMove b ≤ W := by
  obtain ⟨v, hv, hbv⟩ := hab.2
  have hvW : v ∈ W := haW hv
  have hbW : b v ∈ W := hW b (Subgroup.subset_closure hb) v hvW
  have hmem : b v - v ∈ ggLinMove b :=
    LinearMap.mem_range_self (b.toLinearMap - LinearMap.id) v
  exact ggLinMove_le_of_mem (hS b hb) hmem (sub_ne_zero.mpr hbv) (sub_mem hbW hvW)

theorem ggLin_propagate_connected
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (S : Set (V ≃ₗ[ZMod p] V)) (hS : ∀ r ∈ S, GGLinRefl r)
    (hconn : ∀ r ∈ S, ∀ s ∈ S, Relation.EqvGen (fun a b => a ∈ S ∧ b ∈ S ∧ GGLinAdj a b) r s)
    (W : Submodule (ZMod p) V) (hW : ∀ a ∈ Subgroup.closure S, ∀ w ∈ W, a w ∈ W)
    (hmove : ∃ r ∈ S, ∃ w ∈ W, r w ≠ w) : ∀ s ∈ S, ggLinMove s ≤ W := by
  obtain ⟨r₀, hr₀, w₀, hw₀, hr₀w₀⟩ := hmove
  have hbase : ggLinMove r₀ ≤ W := ggLinMove_le_of_move hS hW hr₀ hw₀ hr₀w₀
  intro s hs
  have hiff : (ggLinMove r₀ ≤ W) ↔ (ggLinMove s ≤ W) :=
    Relation.EqvGen.recOn (hconn r₀ hr₀ s hs)
      (motive := fun a b _ => ggLinMove a ≤ W ↔ ggLinMove b ≤ W)
      (fun a b hab =>
        ⟨fun ha => ggLinMove_le_of_adj hS hW hab.1 hab.2.1 hab.2.2 ha,
         fun hb => ggLinMove_le_of_adj hS hW hab.2.1 hab.1 ⟨hab.2.2.2, hab.2.2.1⟩ hb⟩)
      (fun _ => Iff.rfl)
      (fun _ _ _ ih => ih.symm)
      (fun _ _ _ _ _ ihab ihbc => ihab.trans ihbc)
  exact hiff.mp hbase

end Module

end CFSG.StandardType

end
