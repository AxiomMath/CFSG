module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Step1
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
private theorem mem_zOf_iff {X : Subgroup G} {z : G} :
    z ∈ zOf X ↔ z ∈ X ∧ ∀ x ∈ X, x * z = z * x := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    exact ⟨hy, fun x hx => congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨x, hx⟩)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2), rfl⟩

private theorem isElemAbelian_map_aux {H K : Type*} [Group H] [Group K] {E : Subgroup H}
    (f : H →* K) (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem normal_of_le_zOf (h : Counterexample p A θ) {Z : Subgroup G}
    (hZ : Z ≤ zOf (sSup (Msig p A θ))) (hZA : A ≤ Subgroup.normalizer (Z : Set G)) :
    Z.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h.generation]
  refine sup_le ?_ hZA
  rw [Subgroup.le_normalizer_iff]
  intro x hx z hz
  rw [(mem_zOf_iff.mp (hZ hz)).2 x hx, mul_inv_cancel_right]
  exact hz

theorem exists_quotient_member (h : Counterexample p A θ) {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ zOf (sSup (Msig p A θ))) (hZ1 : Z ≠ ⊥) :
    ∃ N : Subgroup (G ⧸ Z), signalizerMcBrideHypothesisB p N ∧
      (sSup (Msig p A θ)).map (QuotientGroup.mk' Z) ≤ N ∧
      ∀ b ∈ A, b ≠ 1 → N ⊓ Subgroup.centralizer {QuotientGroup.mk' Z b} ≤
        (θ b).map (QuotientGroup.mk' Z) := by
  have hAZ : ∀ a ∈ A, a ∈ Z → a = 1 := fun a ha haZ =>
    h.eq_one_of_mem_centralizer_sSup_msig ha
      (Subgroup.mem_centralizer_iff.mpr fun x hx => (mem_zOf_iff.mp (hZ haZ)).2 x hx)
  have hinj : Set.InjOn (QuotientGroup.mk' Z) A := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ Z := QuotientGroup.eq.mp hab
    exact inv_mul_eq_one.mp (hAZ _ (A.mul_mem (A.inv_mem ha) hb) h1)
  have hne1 : ∀ a ∈ A, a ≠ 1 → QuotientGroup.mk' Z a ≠ 1 := fun a ha ha1 hπ =>
    ha1 (hinj ha A.one_mem (hπ.trans (map_one _).symm))
  have hAq : IsElemAbelian p (A.map (QuotientGroup.mk' Z)) :=
    isElemAbelian_map_aux _ h.elemAbelian
  have hcardAq : Nat.card (A.map (QuotientGroup.mk' Z)) = p ^ 3 := by
    rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hinj,
      SetLike.coe_sort_coe, h.card]
  have hθq : IsFunctor p (A.map (QuotientGroup.mk' Z)) (imageFunctor (QuotientGroup.mk' Z) A θ) :=
    h.isFunctor.imageFunctor h.prime h.elemAbelian hinj
  have hC : ∀ y ∈ A.map (QuotientGroup.mk' Z), y ≠ 1 →
      signalizerMcBrideHypothesisB p (imageFunctor (QuotientGroup.mk' Z) A θ y) := by
    rintro _ ⟨a, ha, rfl⟩ hy1
    have ha1 : a ≠ 1 := fun h' => hy1 (by rw [h', map_one])
    rw [imageFunctor_apply hinj ha]
    exact (isSigClass_hypBClass.{u} p).quotient (N := Z) G h.elemAbelian
      (h.isFunctor.normalized a ha ha1) (h.isFunctor.coprime a ha ha1) (h.hypC a ha ha1)
  have hcard : Nat.card (G ⧸ Z) < Nat.card G := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z]
    exact lt_mul_of_one_lt_right Nat.card_pos (Z.one_lt_card_iff_ne_bot.mpr hZ1)
  obtain ⟨N, hN, hNmax⟩ := h.ih (G ⧸ Z) hcard (A.map (QuotientGroup.mk' Z))
    (imageFunctor (QuotientGroup.mk' Z) A θ) ⟨h.prime, h.odd, hAq, hcardAq, hθq, hC⟩
  refine ⟨N, hN.2.2.2, ?_, fun b hb hb1 => ?_⟩
  · rw [h.sSup_msig_eq_thetaSup, Subgroup.map_le_iff_le_comap]
    refine thetaSup_le fun a ha ha1 => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← imageFunctor_apply hinj ha]
    exact hNmax _ (hθq.apply_mem_signalizers (Subgroup.mem_map_of_mem _ ha) (hne1 a ha ha1)
      (hC _ (Subgroup.mem_map_of_mem _ ha) (hne1 a ha ha1)))
  · rw [← imageFunctor_apply hinj hb]
    exact hN.2.2.1 _ (Subgroup.mem_map_of_mem _ hb) (hne1 b hb hb1)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
