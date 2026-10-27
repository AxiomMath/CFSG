module

public import CFSG.RankThree.PartOne.TCX.Tri.Skeleton
public import CFSG.RankThree.PartOne.KGD.D4Frame

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KGD

section Transfer

variable {C : Type} [Group C] {L : Type} [Field L] [CharP L 2] {p : ℕ}
  {ι : C →* ModGL TwistTag.D4.tag L}
  {F₀ Φ : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem IsShintani.frame_transfer (h : IsShintani p ι F₀ Φ α₀) (hp : p.Prime) {f₀ : ℕ}
    (hF₀ : F₀ = twistHom TwistTag.D4 L (iterateFrobenius L 2 f₀))
    {k : Type} [Field k] [Finite k] [Algebra k L] (σk : k ≃+* k)
    (hσk : ∀ c, σk c = c ^ 2 ^ f₀)
    {n g₀ : ModGL TwistTag.D4.tag L}
    (hfr₁ : ∀ P' : Subgroup (ModGL TwistTag.D4.tag L), P' ≤ adjointGroup TwistTag.D4.tag L →
      (∀ u ∈ P', F₀ u = u) → P' ≤ (triEmb k σk L).range)
    (hfr₂ : ∀ Q : Subgroup (graphFixedRootGroup TwistTag.D4 k σk.toRingHom), IsPGroup p Q →
      ∃ c : graphFixedRootGroup TwistTag.D4 k σk.toRingHom, ∀ y ∈ Q,
        g₀⁻¹ * triEmb k σk L (c * y * c⁻¹) * g₀ ∈ twistedTorusOf n F₀)
    {x : C} (hx : orderOf x = p) (hxα : α₀ x = x) :
    ∃ c : C, α₀ c = c ∧ g₀⁻¹ * ι (c * x * c⁻¹) * g₀ ∈ twistedTorusOf n F₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : (algebraMap k L).comp σk.toRingHom =
      (iterateFrobenius L 2 f₀).comp (algebraMap k L) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hσk, map_pow, iterateFrobenius_def]
  have hιx : F₀ (ι x) = ι x := (h.actor_fixed_iff x).1 hxα
  have hzp : Subgroup.zpowers (ι x) ≤ (triEmb k σk L).range := by
    refine hfr₁ _ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact h.mem x
    · rintro u hu
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [map_zpow, hιx]
  obtain ⟨x₀, hx₀⟩ := hzp (Subgroup.mem_zpowers (ι x))
  have hx₀ord : orderOf x₀ = p := by
    rw [← hx, ← orderOf_injective ι h.inj x, ← hx₀]
    exact (orderOf_injective _ triEmb_injective x₀).symm
  have hQ : IsPGroup p (Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀ord, pow_one])
  obtain ⟨c₀, hc₀⟩ := hfr₂ _ hQ
  have hfixc₀ : F₀ (triEmb k σk L c₀) = triEmb k σk L c₀ := by
    rw [hF₀]
    exact triEmb_fixed (K := k) (σ := σk) (L := L) (iterateFrobenius L 2 f₀) hcomm c₀
  obtain ⟨c, hc⟩ := h.fix_mem_range (triEmb_mem_adjointGroup c₀) hfixc₀
  refine ⟨c, ?_, ?_⟩
  · rw [h.actor_fixed_iff, hc, hfixc₀]
  · have := hc₀ x₀ (Subgroup.mem_zpowers x₀)
    rw [map_mul, map_mul, map_inv] at this
    rw [map_mul, map_mul, map_inv, hc, ← hx₀]
    exact this

end Transfer

end CFSG.RankThree.PartOne.TCX.Tri
