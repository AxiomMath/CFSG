module

public import CFSG.Quasithin.EmptyFaithful.SBc11Ctx
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.SBc8V2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc11

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

private theorem exists_fixed_of_isPGroup {X E : Subgroup G} (hX : IsPGroup 2 X)
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hcard : 2 ∣ Nat.card E) :
    ∃ w ∈ E, w ≠ 1 ∧ ∀ x ∈ X, x * w * x⁻¹ = w := by
  have hconj : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun x hx e he =>
    (Subgroup.mem_normalizer_iff.mp (hXE hx) e).mp he
  let _ : MulAction X E :=
    { smul := fun x e => ⟨x * e * x⁻¹, hconj x x.2 e e.2⟩
      one_smul := fun e => Subtype.ext (by
        show ((1 : X) : G) * e * ((1 : X) : G)⁻¹ = e
        simp)
      mul_smul := fun x y e => Subtype.ext (by
        show ((x * y : X) : G) * e * ((x * y : X) : G)⁻¹ = x * (y * e * y⁻¹) * (x : G)⁻¹
        simp [mul_assoc]) }
  have h0 : (1 : E) ∈ MulAction.fixedPoints X E := by
    rw [MulAction.mem_fixedPoints]
    intro x
    exact Subtype.ext (by
      show (x : G) * 1 * (x : G)⁻¹ = 1
      simp)
  obtain ⟨b, hb, hb1⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hcard h0
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun x hx => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨x, hx⟩)

private theorem lemma_15_3_8_of_ctx (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    omegaOneCenterOf (Sgp153 T V₁) =
        VZ T M ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) ∧
      Nat.card ↥(omegaOneCenterOf (Sgp153 T V₁)) = 4 := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have h8 := hyp.hyp.lemma_15_3_8 hyp.decomp
  refine ⟨h8.1, ?_⟩
  rw [h8.1]
  exact h8.2

private theorem exists_omegaOneCenter_not_central (h113 : StageLemma14113)
    (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    ∃ w : G, w ∈ omegaOneCenterOf (Sgp153 T V₁) ∧ w ∉ centerOf I := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  obtain ⟨-, -, -, -, hsyl, -⟩ := ctx_basic c
  have hYI : Yp ≤ I := c.c27.Yp_le.trans (ctx_basic c).2.1
  have hSM : Sgp153 T V₁ ≤ M ⊓ I := le_inf (inf_le_right.trans c.c29.norm_le) hsyl.1
  obtain ⟨-, -, hMN, hV₂card, hV₂fix⟩ := SBc8.V₂_facts h113 c.toCtx15330
  obtain ⟨w, hwV, hw1, hwfix⟩ := exists_fixed_of_isPGroup hsyl.2.1 (hSM.trans hMN)
    (by rw [hV₂card]; exact ⟨2, rfl⟩)
  refine ⟨w, ?_, fun hwc => ?_⟩
  · rw [(lemma_15_3_8_of_ctx c).1]
    refine ⟨hyp.decomp.le₂ hwV, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have := hwfix s hs
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · obtain ⟨y, hy, hne⟩ := hV₂fix w hwV hw1
    have hcomm : y * w = w * y := Subgroup.mem_centralizer_iff.mp hwc.2 y (hYI hy)
    exact hne (by rw [hcomm, mul_inv_cancel_right])

theorem not_isC134Case5 (h113 : StageLemma14113) (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    ¬ IsC134Case5 I (Sgp153 T V₁) L := by
  intro h5
  obtain ⟨w, hwZ, hwI⟩ := exists_omegaOneCenter_not_central h113 c
  obtain ⟨-, -, -, -, hsyl, -⟩ := ctx_basic c
  exact hwI ((h5.2 (Sgp153 T V₁) hsyl le_rfl).1 hwZ)

end Ctx

end SBc11

end CFSG.Quasithin
