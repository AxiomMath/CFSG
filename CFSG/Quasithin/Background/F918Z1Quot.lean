module

public import CFSG.Quasithin.Background.F918Z1Core
public import CFSG.Quasithin.Background.F918Z0Def
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace D37Lift

variable {V : Type} [CommGroup V]

theorem le_stabSub_fixV (H : Subgroup (MulAut V)) : H ≤ stabSub (fixV H) :=
  fun g hg => centSub_le_stabSub (fixV H) (show g ∈ centSub (fixV H) from fun _ hu => hu g hg)

@[expose] def toQuot (C : Subgroup V) (H : Subgroup (MulAut V)) (hH : H ≤ stabSub C) :
    ↥H →* ↥(autQuot H C) :=
  ((quotHom C).comp (Subgroup.inclusion hH)).codRestrict (autQuot H C)
    (fun g => mem_autQuot.2 ⟨Subgroup.inclusion hH g, g.2, rfl⟩)

theorem toQuot_surjective (C : Subgroup V) (H : Subgroup (MulAut V)) (hH : H ≤ stabSub C) :
    Function.Surjective (toQuot C H hH) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hgH, hg⟩ := mem_autQuot.1 hφ
  exact ⟨⟨g.1, hgH⟩, Subtype.ext hg⟩

theorem comm_autQuot {C : Subgroup V} {D X : Subgroup (MulAut V)}
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) :
    ∀ φ ∈ autQuot D C, ∀ ψ ∈ autQuot X C, φ * ψ = ψ * φ := by
  intro φ hφ ψ hψ
  obtain ⟨g, hgD, rfl⟩ := mem_autQuot.1 hφ
  obtain ⟨x, hxX, rfl⟩ := mem_autQuot.1 hψ
  rw [← map_mul, ← map_mul]
  exact congrArg (quotHom C) (Subtype.ext (hcomm g.1 hgD x.1 hxX))

theorem irr_autQuot {C : Subgroup V} {D X : Subgroup (MulAut V)} (hD : D ≤ stabSub C)
    (hX : X ≤ stabSub C)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → C ≤ U → U = C ∨ U = ⊤) :
    ∀ U' : Subgroup (V ⧸ C),
      (∀ φ ∈ autQuot D C ⊔ autQuot X C, ∀ u ∈ U', φ u ∈ U') → U' = ⊥ ∨ U' = ⊤ := by
  intro U' hU'
  let U : Subgroup V := U'.comap (QuotientGroup.mk' C)
  have hmem : ∀ v, v ∈ U ↔ (QuotientGroup.mk v : V ⧸ C) ∈ U' := fun v => Iff.rfl
  have hCU : C ≤ U := fun c hc => by
    rw [hmem, (QuotientGroup.eq_one_iff c).2 hc]
    exact U'.one_mem
  have hstab : ∀ (H : Subgroup (MulAut V)), H ≤ stabSub C →
      (∀ φ ∈ autQuot H C, ∀ u ∈ U', φ u ∈ U') → H ≤ stabSub U := by
    intro H hH hφ
    have hfwd : ∀ g ∈ H, ∀ u ∈ U, g u ∈ U := fun g hg u hu =>
      hφ (quotHom C ⟨g, hH hg⟩) (mem_autQuot.2 ⟨⟨g, hH hg⟩, hg, rfl⟩) (QuotientGroup.mk u) hu
    intro g hg u
    refine ⟨fun h => ?_, hfwd g hg u⟩
    have h' := hfwd g⁻¹ (H.inv_mem hg) _ h
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h'
  have hD' := hstab D hD fun φ hφ => hU' φ (Subgroup.mem_sup_left hφ)
  have hX' := hstab X hX fun φ hφ => hU' φ (Subgroup.mem_sup_right hφ)
  have hinv : ∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U :=
    fun g hg u hu => ((mem_stabSub.1 (sup_le hD' hX' hg)) u).2 hu
  rcases hirr U hinv hCU with h | h
  · left
    refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    have hv : v ∈ C := h ▸ (hmem v).2 hq
    exact (QuotientGroup.eq_one_iff v).2 hv
  · right
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    exact (hmem v).1 (h ▸ Subgroup.mem_top v)

end D37Lift

theorem fixV_eq_bot_of_hasMatModel {V : Type} [CommGroup V] (hexp : ∀ v : V, v ^ 2 = 1)
    {D X : Subgroup (MulAut V)} (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hV : commV (D ⊔ X) = ⊤)
    (hDnt : ¬ D ≤ centSec ⊤ (fixV (D ⊔ X))) (hXnt : ¬ X ≤ centSec ⊤ (fixV (D ⊔ X)))
    (hmodel : HasMatModel (autQuot D (fixV (D ⊔ X))) (autQuot X (fixV (D ⊔ X)))) :
    fixV (D ⊔ X) = ⊥ := by
  obtain ⟨F, _, _, _, d, r, β, ρ, σ, -, -, hM⟩ := hmodel
  have hD : D ≤ stabSub (fixV (D ⊔ X)) := le_sup_left.trans (D37Lift.le_stabSub_fixV (D ⊔ X))
  have hX : X ≤ stabSub (fixV (D ⊔ X)) := le_sup_right.trans (D37Lift.le_stabSub_fixV (D ⊔ X))
  have I_irr' : ∀ W : AddSubgroup (Fin d → F),
      (∀ g : ↥D, ∀ w ∈ W,
        ((ρ.comp (D37Lift.toQuot _ D hD) g : Matrix.GeneralLinearGroup (Fin d) F) :
          Matrix (Fin d) (Fin d) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hM.I_irr W fun g' w hw => ?_
    obtain ⟨g, rfl⟩ := D37Lift.toQuot_surjective _ D hD g'
    exact hW g w hw
  have U_irr' : ∀ W : Submodule F (Fin r → F),
      (∀ x : ↥X, ∀ w ∈ W,
        ((σ.comp (D37Lift.toQuot _ X hX) x : Matrix.GeneralLinearGroup (Fin r) F) :
          Matrix (Fin r) (Fin r) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hM.U_irr W fun x' w hw => ?_
    obtain ⟨x, rfl⟩ := D37Lift.toQuot_surjective _ X hX x'
    exact hW x w hw
  have hρnt : ∃ g : ↥D, (ρ.comp (D37Lift.toQuot _ D hD)) g ≠ 1 := by
    by_contra hcon
    have h1 : ∀ g : ↥D, ρ (D37Lift.toQuot _ D hD g) = 1 :=
      fun g => by_contra fun hne => hcon ⟨g, hne⟩
    refine hDnt fun g hg => ⟨fun u => iff_of_true trivial trivial, fun w _ => ?_⟩
    have h2 := hM.hρ (D37Lift.toQuot _ D hD ⟨g, hg⟩) (QuotientGroup.mk w)
    rw [h1 ⟨g, hg⟩, Units.val_one, Matrix.one_mul, ofAdd_toAdd] at h2
    have h3 : (QuotientGroup.mk (g w) : V ⧸ fixV (D ⊔ X)) = QuotientGroup.mk w := β.injective h2
    exact (mk_eq_mk_iff _ _).1 h3
  have hσnt : ∃ x : ↥X, (σ.comp (D37Lift.toQuot _ X hX)) x ≠ 1 := by
    by_contra hcon
    have h1 : ∀ x : ↥X, σ (D37Lift.toQuot _ X hX x) = 1 :=
      fun x => by_contra fun hne => hcon ⟨x, hne⟩
    refine hXnt fun x hx => ⟨fun u => iff_of_true trivial trivial, fun w _ => ?_⟩
    have h2 := hM.hσ (D37Lift.toQuot _ X hX ⟨x, hx⟩) (QuotientGroup.mk w)
    rw [h1 ⟨x, hx⟩, Units.val_one, Matrix.transpose_one, Matrix.mul_one, ofAdd_toAdd] at h2
    have h3 : (QuotientGroup.mk (x w) : V ⧸ fixV (D ⊔ X)) = QuotientGroup.mk w := β.injective h2
    exact (mk_eq_mk_iff _ _).1 h3
  have key := ker_eq_bot_of_matModel hexp hcomm hV (QuotientGroup.mk' (fixV (D ⊔ X)))
    (QuotientGroup.mk'_surjective _) (le_of_eq (QuotientGroup.ker_mk' _)) β
    (ρ.comp (D37Lift.toQuot _ D hD)) (σ.comp (D37Lift.toQuot _ X hX))
    (fun g v => hM.hρ (D37Lift.toQuot _ D hD g) (QuotientGroup.mk v))
    (fun x v => hM.hσ (D37Lift.toQuot _ X hX x) (QuotientGroup.mk v)) I_irr' U_irr' hρnt hσnt
  rwa [QuotientGroup.ker_mk'] at key

end CFSG.Quasithin
