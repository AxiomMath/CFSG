module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_mixed_Z_conj
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hMs : x ∈ stabTil ⊥ V)
    (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)).map
      ((actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hMs⟩)⁻¹).toMonoidHom =
    commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) := by
  have hV := h.hyp151.isElemAbelian
  let xbar : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨x, hMs⟩
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L
  let Lx : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV (conjSubgroup L x)
  let U₁ : Subgroup (Vtil ⊥ V hV) := commSub ⊤ Lb
  let Z : Subgroup (Vtil ⊥ V hV) := U₁ ⊓ fixV Lb
  have hLx : Lx = Lb.map (MulAut.conj (xbar⁻¹)).toMonoidHom := by
    show lBar ⊥ V hV (conjSubgroup L x) =
      (lBar ⊥ V hV L).map (MulAut.conj (xbar⁻¹)).toMonoidHom
    exact s15_Infra_barSub_conjSubgroup ⊥ V hV hMs L
  have hUx : commSub ⊤ Lx = U₁.map (xbar⁻¹).toMonoidHom := by
    show commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) =
      (commSub ⊤ (lBar ⊥ V hV L)).map (xbar⁻¹).toMonoidHom
    exact s15_Infra_wTil_conjSubgroup ⊥ V L hV hMs
  have hfixX : fixV Lx = (fixV Lb).map (xbar⁻¹).toMonoidHom := by
    rw [hLx, fixV_map_conj_eq]
  have hle_fix : U₁ ≤ fixV Lx := by
    have hcom := (h.hyp151.commute x hxM hxn).2
    exact commSub_eq_bot_iff.mp (by simpa only [wTil, lBar, U₁, Lb, Lx] using hcom)
  have hZle : Z ≤ U₁.map (xbar⁻¹).toMonoidHom := by
    have hpreZ : wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) =
        preTil ⊥ V hV Z := by
      have hpre := s16h_wSub_inf_centralizer_eq_preTil D h
      simpa only [Z, U₁, Lb] using hpre
    have hpreX : conjSubgroup (wSub ⊥ V hV L) x =
        preTil ⊥ V hV (U₁.map (xbar⁻¹).toMonoidHom) := by
      have h := s15_Infra_preTil_map_actTil ⊥ V hV hMs U₁
      rw [show preTil ⊥ V hV U₁ = wSub ⊥ V hV L from rfl] at h
      exact h.symm
    have hmain : imgTil ⊥ V hV
        (wSub ⊥ V hV L ⊓ conjSubgroup (wSub ⊥ V hV L) x) = Z := by
      rw [hZ0, hpreZ, imgTil_preTil]
    rw [← hmain]
    calc imgTil ⊥ V hV (wSub ⊥ V hV L ⊓ conjSubgroup (wSub ⊥ V hV L) x)
        ≤ imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) x) :=
          s15_LP_imgTil_mono hV inf_le_right
      _ = U₁.map (xbar⁻¹).toMonoidHom := by rw [hpreX, imgTil_preTil]
  have hZmap : Z.map (xbar⁻¹).toMonoidHom =
      U₁.map (xbar⁻¹).toMonoidHom ⊓ fixV Lx := by
    rw [show Z = U₁ ⊓ fixV Lb from rfl,
      Subgroup.map_inf_eq U₁ (fixV Lb) (xbar⁻¹).toMonoidHom (xbar⁻¹).injective,
      ← hfixX]
  have hZsub : Z ≤ Z.map (xbar⁻¹).toMonoidHom := by
    rw [hZmap]
    exact le_inf hZle (inf_le_left.trans hle_fix)
  have hcard : Nat.card ↥(Z.map (xbar⁻¹).toMonoidHom) ≤ Nat.card ↥Z :=
    le_of_eq (Subgroup.card_map_of_injective (f := (xbar⁻¹).toMonoidHom) (xbar⁻¹).injective)
  exact (Subgroup.eq_of_le_of_card_ge hZsub hcard).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
