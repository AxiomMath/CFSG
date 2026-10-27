module

public import CFSG.Quasithin.Vol2.Ch10SecERho

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

@[expose] def wFour : Fin 5 → ZMod 2 := ![1, 1, 1, 1, 0]

theorem wFour_isEven : isEven wFour := by decide

theorem wFour_ne_zero : wFour ≠ 0 := by decide

theorem pact_rA_of_fix : ∀ x : Fin 5 → ZMod 2, isEven x → pact SecE.sA x = x →
    pact SecE.sB x = x → pact SecE.rA x = x ∨ pact SecE.rA x = x + wFour := by
  decide +kernel

theorem pact_vFour_of_fix : ∀ σ ∈ SecE.vFour, ∀ x : Fin 5 → ZMod 2, isEven x →
    pact SecE.sA x = x → pact SecE.sB x = x → pact σ x = x ∨ pact σ x = pact SecE.rA x := by
  decide +kernel

theorem eq_of_fix_rA : ∀ x : Fin 5 → ZMod 2, isEven x → pact SecE.sA x = x →
    pact SecE.sB x = x → pact SecE.rA x = x → x = 0 ∨ x = wFour := by
  decide +kernel

theorem pact_wFour_of_fix : ∀ σ : Perm (Fin 5), σ 4 = 4 → pact σ wFour = wFour := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : SecE.Case2Data hyp t)

@[expose] noncomputable def coord₁ (u : ↥(commV D.K₁)) : Fin 5 → ZMod 2 :=
  ((Multiplicative.toAdd (D.β₁ u) : evenWeight 5) : Fin 5 → ZMod 2)

theorem coord₁_injective : Function.Injective (coord₁ D) := by
  intro u u' h
  apply D.β₁.injective
  apply Multiplicative.toAdd.injective
  exact Subtype.ext h

theorem coord₁_mul (u u' : ↥(commV D.K₁)) : coord₁ D (u * u') = coord₁ D u + coord₁ D u' := by
  unfold coord₁
  rw [map_mul, toAdd_mul, AddSubgroup.coe_add]

theorem coord₁_isEven (u : ↥(commV D.K₁)) : isEven (coord₁ D u) :=
  (Multiplicative.toAdd (D.β₁ u)).2

theorem coord₁_apply (k : ↥D.K₁) (u : ↥(commV D.K₁)) :
    coord₁ D ⟨(k : MulAut _) (u : _), commV_invariant D.K₁ _ k.2 _ u.2⟩ =
      pact (D.θ₁ k) (coord₁ D u) :=
  SecE.coord_apply D.θ₁ D.β₁ D.equiv₁ k u

@[expose] noncomputable def vOneW : ↥(commV D.K₁) :=
  D.β₁.symm (Multiplicative.ofAdd ⟨wFour, wFour_isEven⟩)

theorem coord₁_vOneW : coord₁ D (vOneW D) = wFour := by
  simp [coord₁, vOneW]

theorem vOneW_ne_one : vOneW D ≠ 1 := by
  intro h
  have := coord₁_vOneW D
  rw [h] at this
  apply wFour_ne_zero
  rw [← this]
  simp [coord₁]

theorem coord₁_symm_apply (σ : Perm (Fin 5)) (u : ↥(commV D.K₁)) :
    coord₁ D ⟨((D.θ₁.symm σ : ↥D.K₁) : MulAut _) (u : _),
      commV_invariant D.K₁ _ (D.θ₁.symm σ).2 _ u.2⟩ = pact σ (coord₁ D u) := by
  rw [coord₁_apply, MulEquiv.apply_symm_apply]

theorem pact_eq_of_fix (u : ↥(commV D.K₁))
    (hu : ∀ p ∈ D.K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T),
      (p : MulAut _) (u : _) = u) {σ : Perm (Fin 5)} (hσ : σ ∈ SecE.eFour) :
    pact σ (coord₁ D u) = coord₁ D u := by
  rw [← coord₁_symm_apply]
  congr 1
  apply Subtype.ext
  refine hu _ ((D.memP₁ _ (D.θ₁.symm σ).2).mpr ?_)
  simpa using hσ

theorem rho_apply_of_fix (u : ↥(commV D.K₁))
    (hu : ∀ p ∈ D.K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T), p u.1 = u.1) :
    (D.θ₁.symm SecE.rA).1 u.1 = u.1 ∨ (D.θ₁.symm SecE.rA).1 u.1 = (u * vOneW D).1 := by
  have hA := pact_eq_of_fix D u hu (σ := SecE.sA) (by decide)
  have hB := pact_eq_of_fix D u hu (σ := SecE.sB) (by decide)
  have h2 := coord₁_symm_apply D SecE.rA u
  rcases pact_rA_of_fix _ (coord₁_isEven D u) hA hB with h | h
  · left
    rw [h] at h2
    exact congrArg Subtype.val (coord₁_injective D h2)
  · right
    rw [h, ← coord₁_vOneW D, ← coord₁_mul] at h2
    exact congrArg Subtype.val (coord₁_injective D h2)

theorem apply_of_mem_autI_inf_L (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two)
    (h2 : Ch10.Case10_1_1Two T L I) {g : MulAut (IntMod (fsuVM T L I)
      (SecA.isElemAbelian_fsuVM hyp))} (hg : g ∈ autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L))
    (u : ↥(commV D.K₁))
    (hu : ∀ p ∈ D.K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T), p u.1 = u.1) :
    g u.1 = u.1 ∨ g u.1 = (D.θ₁.symm SecE.rA).1 u.1 := by
  have hgK : g ∈ D.K₁ := oTwoUpper_le _ (D.autI_inf_L_le hg)
  have hσ := (D.mem_autI_inf_L_iff h37 h38 h322 h2 g hgK).mp hg
  have hA := pact_eq_of_fix D u hu (σ := SecE.sA) (by decide)
  have hB := pact_eq_of_fix D u hu (σ := SecE.sB) (by decide)
  have h1 := coord₁_apply D ⟨g, hgK⟩ u
  rcases pact_vFour_of_fix _ hσ _ (coord₁_isEven D u) hA hB with h | h
  · left
    rw [h] at h1
    exact congrArg Subtype.val (coord₁_injective D h1)
  · right
    rw [h, ← coord₁_symm_apply D SecE.rA u] at h1
    exact congrArg Subtype.val (coord₁_injective D h1)

end CFSG.Quasithin.Vol2.Ch10.SecF
