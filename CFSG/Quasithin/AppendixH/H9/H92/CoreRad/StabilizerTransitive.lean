module

public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.StabMat

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem exists_linearEquiv_apply_eq_of_ne_local {F W : Type*} [Field F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {x y : W} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : W ≃ₗ[F] W, g x = y := by
  let f : (F ∙ x) ≃ₗ[F] (F ∙ y) :=
    (LinearEquiv.toSpanNonzeroSingleton F W x hx).symm ≪≫ₗ
      (LinearEquiv.toSpanNonzeroSingleton F W y hy)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  have h1 := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [← h1]
  have h2 : (LinearEquiv.toSpanNonzeroSingleton F W x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp
  simp [f, h2]

private theorem exists_GL_mulVec_eq_linearEquiv {n : ℕ}
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    ∃ T : GL (Fin n) (ZMod 2), ∀ x, (T : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = g x := by
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).symm g),
    fun x => ?_⟩
  have h := Matrix.GeneralLinearGroup.toLin_apply
    (Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).symm g)) x
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm.trans rfl

private theorem exists_linearEquiv_stab_apply_eq {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (D : Submodule F V) {w w' : V} (hw : w ∈ D)
    (hw' : w' ∈ D) (hw0 : w ≠ 0) (hw0' : w' ≠ 0) :
    ∃ g : V ≃ₗ[F] V, (∀ x, g x ∈ D ↔ x ∈ D) ∧ g w = w' := by
  obtain ⟨f, hf⟩ := exists_linearEquiv_apply_eq_of_ne_local (F := F) (W := D)
    (x := ⟨w, hw⟩) (y := ⟨w', hw'⟩) (fun h => hw0 (congrArg Subtype.val h))
    (fun h => hw0' (congrArg Subtype.val h))
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (W := D) (W' := D) f
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, ?_⟩
  · have h1 := hg (f.symm ⟨g x, hx⟩)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : ((f.symm ⟨g x, hx⟩ : D) : V) = x := g.injective h1.symm
    rw [← h2]
    exact (f.symm ⟨g x, hx⟩).2
  · have h1 : g x = ((f ⟨x, hx⟩ : D) : V) := (hg ⟨x, hx⟩).symm
    rw [h1]
    exact (f ⟨x, hx⟩).2
  · have h1 := hg ⟨w, hw⟩
    rw [hf] at h1
    exact h1.symm

theorem exists_mem_stabMat_mulVec_eq {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    {w w' : Fin n → ZMod 2} (hw : w ∈ D) (hw' : w' ∈ D) (hw0 : w ≠ 0) (hw0' : w' ≠ 0) :
    ∃ T ∈ stabMat n D, (T : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
  obtain ⟨g, hg1, hg2⟩ := exists_linearEquiv_stab_apply_eq (F := ZMod 2) (V := Fin n → ZMod 2) D
    hw hw' hw0 hw0'
  obtain ⟨T, hT⟩ := exists_GL_mulVec_eq_linearEquiv g
  refine ⟨T, fun x => ?_, ?_⟩
  · rw [hT]
    exact hg1 x
  · rw [hT]
    exact hg2

private theorem two_dvd_natCard_generic {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (D : Submodule (ZMod 2) V) (hD : D ≠ ⊥) : 2 ∣ Nat.card D := by
  have : Module.Finite (ZMod 2) D := Module.Finite.of_finite
  have h1 : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D), Nat.card_zmod]
  have : Nontrivial D := Submodule.nontrivial_iff_ne_bot.mpr hD
  have h2 : 0 < Module.finrank (ZMod 2) D := Module.finrank_pos
  rw [h1]
  exact dvd_pow_self 2 h2.ne'

theorem two_dvd_natCard_of_ne_bot {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hD : D ≠ ⊥) : 2 ∣ Nat.card D :=
  two_dvd_natCard_generic (V := Fin n → ZMod 2) D hD

end CFSG.ASVolI.ChH
