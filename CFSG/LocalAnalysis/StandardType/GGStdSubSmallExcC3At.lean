module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Lift

public section

namespace CFSG.StandardType.SmallExc

open scoped MatrixGroups
open CFSG.Assembly E6ThreeEnd

variable {R R' : Type} [Group R] [Group R']

@[expose] def SLTwoWitness (p : ℕ) (Ab : Subgroup (MulAut R)) (D : Subgroup R) : Prop :=
  ∃ t : R, t ^ p = 1 ∧ (∀ φ ∈ Ab, φ t = t) ∧ MulAut.conj t ∈ Ab ∧ (∃ j ∈ D, t * j ≠ j * t) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ), 2 ≤ n ∧
      Nat.card F = 2 ^ n ∧ ∃ ρ : SL(2, F) →* R, Function.Injective ρ ∧ t ∈ ρ.range ∧
        ρ.range ≤ D ∧ ∀ φ ∈ Ab, ∀ y ∈ ρ.range, φ y ∈ ρ.range

@[expose] def SLTwoAt (p : ℕ) (Ab : Subgroup (MulAut R)) : Prop :=
  ∀ ab ∈ Ab, ab ≠ 1 → ∀ D : Subgroup R, D ≤ ggFix ab →
    (∀ c ∈ ggFix ab, ∀ d ∈ D, c * d * c⁻¹ ∈ D) → CFSG.IsQuasisimple D →
    (∀ φ ∈ Ab, (∀ d ∈ D, φ d = d) → φ ∈ Subgroup.zpowers ab) → SLTwoWitness p Ab D

theorem ggStdSubTwoTorusSLTwoAut_of_forall {p r : ℕ} {I : Set (MulAut R)}
    (h : ∀ Ab : Subgroup (MulAut R), IsElemAbelian p Ab → (∀ φ ∈ Ab, φ ∈ I) →
      p ^ r ≤ Nat.card Ab → SLTwoAt p Ab) :
    GGStdSubTwoTorusSLTwoAut p r R I :=
  h

theorem SLTwoAt.map {p : ℕ} (e : R ≃* R') {Ab : Subgroup (MulAut R)} (h : SLTwoAt p Ab) :
    SLTwoAt p (Ab.map (MulAut.congr e).toMonoidHom) := by
  have hfix : ∀ (a : MulAut R) (x : R), e x ∈ ggFix (MulAut.congr e a) ↔ x ∈ ggFix a :=
    fun a x => by rw [mem_ggFix, mem_ggFix, congr_apply', e.injective.eq_iff]
  rintro _ ⟨ab, hab, rfl⟩ hab1 D' hD' hDn' hDq' hcent'
  set D := D'.comap e.toMonoidHom with hDdef
  have hDD : D.map e.toMonoidHom = D' := Subgroup.map_comap_eq_self_of_surjective e.surjective D'
  obtain ⟨t, htp, htfix, htA, ⟨j, hjD, hj⟩, F, _, _, _, n, hn, hF, ρ, hρ, htρ, hρD, hρinv⟩ :=
    h ab hab (fun h1 => hab1 (by rw [h1, map_one])) D (fun x hx => (hfix ab x).mp (hD' hx))
      (fun c hc d hd => by
        show e (c * d * c⁻¹) ∈ D'
        rw [map_mul, map_mul, map_inv]
        exact hDn' _ ((hfix ab c).mpr hc) _ hd)
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((D.equivMapOfInjective e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr hDD)).symm hDq')
      (fun φ hφ hφD => by
        have h1 := hcent' _ ⟨φ, hφ, rfl⟩ fun d hd => by
          obtain ⟨x, rfl⟩ := e.surjective d
          show MulAut.congr e φ (e x) = e x
          rw [congr_apply', hφD x hd]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
        exact Subgroup.mem_zpowers_iff.mpr
          ⟨k, (MulAut.congr e).injective (by rw [map_zpow]; exact hk)⟩)
  refine ⟨e t, by rw [← map_pow, htp, map_one], ?_, ?_,
    ⟨e j, hjD, fun h' => hj (e.injective (by rw [map_mul, map_mul, h']))⟩, F, inferInstance,
    inferInstance, inferInstance, n, hn, hF, e.toMonoidHom.comp ρ, e.injective.comp hρ, ?_, ?_,
    ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    show MulAut.congr e φ (e t) = e t
    rw [congr_apply', htfix φ hφ]
  · rw [← congr_conj]
    exact ⟨_, htA, rfl⟩
  · obtain ⟨A, rfl⟩ := htρ
    exact ⟨A, rfl⟩
  · rintro _ ⟨A, rfl⟩
    exact hρD ⟨A, rfl⟩
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨A, rfl⟩
    obtain ⟨B, hB⟩ := hρinv φ hφ _ ⟨A, rfl⟩
    refine ⟨B, ?_⟩
    show e (ρ B) = MulAut.congr e φ (e (ρ A))
    rw [hB, congr_apply']

theorem ggStdSubTwoTorusSLTwoAut_of_mulEquiv {p r : ℕ} {I : Set (MulAut R)}
    {I' : Set (MulAut R')} (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGStdSubTwoTorusSLTwoAut p r R' I') : GGStdSubTwoTorusSLTwoAut p r R I := by
  refine ggStdSubTwoTorusSLTwoAut_of_forall fun Ab hAb hAbI hr => ?_
  have hcard : Nat.card (Ab.map (MulAut.congr e).toMonoidHom) = Nat.card Ab :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have h1 : SLTwoAt p (Ab.map (MulAut.congr e).toMonoidHom) :=
    h _ (TableB.isElemAbelian_map hAb _) (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hAbI φ hφ))
      (hcard ▸ hr)
  have h2 := h1.map e.symm
  rwa [map_congr_symm_map_congr] at h2

end CFSG.StandardType.SmallExc

end
