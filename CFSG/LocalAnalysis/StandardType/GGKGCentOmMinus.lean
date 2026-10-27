module

public import CFSG.LieType.Universal.Spin.Twisted.Generation
public import CFSG.LieType.Universal.Spin.Twisted.ShortAction
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Facts
public import CFSG.LargeExtraspecial.A2ModFrBLevi
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.StandardType.KGCentOmMinus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

section ShortLevi

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {b c : F}

omit [Finite F] [CharP F 2] in
private theorem polar_planeVec_eq_polarPlane (v : Vm n F) (p : Fin 2 → F) :
    polar (quadMinus n F b c) v (planeVec n p) =
      polarPlane b c (fun t => v (.inr (.inr t))) p := by
  rw [polar_quadMinus]
  simp [planeVec, polarPlane]

private theorem b_ne_zero_of_irreducible (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  refine hirr s ?_
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  calc s ^ 2 + b * s + c = s ^ 2 + s * s := by rw [hb, hs]; ring
    _ = (2 : F) * s ^ 2 := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem semi_eq_smul_of_commute_eichler_short (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1)
    (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (φ : F ≃+* F) (i : Fin (n - 1))
    (hcomm : ∀ (s : Bool) (p : Fin 2 → F) (v : Vm n F),
      eichler (quadMinus n F b c) (minusVec n i s) (planeVec n p)
          ((A : Matrix _ _ F) *ᵥ (fun k => φ (v k))) =
        (A : Matrix _ _ F) *ᵥ
          (fun k => φ (eichler (quadMinus n F b c) (minusVec n i s) (planeVec n p) v k))) :
    φ = RingEquiv.refl F ∧ ∃ ν : F, ν ≠ 0 ∧ (A : Matrix _ _ F) *ᵥ eVec n i = ν • eVec n i ∧
      (A : Matrix _ _ F) *ᵥ fVec n i = ν • fVec n i ∧
      ∀ p : Fin 2 → F, (A : Matrix _ _ F) *ᵥ planeVec n p = ν • planeVec n p := by
  classical
  have hb : b ≠ 0 := b_ne_zero_of_irreducible hirr
  let p0 : Fin 2 → F := Pi.single 0 1
  let p1 : Fin 2 → F := Pi.single 1 1
  have hp0 : p0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [p0] at this
  have hp1 : p1 ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [p1] at this
  let Qw : (Fin 2 → F) → F := fun p => quadMinus n F b c (planeVec n p)
  let T : Vm n F → Vm n F := fun v => (A : Matrix _ _ F) *ᵥ fun k => φ (v k)
  have hT_add : ∀ u v : Vm n F, T (u + v) = T u + T v := by
    intro u v
    have hv : (fun k => φ ((u + v) k)) = (fun k => φ (u k)) + (fun k => φ (v k)) := by
      funext k
      simp [Pi.add_apply, map_add]
    rw [show T (u + v) = (A : Matrix _ _ F) *ᵥ (fun k => φ ((u + v) k)) from rfl, hv,
      Matrix.mulVec_add]
  have hT_smul : ∀ (a : F) (v : Vm n F), T (a • v) = φ a • T v := by
    intro a v
    have hv : (fun k => φ ((a • v) k)) = φ a • (fun k => φ (v k)) := by
      funext k
      simp [Pi.smul_apply, map_mul]
    rw [show T (a • v) = (A : Matrix _ _ F) *ᵥ (fun k => φ ((a • v) k)) from rfl, hv,
      Matrix.mulVec_smul]
  have hT_inj : Function.Injective T := by
    intro u v huv
    have h1 : (fun k => φ (u k)) = (fun k => φ (v k)) := by
      have h2 := congrArg (fun z => ((↑(A⁻¹) : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) *ᵥ z) huv
      simpa [T, Matrix.mulVec_mulVec] using h2
    funext k
    exact φ.injective (congrFun h1 k)
  set Te : Vm n F := T (eVec n i)
  set Tf : Vm n F := T (fVec n i)
  have hfix_e : ∀ p : Fin 2 → F,
      eichler (quadMinus n F b c) (eVec n i) (planeVec n p) Te = Te := by
    intro p
    have h := hcomm true p (eVec n i)
    rw [minusVec_true] at h
    have hE : eichler (quadMinus n F b c) (eVec n i) (planeVec n p) (eVec n i) = eVec n i := by
      rw [eichler_apply (quadMinus_eVec n b c i) (polar_eVec_planeVec n b c i p)]
      simp [polar_eVec_planeVec, quadMinus_eVec n b c i]
    rw [hE] at h
    simpa [Te] using h
  have hfix_f : ∀ p : Fin 2 → F,
      eichler (quadMinus n F b c) (fVec n i) (planeVec n p) Tf = Tf := by
    intro p
    have h := hcomm false p (fVec n i)
    rw [minusVec_false] at h
    have hE : eichler (quadMinus n F b c) (fVec n i) (planeVec n p) (fVec n i) = fVec n i := by
      rw [eichler_apply (quadMinus_fVec n b c i) (polar_fVec_planeVec n b c i p)]
      simp [polar_fVec_planeVec, quadMinus_fVec n b c i]
    rw [hE] at h
    simpa [Tf] using h
  have hstep1 (p : Fin 2 → F) (hp : p ≠ 0) :
      polar (quadMinus n F b c) Te (eVec n i) = 0 ∧
      polar (quadMinus n F b c) Te (planeVec n p) = 0 := by
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, p k ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (funext h)
    have hE := hfix_e p
    rw [eichler_apply (quadMinus_eVec n b c i) (polar_eVec_planeVec n b c i p)] at hE
    have hzero : polar (quadMinus n F b c) Te (eVec n i) • planeVec n p -
        (polar (quadMinus n F b c) Te (planeVec n p) + Qw p *
          polar (quadMinus n F b c) Te (eVec n i)) • eVec n i = 0 := by
      have h' : Te + (polar (quadMinus n F b c) Te (eVec n i) • planeVec n p -
          (polar (quadMinus n F b c) Te (planeVec n p) + Qw p *
            polar (quadMinus n F b c) Te (eVec n i)) • eVec n i) = Te + 0 := by
        rw [add_zero, ← add_sub_assoc]
        exact hE
      exact add_left_cancel h'
    have hk0 := congrFun hzero (.inr (.inr k))
    have ht : polar (quadMinus n F b c) Te (eVec n i) = 0 := by
      have hk' : polar (quadMinus n F b c) Te (eVec n i) * p k = 0 := by
        simpa [Qw, Pi.sub_apply, Pi.smul_apply, planeVec, eVec] using hk0
      exact (mul_eq_zero.mp hk').resolve_right hk
    have hi0 := congrFun hzero (.inl i)
    have hq : polar (quadMinus n F b c) Te (planeVec n p) = 0 := by
      have ht' : polar (quadMinus n F b c) Te (Pi.single (Sum.inl i) 1) = 0 := by
        simpa [eVec] using ht
      have hi0' : -polar (quadMinus n F b c) Te (planeVec n p) = 0 := by
        simpa [Qw, Pi.sub_apply, Pi.smul_apply, planeVec, eVec, ht'] using hi0
      exact neg_eq_zero.mp hi0'
    exact ⟨ht, hq⟩
  have hstep1f (p : Fin 2 → F) (hp : p ≠ 0) :
      polar (quadMinus n F b c) Tf (fVec n i) = 0 ∧
      polar (quadMinus n F b c) Tf (planeVec n p) = 0 := by
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, p k ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (funext h)
    have hE := hfix_f p
    rw [eichler_apply (quadMinus_fVec n b c i) (polar_fVec_planeVec n b c i p)] at hE
    have hzero : polar (quadMinus n F b c) Tf (fVec n i) • planeVec n p -
        (polar (quadMinus n F b c) Tf (planeVec n p) + Qw p *
          polar (quadMinus n F b c) Tf (fVec n i)) • fVec n i = 0 := by
      have h' : Tf + (polar (quadMinus n F b c) Tf (fVec n i) • planeVec n p -
          (polar (quadMinus n F b c) Tf (planeVec n p) + Qw p *
            polar (quadMinus n F b c) Tf (fVec n i)) • fVec n i) = Tf + 0 := by
        rw [add_zero, ← add_sub_assoc]
        exact hE
      exact add_left_cancel h'
    have hk0 := congrFun hzero (.inr (.inr k))
    have ht : polar (quadMinus n F b c) Tf (fVec n i) = 0 := by
      have hk' : polar (quadMinus n F b c) Tf (fVec n i) * p k = 0 := by
        simpa [Qw, Pi.sub_apply, Pi.smul_apply, planeVec, fVec] using hk0
      exact (mul_eq_zero.mp hk').resolve_right hk
    have hi0 := congrFun hzero (.inr (.inl i))
    have hq : polar (quadMinus n F b c) Tf (planeVec n p) = 0 := by
      have ht' : polar (quadMinus n F b c) Tf (Pi.single (Sum.inr (Sum.inl i)) 1) = 0 := by
        simpa [fVec] using ht
      have hi0' : -polar (quadMinus n F b c) Tf (planeVec n p) = 0 := by
        simpa [Qw, Pi.sub_apply, Pi.smul_apply, planeVec, fVec, ht'] using hi0
      exact neg_eq_zero.mp hi0'
    exact ⟨ht, hq⟩
  have hTe_w : ∀ p : Fin 2 → F, polar (quadMinus n F b c) Te (planeVec n p) = 0 := by
    intro p
    by_cases hp : p = 0
    · rw [hp, planeVec_zero, polar_zero_right]
    · exact (hstep1 p hp).2
  have hTf_w : ∀ p : Fin 2 → F, polar (quadMinus n F b c) Tf (planeVec n p) = 0 := by
    intro p
    by_cases hp : p = 0
    · rw [hp, planeVec_zero, polar_zero_right]
    · exact (hstep1f p hp).2
  have hTe_e : polar (quadMinus n F b c) Te (eVec n i) = 0 := (hstep1 p0 hp0).1
  have hTf_f : polar (quadMinus n F b c) Tf (fVec n i) = 0 := (hstep1f p0 hp0).1
  have hQ0 : Qw p0 = 1 := by
    simp [Qw, p0, quadMinus_planeVec', planeNorm]
  have hQ1 : Qw p1 = c := by
    simp [Qw, p1, quadMinus_planeVec', planeNorm]
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  have hTe_plane0 : Te (.inr (.inr 0)) = 0 := by
    have h := hTe_w p1
    rw [polar_planeVec_eq_polarPlane] at h
    have hform : polarPlane b c (fun t => Te (.inr (.inr t))) p1 =
        b * Te (.inr (.inr 0)) + 2 * c * Te (.inr (.inr 1)) := by
      simp [polarPlane, p1]
    rw [hform] at h
    have hb' : b * Te (.inr (.inr 0)) = 0 := by simpa [h2] using h
    exact (mul_eq_zero.mp hb').resolve_left hb
  have hTe_plane1 : Te (.inr (.inr 1)) = 0 := by
    have h := hTe_w p0
    rw [polar_planeVec_eq_polarPlane] at h
    have hform : polarPlane b c (fun t => Te (.inr (.inr t))) p0 =
        2 * Te (.inr (.inr 0)) + b * Te (.inr (.inr 1)) := by
      simp [polarPlane, p0]
    rw [hform] at h
    have hb' : b * Te (.inr (.inr 1)) = 0 := by simpa [h2] using h
    exact (mul_eq_zero.mp hb').resolve_left hb
  have hTe_plane : ∀ t : Fin 2, Te (.inr (.inr t)) = 0 := by
    intro t
    fin_cases t
    · exact hTe_plane0
    · exact hTe_plane1
  have hTf_plane0 : Tf (.inr (.inr 0)) = 0 := by
    have h := hTf_w p1
    rw [polar_planeVec_eq_polarPlane] at h
    have hform : polarPlane b c (fun t => Tf (.inr (.inr t))) p1 =
        b * Tf (.inr (.inr 0)) + 2 * c * Tf (.inr (.inr 1)) := by
      simp [polarPlane, p1]
    rw [hform] at h
    have hb' : b * Tf (.inr (.inr 0)) = 0 := by simpa [h2] using h
    exact (mul_eq_zero.mp hb').resolve_left hb
  have hTf_plane1 : Tf (.inr (.inr 1)) = 0 := by
    have h := hTf_w p0
    rw [polar_planeVec_eq_polarPlane] at h
    have hform : polarPlane b c (fun t => Tf (.inr (.inr t))) p0 =
        2 * Tf (.inr (.inr 0)) + b * Tf (.inr (.inr 1)) := by
      simp [polarPlane, p0]
    rw [hform] at h
    have hb' : b * Tf (.inr (.inr 1)) = 0 := by simpa [h2] using h
    exact (mul_eq_zero.mp hb').resolve_left hb
  have hTf_plane : ∀ t : Fin 2, Tf (.inr (.inr t)) = 0 := by
    intro t
    fin_cases t
    · exact hTf_plane0
    · exact hTf_plane1
  set α : F := Te (.inl i)
  set α' : F := Tf (.inr (.inl i))
  have hTe_f : polar (quadMinus n F b c) Te (fVec n i) = α := by
    rw [fVec, polar_quadMinus_single_inr_inl]
  have hTf_e : polar (quadMinus n F b c) Tf (eVec n i) = α' := by
    rw [eVec, polar_quadMinus_single_inl]
  have hTf_inl : Tf (.inl i) = 0 := by
    have h := (hstep1f p0 hp0).1
    rwa [fVec, polar_quadMinus_single_inr_inl] at h
  have hTe_inr_inl : Te (.inr (.inl i)) = 0 := by
    have h := hTe_e
    rwa [eVec, polar_quadMinus_single_inl] at h
  set r : Vm n F := Te - α • eVec n i
  set r' : Vm n F := Tf - α' • fVec n i
  have hTe_eq : Te = α • eVec n i + r := by
    change Te = α • eVec n i + (Te - α • eVec n i)
    abel
  have hTf_eq : Tf = α' • fVec n i + r' := by
    change Tf = α' • fVec n i + (Tf - α' • fVec n i)
    abel
  have hr_e : polar (quadMinus n F b c) r (eVec n i) = 0 := by
    change polar (quadMinus n F b c) (Te - α • eVec n i) (eVec n i) = 0
    rw [polar_sub_left, polar_smul_left, hTe_e, polar_eVec_eVec]
    simp
  have hr_f : polar (quadMinus n F b c) r (fVec n i) = 0 := by
    change polar (quadMinus n F b c) (Te - α • eVec n i) (fVec n i) = 0
    rw [polar_sub_left, polar_smul_left, hTe_f, polar_eVec_fVec]
    simp
  have hr_w : ∀ p : Fin 2 → F, polar (quadMinus n F b c) r (planeVec n p) = 0 := by
    intro p
    change polar (quadMinus n F b c) (Te - α • eVec n i) (planeVec n p) = 0
    rw [polar_sub_left, polar_smul_left, hTe_w p, polar_eVec_planeVec]
    simp
  have hr'_e : polar (quadMinus n F b c) r' (eVec n i) = 0 := by
    change polar (quadMinus n F b c) (Tf - α' • fVec n i) (eVec n i) = 0
    rw [polar_sub_left, polar_smul_left, hTf_e, polar_fVec_eVec]
    simp
  have hr'_f : polar (quadMinus n F b c) r' (fVec n i) = 0 := by
    change polar (quadMinus n F b c) (Tf - α' • fVec n i) (fVec n i) = 0
    rw [polar_sub_left, polar_smul_left, hTf_f, polar_fVec_fVec]
    simp
  have hr'_w : ∀ p : Fin 2 → F, polar (quadMinus n F b c) r' (planeVec n p) = 0 := by
    intro p
    change polar (quadMinus n F b c) (Tf - α' • fVec n i) (planeVec n p) = 0
    rw [polar_sub_left, polar_smul_left, hTf_w p, polar_fVec_planeVec]
    simp
  have hr_inl : r (.inl i) = 0 := by
    simp [r, eVec, α]
  have hr_inr_inl : r (.inr (.inl i)) = 0 := by
    simp [r, eVec, hTe_inr_inl]
  have hr_plane : ∀ t : Fin 2, r (.inr (.inr t)) = 0 := by
    intro t
    simp [r, eVec, hTe_plane t]
  have hr'_inl : r' (.inl i) = 0 := by
    simp [r', fVec, hTf_inl]
  have hr'_inr_inl : r' (.inr (.inl i)) = 0 := by
    simp [r', fVec, α']
  have hr'_plane : ∀ t : Fin 2, r' (.inr (.inr t)) = 0 := by
    intro t
    simp [r', fVec, hTf_plane t]
  have hTwA0 : ∀ p : Fin 2 → F,
      T (planeVec n p) = α • planeVec n p +
        (φ (Qw p) * α' - α * Qw p) • fVec n i + φ (Qw p) • r' := by
    intro p
    have he : eichler (quadMinus n F b c) (fVec n i) (planeVec n p) (eVec n i) =
        eVec n i + planeVec n p - Qw p • fVec n i := by
      rw [eichler_apply (quadMinus_fVec n b c i) (polar_fVec_planeVec n b c i p)]
      simp [polar_eVec_fVec, polar_eVec_planeVec, Qw]
    have hTe : eichler (quadMinus n F b c) (fVec n i) (planeVec n p) Te =
        Te + α • planeVec n p - (Qw p * α) • fVec n i := by
      rw [eichler_apply (quadMinus_fVec n b c i) (polar_fVec_planeVec n b c i p)]
      rw [hTe_w p, hTe_f]
      simp [Qw]
    have h := hcomm false p (eVec n i)
    rw [minusVec_false] at h
    change eichler (quadMinus n F b c) (fVec n i) (planeVec n p) Te =
      T (eichler (quadMinus n F b c) (fVec n i) (planeVec n p) (eVec n i)) at h
    rw [hTe] at h
    rw [he] at h
    have hTarg : T (eVec n i + planeVec n p - Qw p • fVec n i) =
        Te + T (planeVec n p) - φ (Qw p) • Tf := by
      rw [sub_eq_add_neg, ← neg_smul, hT_add, hT_add, hT_smul]
      simp only [map_neg, neg_smul]
      simp [Te, Tf]
      abel
    rw [hTarg] at h
    have hc : α • planeVec n p - (Qw p * α) • fVec n i =
        T (planeVec n p) - φ (Qw p) • Tf := by
      have h' : Te + (α • planeVec n p - (Qw p * α) • fVec n i) =
          Te + (T (planeVec n p) - φ (Qw p) • Tf) := by
        rw [← add_sub_assoc, ← add_sub_assoc]
        exact h
      exact add_left_cancel h'
    calc
      T (planeVec n p) = α • planeVec n p - (Qw p * α) • fVec n i +
          φ (Qw p) • Tf := by
        have h' := congrArg (fun z => z + φ (Qw p) • Tf) hc
        rw [sub_add_cancel] at h'
        exact h'.symm
      _ = α • planeVec n p - (Qw p * α) • fVec n i +
          φ (Qw p) • (α' • fVec n i + r') := by rw [hTf_eq]
      _ = α • planeVec n p + (φ (Qw p) * α' - α * Qw p) • fVec n i +
          φ (Qw p) • r' := by
        rw [smul_add, smul_smul, sub_smul, show Qw p * α = α * Qw p by ring]
        abel
  have hTwB0 : ∀ p : Fin 2 → F,
      T (planeVec n p) = α' • planeVec n p +
        (φ (Qw p) * α - α' * Qw p) • eVec n i + φ (Qw p) • r := by
    intro p
    have he : eichler (quadMinus n F b c) (eVec n i) (planeVec n p) (fVec n i) =
        fVec n i + planeVec n p - Qw p • eVec n i := by
      rw [eichler_apply (quadMinus_eVec n b c i) (polar_eVec_planeVec n b c i p)]
      simp [polar_fVec_eVec, polar_fVec_planeVec, Qw]
    have hTfE : eichler (quadMinus n F b c) (eVec n i) (planeVec n p) Tf =
        Tf + α' • planeVec n p - (Qw p * α') • eVec n i := by
      rw [eichler_apply (quadMinus_eVec n b c i) (polar_eVec_planeVec n b c i p)]
      rw [hTf_w p, hTf_e]
      simp [Qw]
    have h := hcomm true p (fVec n i)
    rw [minusVec_true] at h
    change eichler (quadMinus n F b c) (eVec n i) (planeVec n p) Tf =
      T (eichler (quadMinus n F b c) (eVec n i) (planeVec n p) (fVec n i)) at h
    rw [hTfE] at h
    rw [he] at h
    have hTarg : T (fVec n i + planeVec n p - Qw p • eVec n i) =
        Tf + T (planeVec n p) - φ (Qw p) • Te := by
      rw [sub_eq_add_neg, ← neg_smul, hT_add, hT_add, hT_smul]
      simp only [map_neg, neg_smul]
      simp [Te, Tf]
      abel
    rw [hTarg] at h
    have hc : α' • planeVec n p - (Qw p * α') • eVec n i =
        T (planeVec n p) - φ (Qw p) • Te := by
      have h' : Tf + (α' • planeVec n p - (Qw p * α') • eVec n i) =
          Tf + (T (planeVec n p) - φ (Qw p) • Te) := by
        rw [← add_sub_assoc, ← add_sub_assoc]
        exact h
      exact add_left_cancel h'
    calc
      T (planeVec n p) = α' • planeVec n p - (Qw p * α') • eVec n i +
          φ (Qw p) • Te := by
        have h' := congrArg (fun z => z + φ (Qw p) • Te) hc
        rw [sub_add_cancel] at h'
        exact h'.symm
      _ = α' • planeVec n p - (Qw p * α') • eVec n i +
          φ (Qw p) • (α • eVec n i + r) := by rw [hTe_eq]
      _ = α' • planeVec n p + (φ (Qw p) * α - α' * Qw p) • eVec n i +
          φ (Qw p) • r := by
        rw [smul_add, smul_smul, sub_smul, show Qw p * α' = α' * Qw p by ring]
        abel
  have hα_eq : α = α' := by
    have hAB := (hTwA0 p0).symm.trans (hTwB0 p0)
    have hcoord := congrFun hAB (.inr (.inr 0))
    simpa only [p0, fVec, eVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
      Pi.zero_apply, planeVec, hr_plane 0, hr'_plane 0, Sum.inr.injEq, Sum.inr_ne_inl, if_true,
      if_false, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] using hcoord
  have hphiQ0 : φ (Qw p0) ≠ 0 := by
    rw [hQ0, map_one]
    exact one_ne_zero
  have hrr' : r' = r := by
    have hAB := (hTwA0 p0).symm.trans (hTwB0 p0)
    rw [← hα_eq] at hAB
    funext k
    rcases k with j | j | t
    · by_cases hj : j = i
      · subst hj
        rw [hr'_inl, hr_inl]
      · have hk := congrFun hAB (.inl j)
        have hk' : φ (Qw p0) * r' (.inl j) = φ (Qw p0) * r (.inl j) := by
          simpa [p0, fVec, eVec, Pi.single_apply, hj] using hk
        exact mul_left_cancel₀ hphiQ0 hk'
    · by_cases hj : j = i
      · subst hj
        rw [hr'_inr_inl, hr_inr_inl]
      · have hk := congrFun hAB (.inr (.inl j))
        have hk' : φ (Qw p0) * r' (.inr (.inl j)) = φ (Qw p0) * r (.inr (.inl j)) := by
          simpa [p0, fVec, eVec, Pi.single_apply, hj] using hk
        exact mul_left_cancel₀ hphiQ0 hk'
    · rw [hr'_plane t, hr_plane t]
  have hTwA (p : Fin 2 → F) :
      T (planeVec n p) = α • planeVec n p +
        (φ (Qw p) * α - α * Qw p) • fVec n i + φ (Qw p) • r := by
    have := hTwA0 p
    rwa [← hα_eq, hrr'] at this
  have hTwB (p : Fin 2 → F) :
      T (planeVec n p) = α • planeVec n p +
        (φ (Qw p) * α - α * Qw p) • eVec n i + φ (Qw p) • r := by
    have := hTwB0 p
    rwa [← hα_eq] at this
  have hα_ne : α ≠ 0 := by
    intro hα0
    have hw0 : T (planeVec n p0) = r := by
      rw [hTwA p0, hQ0, hα0]
      simp [map_one]
    have hw1 : T (planeVec n p1) = φ c • r := by
      rw [hTwA p1, hQ1, hα0]
      simp
    have h1 : T (c • planeVec n p0) = T (planeVec n p1) := by
      calc T (c • planeVec n p0) = φ c • T (planeVec n p0) := hT_smul c _
        _ = φ c • r := by rw [hw0]
        _ = T (planeVec n p1) := hw1.symm
    have hne : c • planeVec n p0 ≠ planeVec n p1 := by
      intro h
      have h0 : (0 : F) = 1 := by
        have := congrFun h (.inr (.inr 1))
        simp [p0, p1, planeVec] at this
      exact zero_ne_one h0
    exact hne (hT_inj h1)
  have hφ : φ = RingEquiv.refl F := by
    ext a
    have h2 := hT_smul a (planeVec n p0)
    rw [← planeVec_smul] at h2
    rw [hTwA (a • p0), hTwA p0] at h2
    have hcoord := congrFun h2 (.inr (.inr 0))
    have hcoord' : α * a = φ a * α := by
      simpa only [p0, fVec, eVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
        Pi.zero_apply, planeVec, hr_plane 0, Sum.inr.injEq, Sum.inr_ne_inl, if_true, if_false,
        smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] using hcoord
    rw [mul_comm (φ a) α] at hcoord'
    exact (mul_left_cancel₀ hα_ne hcoord').symm
  obtain ⟨c0, hc0, hc1⟩ := hF
  have hcoef : c0 ^ 2 - c0 ≠ 0 := by
    have h : c0 ^ 2 - c0 = c0 * (c0 - 1) := by ring
    rw [h]
    exact mul_ne_zero hc0 (sub_ne_zero.mpr hc1)
  have hQsmul : Qw (c0 • p0) = c0 ^ 2 := by
    have h1 : Qw (c0 • p0) = c0 ^ 2 * Qw p0 := by
      simp [Qw, quadMinus_planeVec', planeNorm_smul]
    rw [h1, hQ0, mul_one]
  have hr_zero : r = 0 := by
    have h2 := hT_smul c0 (planeVec n p0)
    rw [hφ] at h2
    have h2' : T (planeVec n (c0 • p0)) = c0 • T (planeVec n p0) := by
      rw [planeVec_smul]
      simpa using h2
    rw [hTwA (c0 • p0), hTwA p0, hQ0, hQsmul, planeVec_smul, hφ] at h2'
    funext k
    rcases k with j | j | t
    · by_cases hj : j = i
      · subst hj
        exact hr_inl
      · have hk := congrFun h2' (.inl j)
        have hk' : c0 ^ 2 * r (.inl j) = c0 * r (.inl j) := by
          simpa only [p0, fVec, eVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
            Pi.zero_apply, planeVec, hj, Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inl.injEq,
            Sum.inr.injEq, RingEquiv.refl_apply, if_true, if_false, smul_eq_mul, mul_zero,
            zero_mul, add_zero, zero_add, mul_one, one_mul, one_smul] using hk
        have hzero : (c0 ^ 2 - c0) * r (.inl j) = 0 := by
          linear_combination hk'
        have := (mul_eq_zero.mp hzero).resolve_left hcoef
        simpa using this
    · by_cases hj : j = i
      · subst hj
        exact hr_inr_inl
      · have hk := congrFun h2' (.inr (.inl j))
        have hk' : c0 ^ 2 * r (.inr (.inl j)) = c0 * r (.inr (.inl j)) := by
          simpa only [p0, fVec, eVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
            Pi.zero_apply, planeVec, hj, Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inl.injEq,
            Sum.inr.injEq, RingEquiv.refl_apply, if_true, if_false, smul_eq_mul, mul_zero,
            zero_mul, add_zero, zero_add, mul_one, one_mul, one_smul] using hk
        have hzero : (c0 ^ 2 - c0) * r (.inr (.inl j)) = 0 := by
          linear_combination hk'
        have := (mul_eq_zero.mp hzero).resolve_left hcoef
        simpa using this
    · exact hr_plane t
  have hTe_final : Te = α • eVec n i := by
    rw [hTe_eq, hr_zero, add_zero]
  have hTf_final : Tf = α • fVec n i := by
    rw [hTf_eq, hrr', hr_zero, add_zero, ← hα_eq]
  have hTw_final : ∀ p : Fin 2 → F, T (planeVec n p) = α • planeVec n p := by
    intro p
    rw [hTwA p, hr_zero, smul_zero, add_zero, hφ]
    simp only [RingEquiv.refl_apply]
    rw [show Qw p * α - α * Qw p = 0 by ring, zero_smul, add_zero]
  have hA_e : (A : Matrix _ _ F) *ᵥ eVec n i = α • eVec n i := by
    rw [← hTe_final]
    simp [Te, T, hφ]
  have hA_f : (A : Matrix _ _ F) *ᵥ fVec n i = α • fVec n i := by
    rw [← hTf_final]
    simp [Tf, T, hφ]
  have hA_w : ∀ p : Fin 2 → F,
      (A : Matrix _ _ F) *ᵥ planeVec n p = α • planeVec n p := by
    intro p
    rw [← hTw_final p]
    simp [T, hφ]
  exact ⟨hφ, α, hα_ne, hA_e, hA_f, hA_w⟩

end ShortLevi

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {b c : F}

omit [Finite F] [CharP F 2] in
private theorem eq_diagonal_of_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : Matrix ι ι F} {d : ι → F}
    (h : ∀ q, g *ᵥ Pi.single q 1 = d q • Pi.single q 1) :
    g = Matrix.diagonal d := by
  refine Matrix.ext_of_mulVec_single fun q => ?_
  rw [h q, Matrix.diagonal_mulVec_single, mul_one]
  simpa using (Pi.single_smul' q (d q) (1 : F)).symm

omit [Finite F] [CharP F 2] in
private theorem eq_smul_single_of_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → F} {μ : F} {x : ι → F} {q₀ : ι}
    (hx : Matrix.diagonal d *ᵥ x = μ • x) (h : ∀ q, q ≠ q₀ → d q ≠ μ) :
    x = x q₀ • Pi.single q₀ 1 := by
  have hcoord : ∀ q, d q * x q = μ * x q := by
    intro q
    have h := congrFun hx q
    rwa [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
  funext q
  by_cases hq : q = q₀
  · subst hq
    simp
  · have hxq : x q = 0 := by
      have h1 := hcoord q
      have h2 : (d q - μ) * x q = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (h q hq))
    rw [hxq]
    simp [hq]

omit [Finite F] [CharP F 2] in
private theorem pow_mulVec_eq_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι F} {v : ι → F} {a : F} (h : M *ᵥ v = a • v) (m : ℕ) :
    (M ^ m) *ᵥ v = a ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']

private theorem planeVec_single {K : Type*} [Field K] (n : ℕ) (t : Fin 2) :
    planeVec n (Pi.single t (1 : K)) = Pi.single (.inr (.inr t)) 1 := by
  funext q
  rcases q with j | j | s <;> simp [planeVec, Pi.single_apply]

private def torusDiag {K : Type*} [Field K] (n : ℕ) (k : Fin (n - 1)) (ζ : K) :
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → K
  | .inl j => if j = k then ζ else 1
  | .inr (.inl j) => if j = k then ζ⁻¹ else 1
  | .inr (.inr _) => 1

omit [Finite F] [CharP F 2] in
private theorem eq_diagonal_of_torus_action {n : ℕ}
    (k : Fin (n - 1)) {ζ : F}
    {g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (he : g *ᵥ eVec n k = ζ • eVec n k)
    (hf : g *ᵥ fVec n k = ζ⁻¹ • fVec n k)
    (ho : ∀ j, j ≠ k → g *ᵥ eVec n j = eVec n j ∧ g *ᵥ fVec n j = fVec n j)
    (hp : ∀ p : Fin 2 → F, g *ᵥ planeVec n p = planeVec n p) :
    g = Matrix.diagonal (n := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (torusDiag n k ζ) := by
  refine eq_diagonal_of_mulVec_single (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (d := torusDiag n k ζ) fun q => ?_
  rcases q with j | j | t
  · by_cases hjk : j = k
    · subst hjk
      simpa [eVec, torusDiag] using he
    · simpa [eVec, torusDiag, hjk] using (ho j hjk).1
  · by_cases hjk : j = k
    · subst hjk
      simpa [fVec, torusDiag] using hf
    · simpa [fVec, torusDiag, hjk] using (ho j hjk).2
  · simpa [torusDiag, planeVec_single (K := F) n t] using hp (Pi.single t 1)

private theorem pow_two_pow_injective {K : Type*} [Field K] [CharP K 2] (m : ℕ) :
    Function.Injective fun x : K => x ^ 2 ^ m := by
  induction m with
  | zero => intro x y h; simpa using h
  | succ m ih =>
      intro x y h
      apply ih
      have h' : (x ^ 2 ^ m) ^ 2 = (y ^ 2 ^ m) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
        simpa [Nat.pow_succ] using h
      exact CharTwo.sq_injective h'

private abbrev OmMatrix (n : ℕ) (F : Type) : Type :=
  Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F

omit [Finite F] in
theorem eq_smul_of_commute_torus
    (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (ν : F)
    (hAp : ∀ p : Fin 2 → F, (A : Matrix _ _ F) *ᵥ planeVec n p = ν • planeVec n p)
    (htor : ∀ k : Fin (n - 1), ∃ ζ : F, ζ ≠ 0 ∧ ζ ^ 2 ≠ 1 ∧
      ∃ g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F, (A : Matrix _ _ F) * g = g * (A : Matrix _ _ F) ∧
        g *ᵥ eVec n k = ζ • eVec n k ∧ g *ᵥ fVec n k = ζ⁻¹ • fVec n k ∧
        (∀ j, j ≠ k → g *ᵥ eVec n j = eVec n j ∧ g *ᵥ fVec n j = fVec n j) ∧
        ∀ p : Fin 2 → F, g *ᵥ planeVec n p = planeVec n p)
    (m : ℕ)
    (hpow : ∀ (k : Fin (n - 1)) (p : Fin 2 → F) (v : Vm n F),
      eichler (quadMinus n F b c) (eVec n k) (planeVec n p) (((A : Matrix _ _ F) ^ (2 ^ m)) *ᵥ v) =
        ((A : Matrix _ _ F) ^ (2 ^ m)) *ᵥ eichler (quadMinus n F b c) (eVec n k) (planeVec n p) v) :
    (A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
      ν • 1 := by
  have hfinal : ∀ k : Fin (n - 1),
      (A : OmMatrix n F) *ᵥ eVec n k = ν • eVec n k ∧
      (A : OmMatrix n F) *ᵥ fVec n k = ν • fVec n k := by
    intro k
    obtain ⟨ζ, hζ0, hζ, g, hcomm, hge, hgf, hoth, hgp⟩ := htor k
    have hζ1 : ζ ≠ 1 := fun h => hζ (by rw [h]; norm_num)
    have hζinv1 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
    have hζinvζ : ζ⁻¹ ≠ ζ := by
      intro h
      apply hζ
      calc ζ ^ 2 = ζ * ζ⁻¹ := by rw [pow_two, h]
        _ = 1 := mul_inv_cancel₀ hζ0
    have hd : g = Matrix.diagonal (n := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (torusDiag n k ζ) :=
      eq_diagonal_of_torus_action k hge hgf hoth hgp
    have hgx : g *ᵥ ((A : OmMatrix n F) *ᵥ eVec n k) =
        ζ • ((A : OmMatrix n F) *ᵥ eVec n k) := by
      rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hge, Matrix.mulVec_smul]
    rw [hd] at hgx
    have hxe : (A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ eVec n k =
        ((A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ eVec n k) (.inl k) • eVec n k := by
      refine (eq_smul_single_of_diagonal (d := torusDiag n k ζ) (μ := ζ)
        (q₀ := (Sum.inl k : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) hgx ?_)
      intro q hq
      rcases q with j | j | t
      · by_cases hjk : j = k
        · subst hjk
          exact absurd rfl hq
        · simpa [torusDiag, hjk] using hζ1.symm
      · by_cases hjk : j = k
        · subst hjk
          simpa [torusDiag] using hζinvζ
        · simpa [torusDiag, hjk] using hζ1.symm
      · simpa [torusDiag] using hζ1.symm
    have hgy : g *ᵥ ((A : OmMatrix n F) *ᵥ fVec n k) =
        ζ⁻¹ • ((A : OmMatrix n F) *ᵥ fVec n k) := by
      rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hgf, Matrix.mulVec_smul]
    rw [hd] at hgy
    have hxf : (A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ fVec n k =
        ((A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ fVec n k) (.inr (.inl k)) • fVec n k := by
      refine (eq_smul_single_of_diagonal (d := torusDiag n k ζ) (μ := ζ⁻¹)
        (q₀ := (Sum.inr (Sum.inl k) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) hgy ?_)
      intro q hq
      rcases q with j | j | t
      · by_cases hjk : j = k
        · subst hjk
          simpa [torusDiag] using hζinvζ.symm
        · simpa [torusDiag, hjk] using hζinv1.symm
      · by_cases hjk : j = k
        · subst hjk
          exact absurd rfl hq
        · simpa [torusDiag, hjk] using hζinv1.symm
      · simpa [torusDiag] using hζinv1.symm
    let a : F := ((A : OmMatrix n F) *ᵥ eVec n k) (.inl k)
    let a' : F := ((A : OmMatrix n F) *ᵥ fVec n k) (.inr (.inl k))
    have hxe' : (A : OmMatrix n F) *ᵥ eVec n k = a • eVec n k := hxe
    have hxf' : (A : OmMatrix n F) *ᵥ fVec n k = a' • fVec n k := hxf
    have hpow_e : ((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ eVec n k = a ^ (2 ^ m) • eVec n k :=
      pow_mulVec_eq_smul hxe' (2 ^ m)
    have hpow_f : ((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ fVec n k = a' ^ (2 ^ m) • fVec n k :=
      pow_mulVec_eq_smul hxf' (2 ^ m)
    have hpow_w : ((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ planeVec n (Pi.single 0 1) =
        ν ^ (2 ^ m) • planeVec n (Pi.single 0 1) :=
      pow_mulVec_eq_smul (hAp (Pi.single 0 1)) (2 ^ m)
    let E : Vm n F ≃ₗ[F] Vm n F :=
      eichler (quadMinus n F b c) (eVec n k) (planeVec n (Pi.single 0 1))
    have hQe : quadMinus n F b c (eVec n k) = 0 := quadMinus_eVec n b c k
    have hBew : polar (quadMinus n F b c) (eVec n k) (planeVec n (Pi.single 0 1)) = 0 :=
      polar_eVec_planeVec n b c k (Pi.single 0 1)
    have hBfw : polar (quadMinus n F b c) (fVec n k) (planeVec n (Pi.single 0 1)) = 0 :=
      polar_fVec_planeVec n b c k (Pi.single 0 1)
    have hQw : quadMinus n F b c (planeVec n (Pi.single 0 1)) = 1 := by
      rw [quadMinus_planeVec']
      simp [planeNorm]
    have hBef : polar (quadMinus n F b c) (fVec n k) (eVec n k) = 1 := by
      rw [polar_fVec_eVec]
      simp
    have hE : E (fVec n k) = fVec n k + planeVec n (Pi.single 0 1) - eVec n k := by
      show eichler (quadMinus n F b c) (eVec n k) (planeVec n (Pi.single 0 1)) (fVec n k) = _
      rw [eichler_apply hQe hBew, hBef, hBfw, hQw]
      simp
    have hmain : E (((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ fVec n k) =
        ((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ E (fVec n k) :=
      hpow k (Pi.single 0 1) (fVec n k)
    have hEq : a' ^ (2 ^ m) • ((fVec n k + planeVec n (Pi.single 0 1) - eVec n k : Vm n F)) =
        ((a' ^ (2 ^ m) • fVec n k + ν ^ (2 ^ m) • planeVec n (Pi.single 0 1) -
          a ^ (2 ^ m) • eVec n k : Vm n F)) := by
      calc
        a' ^ (2 ^ m) • (fVec n k + planeVec n (Pi.single 0 1) - eVec n k)
            = a' ^ (2 ^ m) • E (fVec n k) := by rw [hE]
        _ = E (a' ^ (2 ^ m) • fVec n k) := (E.map_smul _ _).symm
        _ = E (((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ fVec n k) := by rw [hpow_f]
        _ = ((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ E (fVec n k) := hmain
        _ = ((A : OmMatrix n F) ^ (2 ^ m)) *ᵥ
              (fVec n k + planeVec n (Pi.single 0 1) - eVec n k) := by rw [hE]
        _ = a' ^ (2 ^ m) • fVec n k + ν ^ (2 ^ m) • planeVec n (Pi.single 0 1) -
              a ^ (2 ^ m) • eVec n k := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_add, hpow_f, hpow_e, hpow_w]
    have hν_eq : a' ^ (2 ^ m) = ν ^ (2 ^ m) := by
      have h := congrFun hEq (.inr (.inr (0 : Fin 2)))
      simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eVec, fVec, planeVec,
        Pi.single_apply] using h
    have ha_eq : a' ^ (2 ^ m) = a ^ (2 ^ m) := by
      have h := congrFun hEq (.inl k)
      have h' : -(a' ^ (2 ^ m)) = -(a ^ (2 ^ m)) := by
        simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eVec, fVec, planeVec,
          Pi.single_apply] using h
      exact neg_inj.mp h'
    have haν : a = ν := pow_two_pow_injective (K := F) m (ha_eq.symm.trans hν_eq)
    have ha'ν : a' = ν := pow_two_pow_injective (K := F) m hν_eq
    refine ⟨?_, ?_⟩
    · rw [hxe]
      change a • eVec n k = ν • eVec n k
      rw [haν]
    · rw [hxf]
      change a' • fVec n k = ν • fVec n k
      rw [ha'ν]
  rw [Matrix.smul_one_eq_diagonal (a := ν)]
  refine Matrix.ext_of_mulVec_single fun q => ?_
  rw [Matrix.diagonal_const_mulVec]
  rcases q with k | k | t
  · simpa [eVec] using (hfinal k).1
  · simpa [fVec] using (hfinal k).2
  · simpa [planeVec_single (K := F) n t] using hAp (Pi.single t 1)

end Torus

section Core

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {b c : F}

omit [Finite F] [CharP F 2] in
private theorem map_mulVec_comp (φ : F ≃+* F) (M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (v : Vm n F) :
    (M.map φ) *ᵥ (fun k => φ (v k)) = fun k => φ ((M *ᵥ v) k) := by
  funext k
  exact (RingHom.map_mulVec φ.toRingHom M v k).symm

omit [Finite F] [CharP F 2] in
private theorem coe_glFieldEquiv_map (φ : F ≃+* F)
    (M : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
    (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv _ φ M).val =
      M.val.map φ := by
  ext a b
  rfl

theorem mem_centralizer_of_shortLevi_of_torus (hn : 4 ≤ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1) {f : ℕ}
    (hf : 1 ≤ f) (hcard : Nat.card F = 2 ^ f)
    (ψ : spinGroup (quadMinus n F b c) →* G) (hψ : Function.Injective ψ)
    (Bs : Subgroup G) {t : G} (m : ℕ) (ht2 : t ^ (2 ^ m) = 1)
    (htB : ∀ x ∈ Bs, t * x = x * t)
    (htN : t ∈ Subgroup.normalizer (ψ.range : Set G)) (i : Fin (n - 1))
    (hshort : ∀ (s : Bool) (P : Fin 2 → F),
      t * ψ (twShortRoot n hirr i s (.ofAdd P)) * t⁻¹ = ψ (twShortRoot n hirr i s (.ofAdd P)))
    (htor : ∀ k : Fin (n - 1), ∃ x ∈ Bs, ∃ h : spinGroup (quadMinus n F b c), ∃ ζ : F,
      ζ ^ 2 ≠ 1 ∧ (∀ u, x⁻¹ * ψ u * x = ψ (h * u * h⁻¹)) ∧
      spinAction _ h (eVec n k) = ζ • eVec n k ∧ spinAction _ h (fVec n k) = ζ⁻¹ • fVec n k ∧
      (∀ j, j ≠ k → spinAction _ h (eVec n j) = eVec n j ∧
        spinAction _ h (fVec n j) = fVec n j) ∧
      ∀ P, spinAction _ h (planeVec n P) = planeVec n P) :
    t ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen := CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr
  have hinjS : Function.Injective (spinAction (quadMinus n F b c)) :=
    CFSG.LargeExtraspecial.A2Mod.FrB.spinAction_injective n hirr (CharP.cast_eq_zero F 2)
  have hinjM : Function.Injective (spinMatrix (quadMinus n F b c)) := by
    intro x y hxy
    apply hinjS
    apply LinearEquiv.ext
    intro v
    rw [← spinMatrix_mulVec, ← spinMatrix_mulVec, hxy]
  obtain ⟨β, hβ⟩ := CFSG.StandardType.ggF4_exists_pullAut hψ htN
  obtain ⟨A, φ, μ, -, hA⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.spinMinus_aut_similarity (p := 2) hn hf hcard
      hirr β
  have hβs : ∀ (s : Bool) (P : Fin 2 → F),
      β (twShortRoot n hirr i s (.ofAdd P)) = twShortRoot n hirr i s (.ofAdd P) := fun s P =>
    hψ (by rw [hβ, hshort])
  have hcomm : ∀ (s : Bool) (P : Fin 2 → F) (v : Vm n F),
      eichler (quadMinus n F b c) (minusVec n i s) (planeVec n P)
          ((A : Matrix _ _ F) *ᵥ (fun k => φ (v k))) =
        (A : Matrix _ _ F) *ᵥ
          (fun k => φ (eichler (quadMinus n F b c) (minusVec n i s) (planeVec n P) v k)) := by
    intro s P v
    have h1 := hA (twShortRoot n hirr i s (.ofAdd P))
    rw [hβs] at h1
    have h2 : (spinMatrix (quadMinus n F b c) (twShortRoot n hirr i s (.ofAdd P))).val *
        A.val = A.val *
          ((spinMatrix (quadMinus n F b c) (twShortRoot n hirr i s (.ofAdd P))).val.map φ) := by
      have := congrArg (fun X => (X * A).val) h1
      simpa [mul_assoc, coe_glFieldEquiv_map] using this
    have h3 := congrArg (fun X => X *ᵥ (fun k => φ (v k))) h2
    simp only [← Matrix.mulVec_mulVec] at h3
    rw [map_mulVec_comp, spinMatrix_mulVec, spinMatrix_mulVec,
      spinAction_twShortRoot_eq_eichler] at h3
    exact h3
  obtain ⟨rfl, ν, -, -, -, hAp⟩ := semi_eq_smul_of_commute_eichler_short hirr hF A φ i hcomm
  have hA1 : ∀ x, spinMatrix (quadMinus n F b c) (β x) =
      A * spinMatrix (quadMinus n F b c) x * A⁻¹ := by
    intro x
    have h := hA x
    have hid : CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv _
        (RingEquiv.refl F) (spinMatrix (quadMinus n F b c) x) = spinMatrix (quadMinus n F b c) x :=
      Units.ext (by rw [coe_glFieldEquiv_map]; ext a b; rfl)
    rwa [hid] at h
  have hβfix : ∀ x ∈ Bs, ∀ h : spinGroup (quadMinus n F b c),
      (∀ u, x⁻¹ * ψ u * x = ψ (h * u * h⁻¹)) → β h = h := by
    intro x hx h hh
    have key : ∀ u, β (h * u * h⁻¹) = h * β u * h⁻¹ := by
      intro u
      apply hψ
      rw [hβ, ← hh u, ← hh (β u), hβ]
      have htx : t * x⁻¹ = x⁻¹ * t := by
        have h1 := htB x hx
        calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
          _ = x⁻¹ * (t * x) * x⁻¹ := by rw [h1]
          _ = x⁻¹ * t := by group
      have htx' : x * t⁻¹ = t⁻¹ * x := by
        have h1 := htB x hx
        calc x * t⁻¹ = t⁻¹ * (t * x) * t⁻¹ := by group
          _ = t⁻¹ * (x * t) * t⁻¹ := by rw [h1]
          _ = t⁻¹ * x := by group
      calc t * (x⁻¹ * ψ u * x) * t⁻¹ = (t * x⁻¹) * ψ u * (x * t⁻¹) := by group
        _ = (x⁻¹ * t) * ψ u * (t⁻¹ * x) := by rw [htx, htx']
        _ = x⁻¹ * (t * ψ u * t⁻¹) * x := by group
    have hc : h⁻¹ * β h ∈ Subgroup.center (spinGroup (quadMinus n F b c)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := β.surjective g
      have h1 := key u
      rw [map_mul, map_mul, map_inv] at h1
      calc β u * (h⁻¹ * β h) = h⁻¹ * (h * β u * h⁻¹) * β h := by group
        _ = h⁻¹ * (β h * β u * (β h)⁻¹) * β h := by rw [← h1]
        _ = h⁻¹ * β h * β u := by group
    rw [hcen, Subgroup.mem_bot] at hc
    calc β h = h * (h⁻¹ * β h) := by group
      _ = h := by rw [hc, mul_one]
  have hAcomm : ∀ x ∈ Bs, ∀ h : spinGroup (quadMinus n F b c),
      (∀ u, x⁻¹ * ψ u * x = ψ (h * u * h⁻¹)) →
        A * spinMatrix (quadMinus n F b c) h = spinMatrix (quadMinus n F b c) h * A := by
    intro x hx h hh
    have h1 := hA1 h
    rw [hβfix x hx h hh] at h1
    calc A * spinMatrix (quadMinus n F b c) h
        = (A * spinMatrix (quadMinus n F b c) h * A⁻¹) * A := by group
      _ = spinMatrix (quadMinus n F b c) h * A := by rw [← h1]
  have hβpow : ∀ (N : ℕ) (u : spinGroup (quadMinus n F b c)),
      ψ ((β ^ N) u) = t ^ N * ψ u * t⁻¹ ^ N := by
    intro N
    induction N with
    | zero => intro u; simp
    | succ N ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, hβ, ih]
      group
  have hβ1 : ∀ u, (β ^ (2 ^ m)) u = u := fun u => hψ (by rw [hβpow, inv_pow, ht2, inv_one]; group)
  have hApow : ∀ (N : ℕ) (x : spinGroup (quadMinus n F b c)),
      spinMatrix (quadMinus n F b c) ((β ^ N) x) =
        A ^ N * spinMatrix (quadMinus n F b c) x * A⁻¹ ^ N := by
    intro N
    induction N with
    | zero => intro x; simp
    | succ N ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hA1, ih]
      group
  have hpow : ∀ (k : Fin (n - 1)) (P : Fin 2 → F) (v : Vm n F),
      eichler (quadMinus n F b c) (eVec n k) (planeVec n P) ((A.val ^ (2 ^ m)) *ᵥ v) =
        (A.val ^ (2 ^ m)) *ᵥ eichler (quadMinus n F b c) (eVec n k) (planeVec n P) v := by
    intro k P v
    have h1 := hApow (2 ^ m) (twShortRoot n hirr k true (.ofAdd P))
    rw [hβ1] at h1
    have h2 : (A ^ (2 ^ m)).val *
          (spinMatrix (quadMinus n F b c) (twShortRoot n hirr k true (.ofAdd P))).val =
        (spinMatrix (quadMinus n F b c) (twShortRoot n hirr k true (.ofAdd P))).val *
          (A ^ (2 ^ m)).val := by
      have h3 : A ^ (2 ^ m) *
            spinMatrix (quadMinus n F b c) (twShortRoot n hirr k true (.ofAdd P)) =
          spinMatrix (quadMinus n F b c) (twShortRoot n hirr k true (.ofAdd P)) *
            A ^ (2 ^ m) := by
        calc A ^ (2 ^ m) * spinMatrix (quadMinus n F b c) (twShortRoot n hirr k true (.ofAdd P))
            = (A ^ (2 ^ m) *
                spinMatrix (quadMinus n F b c) (twShortRoot n hirr k true (.ofAdd P)) *
                A⁻¹ ^ (2 ^ m)) * A ^ (2 ^ m) := by group
          _ = _ := by rw [← h1]
      exact congrArg Units.val h3
    have h4 := congrArg (fun X => X *ᵥ v) h2
    simp only [← Matrix.mulVec_mulVec, Units.val_pow_eq_pow_val] at h4
    rw [spinMatrix_mulVec, spinMatrix_mulVec, spinAction_twShortRoot_eq_eichler,
      minusVec_true] at h4
    exact h4.symm
  have htor' : ∀ k : Fin (n - 1), ∃ ζ : F, ζ ≠ 0 ∧ ζ ^ 2 ≠ 1 ∧
      ∃ g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      A.val * g = g * A.val ∧
      g *ᵥ eVec n k = ζ • eVec n k ∧ g *ᵥ fVec n k = ζ⁻¹ • fVec n k ∧
      (∀ j, j ≠ k → g *ᵥ eVec n j = eVec n j ∧ g *ᵥ fVec n j = fVec n j) ∧
      ∀ P : Fin 2 → F, g *ᵥ planeVec n P = planeVec n P := by
    intro k
    obtain ⟨x, hx, h, ζ, hζ, hh, he, hf, hj, hP⟩ := htor k
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at he
      have h0 := congrFun (((spinAction (quadMinus n F b c)) h).map_eq_zero_iff.mp he) (.inl k)
      simp [eVec] at h0
    refine ⟨ζ, hζ0, hζ, (spinMatrix (quadMinus n F b c) h).val,
      congrArg Units.val (hAcomm x hx h hh), ?_, ?_, ?_, ?_⟩
    · rw [spinMatrix_mulVec, he]
    · rw [spinMatrix_mulVec, hf]
    · intro j hjk
      rw [spinMatrix_mulVec, spinMatrix_mulVec]
      exact hj j hjk
    · intro P
      rw [spinMatrix_mulVec, hP]
  have hAν := eq_smul_of_commute_torus A ν hAp htor' m hpow
  have hβid : ∀ x, β x = x := by
    intro x
    apply hinjM
    have hcommA : A * spinMatrix (quadMinus n F b c) x = spinMatrix (quadMinus n F b c) x * A := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hAν, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    rw [hA1, hcommA, mul_inv_cancel_right]
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h1 := hβ u
  rw [hβid] at h1
  calc ψ u * t = t * ψ u * t⁻¹ * t := by rw [← h1]
    _ = t * ψ u := by group

end Core

end CFSG.StandardType.KGCentOmMinus

end
