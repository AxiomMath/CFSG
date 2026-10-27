module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv15
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped Matrix MatrixGroups

theorem w4t_sl2_two_mul_le {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* SL(2, GaloisField 2 n)) {d : ℕ}
    (f : X →* GL (Fin d) (ZMod 2)) (hf : f ≠ 1) : 2 * n ≤ d := by
  classical
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hGF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hGF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup SL(2, GaloisField 2 n) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.sl2_isSimpleGroup CharTwo.two_eq_zero
      (by rwa [Fintype.card_eq_nat_card])
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (GaloisField 2 n) h4
  have : IsSimpleGroup X := e.isSimpleGroup
  have hper : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let σ : GL (Fin d) (ZMod 2) ≃* ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  have hρ : ∃ g, (σ.toMonoidHom.comp f) g ≠ 1 := by
    by_contra h
    push Not at h
    refine hf (MonoidHom.ext fun g => ?_)
    have h1 : σ (f g) = σ 1 := (h g).trans (map_one σ).symm
    exact σ.injective h1
  let _ : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  have h := Background.Harris.CaseClassificationAndDescent.TwoComp.two_mul_le_finrank_of_ne_one
    (M := Fin d → ZMod 2) hn hper e (σ.toMonoidHom.comp f) hρ
  rwa [Module.finrank_fin_fun] at h

theorem w4t_sl2_exists_rep {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* SL(2, GaloisField 2 n)) :
    ∃ f : X →* GL (Fin (2 * n)) (ZMod 2), f ≠ 1 := by
  classical
  have hfr : Module.finrank (ZMod 2) (Fin 2 → GaloisField 2 n) = 2 * n := by
    rw [Module.finrank_pi_fintype, GaloisField.finrank 2 (by omega), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Fin 2 → GaloisField 2 n) hfr
  let r : SL(2, GaloisField 2 n) →*
      ((Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 n)) :=
    { toFun := fun g => (Matrix.SpecialLinearGroup.toLin' g).restrictScalars (ZMod 2)
      map_one' := by
        ext v
        simp
      map_mul' := fun g g' => by
        ext v
        simp }
  let σ : ((Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 n)) ≃*
      GL (Fin (2 * n)) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
        Matrix.GeneralLinearGroup.toLin.symm)
  refine ⟨σ.toMonoidHom.comp (r.comp e.toMonoidHom), fun h => ?_⟩
  have hnt : Nontrivial SL(2, GaloisField 2 n) := by
    refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, 1, fun h1 => ?_⟩⟩
    have := congrArg
      (fun A : SL(2, GaloisField 2 n) => (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 1) h1
    simp at this
  obtain ⟨g, hg⟩ := exists_ne (1 : SL(2, GaloisField 2 n))
  have h1 : σ (r g) = σ 1 := by
    have := congrArg (fun φ : X →* GL (Fin (2 * n)) (ZMod 2) => φ (e.symm g)) h
    simpa using this
  have h2 : r g = 1 := σ.injective h1
  refine hg (Matrix.SpecialLinearGroup.toLin'_injective (LinearEquiv.ext fun v => ?_))
  have := congrArg (fun φ : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 n) => φ v)
    h2
  simpa [r] using this

theorem dMinDeg_eq_of_mulEquiv_sl2 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* SL(2, GaloisField 2 n)) : dMinDeg X = 2 * n := by
  obtain ⟨f, hf⟩ := w4t_sl2_exists_rep (by omega) e
  have hmem : 2 * n ∈ {d : ℕ | ∃ f : X →* GL (Fin d) (ZMod 2), f ≠ 1} := ⟨f, hf⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro d ⟨g, hg⟩
  exact w4t_sl2_two_mul_le hn e g hg

end CFSG.LocalAnalysis.WeakClosure81
