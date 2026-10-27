module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtSL

public section

namespace CFSG.Quasithin.H13.Lem1227Lt

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

namespace SL

theorem units_zmod_two_eq_one : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by
  decide

theorem ringEquiv_zmod_two_eq_one (σ : ZMod 2 ≃+* ZMod 2) : σ = 1 := by
  ext x
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) x with rfl | rfl
  · simp
  · simp

theorem inner_of_stabilizer {n d : ℕ} (hn : 3 ≤ n) (hd1 : 1 ≤ d) (hdn : d < n) (hd : n ≠ 2 * d)
    (α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)))
    (hα : (stabilizer (flagSpace n (ZMod 2) d)).map (α : _ →* _) =
      stabilizer (flagSpace n (ZMod 2) d)) :
    ∃ A : SpecialLinearGroup (Fin n) (ZMod 2), ∀ x, α x = A * x * A⁻¹ := by
  classical
  have hK : Nat.card (ZMod 2) = 2 := card_zmod_two
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinjp : Function.Injective (proj n (ZMod 2)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_bot_of_card_two hK n]
  let e : SpecialLinearGroup (Fin n) (ZMod 2) ≃* projectiveSL n (ZMod 2) :=
    MulEquiv.ofBijective (proj n (ZMod 2)) ⟨hinjp, proj_surjective n (ZMod 2)⟩
  have he : ∀ x, e x = proj n (ZMod 2) x := fun x => rfl
  let α' : MulAut (projectiveSL n (ZMod 2)) := e.symm.trans (α.trans e)
  have hα' : ∀ x, α' (proj n (ZMod 2) x) = proj n (ZMod 2) (α x) := by
    intro x
    show e (α (e.symm (proj n (ZMod 2) x))) = _
    rw [← he x, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨-, hgen⟩ := automorphism_generation (K := ZMod 2) (n := n) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α'
  rw [ringEquiv_zmod_two_eq_one σ, map_one, mul_one] at hαeq
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hαeq
    have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact units_zmod_two_eq_one _
    let g : SpecialLinearGroup (Fin n) (ZMod 2) := ⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩
    have hg : SpecialLinearGroup.toGL g = A := Units.ext rfl
    refine ⟨g, fun x => ?_⟩
    apply e.injective
    have h1 : e (α x) = α' (e x) := (hα' x).symm
    rw [h1, hαeq, ← hg, conjAut_toGL, he x]
    simp only [MulAut.conj_apply, map_mul, map_inv, he]
  ·
    exfalso
    rw [pow_one] at hαeq
    have hP : (projStabilizer (flagSpace n (ZMod 2) d)).map (α' : _ →* _) =
        projStabilizer (flagSpace n (ZMod 2) d) := by
      rw [projStabilizer, Subgroup.map_map]
      have : (α' : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)).comp
          (proj n (ZMod 2)) = (proj n (ZMod 2)).comp (α : _ →* _) := by
        ext x
        exact hα' x
      rw [this, ← Subgroup.map_map, hα]
    have hmap : (projStabilizer (flagSpace n (ZMod 2) d)).map (α' : _ →* _) =
        projStabilizer ((dotOrth (flagSpace n (ZMod 2) d)).map
          (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))) := by
      obtain ⟨-, -, -, -, -, -, hconj, -, hdual, -⟩ :=
        standard_automorphism_transport (K := ZMod 2) (n := n)
      rw [hαeq]
      have : ((conjAut n (ZMod 2) A * dualAut n (ZMod 2) : MulAut (projectiveSL n (ZMod 2))) :
          projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)) =
          (conjAut n (ZMod 2) A : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)).comp
            (dualAut n (ZMod 2) : projectiveSL n (ZMod 2) →* projectiveSL n (ZMod 2)) := rfl
      rw [this, ← Subgroup.map_map, hdual, hconj]
    rw [hmap] at hP
    have hfd : finrank (ZMod 2) (flagSpace n (ZMod 2) d) = d := finrank_flagSpace hdn.le
    have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2))) := by
      have hu : IsUnit (A : Matrix (Fin n) (Fin n) (ZMod 2)) := A.isUnit
      exact Matrix.mulVec_injective_iff_isUnit.2 hu
    have hW1 : finrank (ZMod 2) ((dotOrth (flagSpace n (ZMod 2) d)).map
        (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))) = n - d := by
      rw [(Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm, finrank_dotOrth, hfd]
    obtain ⟨-, hInjOn, -⟩ := maximal_parabolics (K := ZMod 2) (n := n) 2 (by omega)
    have hW1' := bot_lt_and_lt_top_of_finrank (K := ZMod 2) (n := n)
      (W := (dotOrth (flagSpace n (ZMod 2) d)).map
        (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))) (by omega) (by omega)
    have hW2' := bot_lt_and_lt_top_of_finrank (K := ZMod 2) (n := n)
      (W := flagSpace n (ZMod 2) d) (by omega) (by omega)
    have heq := hInjOn hW1' hW2' hP
    have := congrArg (fun W : Submodule (ZMod 2) (Fin n → ZMod 2) => finrank (ZMod 2) W) heq
    omega

end SL

end CFSG.Quasithin.H13.Lem1227Lt
