module

public import CFSG.Quasithin.Background.L34BinMatch
public import CFSG.Quasithin.Vol2.Ch9L34Norm18

public section

namespace CFSG.Quasithin.H13.Ch9.L34B

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.L34Bin
open CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups

abbrev R9 : SL(3, F4) →* Matrix (Fin 9) (Fin 9) (ZMod 2) := autMat.comp (slRep rho9)

theorem uSL_mem_upperUni (a b c : F4) : uSL a b c ∈ upperUni F4 :=
  mem_upperUni.mpr ⟨c, b, a, Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)⟩

theorem isPGroup_U : IsPGroup 2 (upperUni F4) :=
  isPGroup_upperUni (by rw [Nat.card_eq_fintype_card, card_F4])

theorem fix9_gen {w : W9} (h1 : slRep rho9 (uSL (f4c 1) 0 0) w = w)
    (h2 : slRep rho9 (uSL (f4c 2) 0 0) w = w) (h3 : slRep rho9 (uSL 0 0 (f4c 1)) w = w)
    (h4 : slRep rho9 (uSL 0 0 (f4c 2)) w = w) : w = 1 ∨ w = toW 9 1 := by
  have hg : ∀ s ∈ gen18, s ((w, 1) : W18) = (w, 1) := by
    rintro _ (rfl | rfl | rfl | rfl)
    · exact (rho18GL_apply _ _).trans (Prod.ext h1 (map_one _))
    · exact (rho18GL_apply _ _).trans (Prod.ext h2 (map_one _))
    · exact (rho18GL_apply _ _).trans (Prod.ext h3 (map_one _))
    · exact (rho18GL_apply _ _).trans (Prod.ext h4 (map_one _))
  have h18 : ((w, 1) : W18) ∈ fixV P18 := mem_fixV_closure hg
  have hne : toW 9 1 ≠ (1 : W9) := fun h =>
    absurd (toW_inj (n := 9) (by norm_num) (by norm_num) (h.trans (toW_zero 9).symm))
      (by norm_num)
  rcases fixV_P18 h18 with h | h | h | h <;> rw [coords18_vm] at h
  · left
    rw [← toW_zero 9]
    exact congrArg Prod.fst h
  · right
    exact congrArg Prod.fst h
  · exact absurd (congrArg Prod.snd h).symm hne
  · exact absurd (congrArg Prod.snd h).symm hne

theorem fix9 {w : W9} (hw : ∀ p ∈ upperUni F4, slRep rho9 p w = w) :
    w = 1 ∨ w = toW 9 1 :=
  fix9_gen (hw _ (uSL_mem_upperUni _ _ _)) (hw _ (uSL_mem_upperUni _ _ _))
    (hw _ (uSL_mem_upperUni _ _ _)) (hw _ (uSL_mem_upperUni _ _ _))

theorem closure_orbit9 : Subgroup.closure {x | ∃ g, slRep rho9 g (toW 9 1) = x} = ⊤ := by
  have h18 := congrArg (Subgroup.map (MonoidHom.fst W9 W9)) closure_orbit18
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ Prod.fst_surjective] at h18
  rw [eq_top_iff, ← h18]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
  refine ⟨g, ?_⟩
  have h1 := congrArg Prod.fst (rho18GL_apply (SpecialLinearGroup.toGL g) (coords18.vm 513))
  have h2 : (coords18.vm 513).1 = toW 9 1 := by
    rw [coords18_vm]
    show toW 9 513 = toW 9 1
    rw [← toW_mod 9 513]
    rfl
  rw [h2] at h1
  exact h1.symm

theorem hirr9 : ∀ N : Submodule (ZMod 2) (Fin 9 → ZMod 2),
    (∀ g, ∀ v ∈ N, (R9 g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  hirr_of_fix (slRep rho9) (upperUni F4) isPGroup_U fun w hw1 hw => by
    rcases fix9 hw with rfl | rfl
    · exact absurd rfl hw1
    · exact closure_orbit9

theorem omega_mul_omega_mul_omega : (omegaU : F4) * ((omegaU : F4) * omegaU) = 1 := by
  rw [← (omega_pow_eq_one_iff 3).mpr rfl]
  ring

theorem coe_toGL_zSL :
    ((SpecialLinearGroup.toGL zSL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      Matrix.diagonal fun _ => (omegaU : F4) := by
  have hω : (omegaU : F4)⁻¹ = omegaU * omegaU :=
    inv_eq_of_mul_eq_one_right omega_mul_omega_mul_omega
  have hinv : (omegaU : F4)⁻¹ * (omegaU : F4)⁻¹ = omegaU := by
    rw [hω]
    calc (omegaU : F4) * omegaU * (omegaU * omegaU) =
        omegaU * (omegaU * (omegaU * omegaU)) := by ring
      _ = omegaU := by rw [omega_mul_omega_mul_omega, mul_one]
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, zSL, dT_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dTMat, hinv]

theorem rho9_zSL : slRep rho9 zSL = 1 := by
  have h : ∀ Y : Matrix (Fin 3) (Fin 3) F4, Matrix.diagonal (fun _ => (omegaU : F4)) * Y *
      (bar (Matrix.diagonal fun _ => (omegaU : F4)))ᵀ = Y := by
    intro Y
    ext i j
    simp only [bar, Matrix.diagonal_map (show cj 0 = 0 from rfl), Matrix.diagonal_transpose,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [cj, mul_comm _ (Y i j), mul_assoc, omega_mul_omega_mul_omega, mul_one]
  have hact : ∀ m, act (SpecialLinearGroup.toGL zSL : GL (Fin 3) F4) m = m := fun m => by
    rw [act, coe_toGL_zSL, h, code_herm]
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, rfl⟩ := toW9.surjective w
  exact (rho9_toW9 _ m).trans (congrArg toW9 (hact m))

theorem R9_zSL : R9 zSL = 1 := by
  rw [MonoidHom.comp_apply, rho9_zSL, map_one]

theorem exists_pair9 :
    ∃ (a b : Fin 2 → Bool) (Y Y' : Subrepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep (baseF R9))),
      Nonempty (Representation.Equiv Y.toRepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRep (F := F4) F4 a b))) ∧
      Nonempty (Representation.Equiv Y'.toRepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep
          (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b)))) ∧
      ((a = ![true, true] ∧ b = ![false, false]) ∨ (a = ![false, false] ∧ b = ![true, true])) := by
  obtain ⟨a, b, Y, Y', -, -, eY, eY', -, hd, hn⟩ := exists_pair_digit R9 (by norm_num) hirr9
    R9_zSL (exists_ne_one_of_hirr R9 (by norm_num) hirr9)
  refine ⟨a, b, Y, Y', eY, eY', ?_⟩
  rcases dimT_digits5 hd with ⟨h9, h | h⟩ | ⟨h8, -⟩ | ⟨h64, -⟩
  · exact Or.inl (Prod.ext_iff.mp h)
  · exact Or.inr (Prod.ext_iff.mp h)
  · simp only at h8
    omega
  · simp only at h64
    omega

theorem toGL_gamSL (g : SL(3, F4)) :
    SpecialLinearGroup.toGL (gamSL g) = grGL (SpecialLinearGroup.toGL g) := by
  rw [gamSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, grGL_apply, coe_grU, grM, w0GLb, ← map_inv, wJ_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, tauSL_coe, trInvMat, wJ_coe]
  rfl

theorem gamSL_uSL (a b c : F4) : gamSL (uSL a b c) = uSL c (a * c + b) a := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_gamSL, toGL_uSL, toGL_uSL]
  apply Units.ext
  rw [grGL_apply, coe_grU, grM, coe_uGL_inv, coe_uGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w0, um, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

noncomputable abbrev R9g : SL(3, F4) →* Matrix (Fin 9) (Fin 9) (ZMod 2) := R9.comp gamSL

theorem fix9g {w : W9} (hw : ∀ p ∈ upperUni F4, slRep rho9 (gamSL p) w = w) :
    w = 1 ∨ w = toW 9 1 := by
  have e : ∀ t : F4, gamSL (uSL 0 0 t) = uSL t 0 0 ∧ gamSL (uSL t 0 0) = uSL 0 0 t := fun t =>
    ⟨by rw [gamSL_uSL, zero_mul, add_zero], by rw [gamSL_uSL, mul_zero, add_zero]⟩
  refine fix9_gen ?_ ?_ ?_ ?_
  · rw [← (e _).1]
    exact hw _ (uSL_mem_upperUni _ _ _)
  · rw [← (e _).1]
    exact hw _ (uSL_mem_upperUni _ _ _)
  · rw [← (e _).2]
    exact hw _ (uSL_mem_upperUni _ _ _)
  · rw [← (e _).2]
    exact hw _ (uSL_mem_upperUni _ _ _)

theorem eq_of_fix9 {σ : SL(3, F4) →* MulAut W9}
    (hfix : ∀ {w : W9}, (∀ p ∈ upperUni F4, σ p w = w) → w = 1 ∨ w = toW 9 1)
    {v : Fin 9 → ZMod 2} (hv : v ≠ 0)
    (hfv : ∀ p ∈ upperUni F4, ((autMat.comp σ) p).mulVec v = v) :
    v = Multiplicative.toAdd (toW 9 1) := by
  have h1 : ∀ p ∈ upperUni F4, σ p (Multiplicative.ofAdd v) = Multiplicative.ofAdd v :=
    fun p hp => by
      have := hfv p hp
      rw [MonoidHom.comp_apply, autMat_mulVec] at this
      exact congrArg Multiplicative.ofAdd this
  rcases hfix h1 with h | h
  · exact absurd (by simpa using congrArg Multiplicative.toAdd h) hv
  · exact congrArg Multiplicative.toAdd h

theorem exists_scal9 {v v' : Fin 9 → ZMod 2} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hfv : ∀ p ∈ upperUni F4, (R9 p).mulVec v = v)
    (hfv' : ∀ p ∈ upperUni F4, (R9 p).mulVec v' = v') :
    ∃ S : Matrix (Fin 9) (Fin 9) (ZMod 2), (∀ g, S * R9 g = R9 g * S) ∧ S.mulVec v = v' :=
  ⟨1, fun g => by rw [Matrix.one_mul, Matrix.mul_one], by
    rw [Matrix.one_mulVec, eq_of_fix9 fix9 hv hfv, eq_of_fix9 fix9 hv' hfv']⟩

theorem exists_scal9g {v v' : Fin 9 → ZMod 2} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hfv : ∀ p ∈ upperUni F4, (R9g p).mulVec v = v)
    (hfv' : ∀ p ∈ upperUni F4, (R9g p).mulVec v' = v') :
    ∃ S : Matrix (Fin 9) (Fin 9) (ZMod 2), (∀ g, S * R9g g = R9g g * S) ∧ S.mulVec v = v' :=
  ⟨1, fun g => by rw [Matrix.one_mul, Matrix.mul_one], by
    rw [Matrix.one_mulVec, eq_of_fix9 (σ := (slRep rho9).comp gamSL) fix9g hv hfv,
      eq_of_fix9 (σ := (slRep rho9).comp gamSL) fix9g hv' hfv']⟩

theorem hirr9g : ∀ N : Submodule (ZMod 2) (Fin 9 → ZMod 2),
    (∀ g, ∀ v ∈ N, (R9g g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  hirr_comp R9 hirr9 gamSL gamSL_surjective

end CFSG.Quasithin.H13.Ch9.L34B

