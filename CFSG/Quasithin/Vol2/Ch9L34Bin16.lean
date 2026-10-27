module

public import CFSG.Quasithin.Vol2.Ch9L34Bin9
public import CFSG.Quasithin.Vol2.Ch9L34Norm16

public section

namespace CFSG.Quasithin.H13.Ch9.L34B

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.L34Bin
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.Monster.Code (bvec)
open scoped MatrixGroups

abbrev R16 : SL(3, F4) →* Matrix (Fin 16) (Fin 16) (ZMod 2) := autMat.comp (slRep rho16GL)

theorem fix16 {w : Wn 16} (hw : ∀ p ∈ upperUni F4, slRep rho16GL p w = w) :
    w = toW 16 0 ∨ w = toW 16 4 ∨ w = toW 16 8 ∨ w = toW 16 12 := by
  apply fixV_P16
  apply mem_fixV_closure
  rintro _ (rfl | rfl | rfl | rfl) <;> exact hw _ (uSL_mem_upperUni _ _ _)

theorem orbit_eq16 (w : Wn 16) :
    {x | ∃ γ ∈ img16, γ w = x} = {x | ∃ g, slRep rho16GL g w = x} := by
  ext x
  exact ⟨fun ⟨_, ⟨g, rfl⟩, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨_, ⟨g, rfl⟩, hg⟩⟩

theorem hirr16 : ∀ N : Submodule (ZMod 2) (Fin 16 → ZMod 2),
    (∀ g, ∀ v ∈ N, (R16 g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  hirr_of_fix (slRep rho16GL) (upperUni F4) isPGroup_U fun w hw1 hw => by
    rcases fix16 hw with rfl | rfl | rfl | rfl
    · exact absurd (toW_zero 16) hw1
    · rw [← orbit_eq16]
      exact closure_orbit16 (by simp)
    · rw [← orbit_eq16]
      exact closure_orbit16 (by simp)
    · rw [← orbit_eq16]
      exact closure_orbit16 (by simp)

theorem conj_zSL (X : Matrix (Fin 3) (Fin 3) F4) :
    ((SpecialLinearGroup.toGL zSL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) * X *
      (↑(SpecialLinearGroup.toGL zSL)⁻¹ : Matrix (Fin 3) (Fin 3) F4) = X := by
  have hc : ((SpecialLinearGroup.toGL zSL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) * X =
      X * ((SpecialLinearGroup.toGL zSL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
    rw [coe_toGL_zSL]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact mul_comm _ _
  rw [hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem rho16GL_zSL : slRep rho16GL zSL = 1 := by
  refine ext_toW16 fun m hm => ?_
  rw [slRep, MonoidHom.comp_apply, rho16GL_toW _ hm, act16, conj_zSL, csl_sl hm]
  rfl

theorem R16_zSL : R16 zSL = 1 := by
  rw [MonoidHom.comp_apply, rho16GL_zSL, map_one]

theorem exists_pair16 :
    ∃ (a b : Fin 2 → Bool) (Y Y' : Subrepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep (baseF R16))),
      Nonempty (Representation.Equiv Y.toRepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRep (F := F4) F4 a b))) ∧
      Nonempty (Representation.Equiv Y'.toRepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep
          (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b)))) ∧
      ((a = ![true, false] ∧ b = ![true, false]) ∨ (a = ![false, true] ∧ b = ![false, true])) := by
  obtain ⟨a, b, Y, Y', -, -, eY, eY', -, hd, hn⟩ := exists_pair_digit R16 (by norm_num) hirr16
    R16_zSL (exists_ne_one_of_hirr R16 (by norm_num) hirr16)
  refine ⟨a, b, Y, Y', eY, eY', ?_⟩
  rcases dimT_digits5 hd with ⟨h9, -⟩ | ⟨h8, h | h⟩ | ⟨h64, -⟩
  · simp only at h9
    omega
  · exact Or.inl (Prod.ext_iff.mp h)
  · exact Or.inr (Prod.ext_iff.mp h)
  · simp only at h64
    omega

@[expose] def scalN (c : F4) (m : ℕ) : ℕ := csl (c • sl m)

theorem isSl_smul (c : F4) {X : Matrix (Fin 3) (Fin 3) F4} (h : IsSl X) : IsSl (c • X) := by
  rw [IsSl] at h ⊢
  simp only [Matrix.smul_apply, smul_eq_mul, h, mul_add]

theorem xorLin_scalN (c : F4) : XorLin (scalN c) := fun a b => by
  rw [scalN, scalN, scalN, sl_xor, smul_add, csl_add]

theorem scalN_scalN {c d : F4} (hcd : c * d = 1) {m : ℕ} (hm : m < 2 ^ 16) :
    scalN c (scalN d m) = m := by
  rw [scalN, scalN, sl_csl (isSl_smul d (isSl_sl m)), smul_smul, hcd, one_smul, csl_sl hm]

@[expose] def scal16 (c d : F4) (hcd : c * d = 1) : MulAut (Wn 16) :=
  autMask 16 (scalN c) (scalN d) (xorLin_scalN c) (fun _ => csl_lt _) (fun _ => csl_lt _)
    (fun _ hm => scalN_scalN (by rw [mul_comm]; exact hcd) hm) (fun _ hm => scalN_scalN hcd hm)

theorem scal16_toW {c d : F4} (hcd : c * d = 1) {m : ℕ} (hm : m < 2 ^ 16) :
    scal16 c d hcd (toW 16 m) = toW 16 (scalN c m) :=
  autMask_toW _ _ _ _ _ hm

theorem scal16_comm {c d : F4} (hcd : c * d = 1) (g : SL(3, F4)) :
    scal16 c d hcd * slRep rho16GL g = slRep rho16GL g * scal16 c d hcd := by
  refine ext_toW16 fun m hm => ?_
  simp only [MulAut.mul_apply, slRep, MonoidHom.comp_apply]
  rw [rho16GL_toW _ hm, scal16_toW _ (act16_lt _ _ _), scal16_toW _ hm,
    show scalN c m = csl (c • sl m) from rfl, rho16GL_toW _ (csl_lt _), act16, act16, scalN,
    sl_csl (isSl_conj _ _ (Units.inv_mul _) (isSl_sl m)), sl_csl (isSl_smul c (isSl_sl m)),
    Matrix.mul_smul, Matrix.smul_mul]

theorem exists_iterate_scalN : ∀ m ∈ [4, 8, 12], ∀ m' ∈ [4, 8, 12],
    ∃ k ∈ [0, 1, 2], (scalN ⟨2⟩)^[k] m = m' := by
  decide +kernel

theorem exists_scal16 {v v' : Fin 16 → ZMod 2} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hfv : ∀ p ∈ upperUni F4, (R16 p).mulVec v = v)
    (hfv' : ∀ p ∈ upperUni F4, (R16 p).mulVec v' = v') :
    ∃ S : Matrix (Fin 16) (Fin 16) (ZMod 2), (∀ g, S * R16 g = R16 g * S) ∧ S.mulVec v = v' := by
  have hω : (⟨2⟩ : F4) * ⟨3⟩ = 1 := congrArg F4.mk (by decide)
  have hfix : ∀ u : Fin 16 → ZMod 2, u ≠ 0 → (∀ p ∈ upperUni F4, (R16 p).mulVec u = u) →
      ∃ m ∈ [4, 8, 12], u = bvec 16 m := by
    intro u hu hfu
    have h1 : ∀ p ∈ upperUni F4, slRep rho16GL p (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd u := fun p hp => by
      have := hfu p hp
      rw [MonoidHom.comp_apply, autMat_mulVec] at this
      exact congrArg Multiplicative.ofAdd this
    rcases fix16 h1 with h | h | h | h <;> have e := congrArg Multiplicative.toAdd h <;>
      simp only [toAdd_ofAdd, toAdd_toW] at e
    · have hz : bvec 16 0 = 0 := by rw [← toAdd_toW, toW_zero, toAdd_one]
      exact absurd (e.trans hz) hu
    · exact ⟨4, by simp, e⟩
    · exact ⟨8, by simp, e⟩
    · exact ⟨12, by simp, e⟩
  let S1 : Matrix (Fin 16) (Fin 16) (ZMod 2) := autMat (scal16 ⟨2⟩ ⟨3⟩ hω)
  have hS1 : ∀ g, S1 * R16 g = R16 g * S1 := fun g => by
    show autMat (scal16 ⟨2⟩ ⟨3⟩ hω) * autMat (slRep rho16GL g) =
      autMat (slRep rho16GL g) * autMat (scal16 ⟨2⟩ ⟨3⟩ hω)
    rw [← map_mul, scal16_comm, map_mul]
  have hSk : ∀ k g, S1 ^ k * R16 g = R16 g * S1 ^ k := by
    intro k g
    induction k with
    | zero => rw [pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, hS1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hS1v : ∀ m, m < 2 ^ 16 → S1.mulVec (bvec 16 m) = bvec 16 (scalN ⟨2⟩ m) := fun m hm => by
    rw [autMat_mulVec]
    exact congrArg Multiplicative.toAdd (scal16_toW hω hm)
  have hpow : ∀ k m, m < 2 ^ 16 →
      (S1 ^ k).mulVec (bvec 16 m) = bvec 16 ((scalN ⟨2⟩)^[k] m) := by
    intro k
    induction k with
    | zero => intro m _; rw [pow_zero, Matrix.one_mulVec]; rfl
    | succ k ih =>
      intro m hm
      rw [pow_succ, ← Matrix.mulVec_mulVec, hS1v m hm,
        ih _ (show scalN ⟨2⟩ m < 2 ^ 16 from csl_lt _), Function.iterate_succ_apply]
  obtain ⟨m, hm, hvm⟩ := hfix v hv hfv
  obtain ⟨m', hm', hvm'⟩ := hfix v' hv' hfv'
  obtain ⟨k, -, hk⟩ := exists_iterate_scalN m hm m' hm'
  have hlt : m < 2 ^ 16 := by
    have h4 : ∀ x ∈ [4, 8, 12], x < 2 ^ 16 := by decide
    exact h4 m hm
  refine ⟨S1 ^ k, hSk k, ?_⟩
  rw [hvm, hvm', hpow k m hlt, hk]

end CFSG.Quasithin.H13.Ch9.L34B
