module

public import CFSG.Quasithin.Vol2.Ch9L34Bin16
public import CFSG.Quasithin.Vol2.Ch9L34Norm64

public section

namespace CFSG.Quasithin.H13.Ch9.L34B

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.L34Bin
open CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups


abbrev R64 : SL(3, F4) →* Matrix (Fin 64) (Fin 64) (ZMod 2) := autMat.comp (slRep rho64GL)

theorem fix64 {w : Wn 64} (hw : ∀ p ∈ upperUni F4, slRep rho64GL p w = w) :
    w = 1 ∨ w = toW 64 512 := by
  apply fixV_P64
  apply mem_fixV_closure
  rintro _ (rfl | rfl | rfl | rfl) <;> exact hw _ (uSL_mem_upperUni _ _ _)

theorem orbit_eq64 (w : Wn 64) :
    {x | ∃ γ ∈ img64, γ w = x} = {x | ∃ g, slRep rho64GL g w = x} := by
  ext x
  exact ⟨fun ⟨_, ⟨g, rfl⟩, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨_, ⟨g, rfl⟩, hg⟩⟩

theorem hirr64 : ∀ N : Submodule (ZMod 2) (Fin 64 → ZMod 2),
    (∀ g, ∀ v ∈ N, (R64 g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  hirr_of_fix (slRep rho64GL) (upperUni F4) isPGroup_U fun w hw1 hw => by
    rcases fix64 hw with rfl | rfl
    · exact absurd rfl hw1
    · rw [← orbit_eq64]
      exact closure_orbit64

theorem adGL_zSL : adGL (SpecialLinearGroup.toGL zSL) = 1 := by
  ext k l
  simp only [adGL, adM, Matrix.of_apply, conj_zSL, coord8_slOf, Pi.single_apply, Matrix.one_apply]

theorem rho64GL_zSL : slRep rho64GL zSL = 1 := by
  refine ext_toW64 fun m hm => ?_
  rw [slRep, MonoidHom.comp_apply, rho64GL_toW _ hm, adGL_zSL, actH8_one hm]
  rfl

theorem R64_zSL : R64 zSL = 1 := by
  rw [MonoidHom.comp_apply, rho64GL_zSL, map_one]

theorem exists_pair64 :
    ∃ (a b : Fin 2 → Bool) (Y Y' : Subrepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep (baseF R64))),
      Nonempty (Representation.Equiv Y.toRepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRep (F := F4) F4 a b))) ∧
      Nonempty (Representation.Equiv Y'.toRepresentation
        (CFSG.QuasithinUnique.Setup.X7.matRep
          (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b)))) ∧
      a = ![true, true] ∧ b = ![true, true] := by
  obtain ⟨a, b, Y, Y', -, -, eY, eY', -, hd, hn⟩ := exists_pair_digit R64 (by norm_num) hirr64
    R64_zSL (exists_ne_one_of_hirr R64 (by norm_num) hirr64)
  refine ⟨a, b, Y, Y', eY, eY', ?_⟩
  rcases dimT_digits5 hd with ⟨h9, -⟩ | ⟨h8, -⟩ | ⟨-, h⟩
  · simp only at h9
    omega
  · simp only at h8
    omega
  · exact Prod.ext_iff.mp h

theorem exists_scal64 {v v' : Fin 64 → ZMod 2} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hfv : ∀ p ∈ upperUni F4, (R64 p).mulVec v = v)
    (hfv' : ∀ p ∈ upperUni F4, (R64 p).mulVec v' = v') :
    ∃ S : Matrix (Fin 64) (Fin 64) (ZMod 2), (∀ g, S * R64 g = R64 g * S) ∧ S.mulVec v = v' := by
  have key : ∀ u : Fin 64 → ZMod 2, u ≠ 0 → (∀ p ∈ upperUni F4, (R64 p).mulVec u = u) →
      u = Multiplicative.toAdd (toW 64 512) := by
    intro u hu hfu
    have h1 : ∀ p ∈ upperUni F4, slRep rho64GL p (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd u := fun p hp => by
      have := hfu p hp
      rw [MonoidHom.comp_apply, autMat_mulVec] at this
      exact congrArg Multiplicative.ofAdd this
    rcases fix64 h1 with h | h
    · exact absurd (by simpa using congrArg Multiplicative.toAdd h) hu
    · exact congrArg Multiplicative.toAdd h
  exact ⟨1, fun g => by rw [Matrix.one_mul, Matrix.mul_one], by
    rw [Matrix.one_mulVec, key v hv hfv, key v' hv' hfv']⟩

end CFSG.Quasithin.H13.Ch9.L34B
