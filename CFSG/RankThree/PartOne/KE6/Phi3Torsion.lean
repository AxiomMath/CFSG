module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.PartOne.KE6.Phi3Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open scoped Matrix

variable {L : Type} [Field L] {Fr : L →+* L}

theorem dualMatrix_e6T3W {R : Type*} [CommRing R] :
    dualMatrix R e6T3W = ((e6T3Matrix.map (Int.cast : ℤ → R)).transpose) := by
  rw [dualMatrix, weylMatrix_e6T3W_eq]

theorem phi3Matrix_transpose_mulVec_eq_zero_iff {p : ℕ} (q : ℕ)
    (z : Fin Tag.E6.rank → ZMod p) :
    ((phi3Matrix q)ᵀ.map (Int.cast : ℤ → ZMod p)) *ᵥ z = 0 ↔
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q : ZMod p) • z := by
  have hM : (phi3Matrix q)ᵀ.map (Int.cast : ℤ → ZMod p) =
      dualMatrix (ZMod p) e6T3W - Matrix.scalar (Fin Tag.E6.rank) (q : ZMod p) := by
    rw [dualMatrix_e6T3W, phi3Matrix, Matrix.transpose_sub, Matrix.map_sub _ Int.cast_sub,
      Matrix.transpose_map]
    congr 1
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_transpose,
      Matrix.diagonal_map Int.cast_zero]
    simp only [Int.cast_natCast]
  rw [hM, Matrix.sub_mulVec, sub_eq_zero]
  have : Matrix.scalar (Fin Tag.E6.rank) (q : ZMod p) *ᵥ z = (q : ZMod p) • z := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this]

theorem phi3_prime_setup [IsAlgClosed L] {q : ℕ} (hq : (q : L) = 0) {p : ℕ} (hp : p.Prime)
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 + (q : ℤ) + 1) :
    (p : L) ≠ 0 ∧ (∃ ζ : Lˣ, IsPrimitiveRoot ζ p) ∧
      ((q : ℕ) : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0 := by
  have hpL : (p : L) ≠ 0 := fun h => by
    obtain ⟨c, hc⟩ := hpq
    have h1 : (((q : ℤ) ^ 2 + (q : ℤ) + 1 : ℤ) : L) = 0 := by
      rw [hc]; push_cast; rw [h, zero_mul]
    push_cast at h1
    rw [hq] at h1
    norm_num at h1
  refine ⟨hpL, ?_, ?_⟩
  · have : NeZero (p : L) := ⟨hpL⟩
    have := IsSepClosed.hasEnoughRootsOfUnity L p
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
    refine ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp ?_⟩
    rw [IsUnit.unit_spec]
    exact hζ₀
  · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpq
    push_cast at h
    exact h

theorem exists_column_of_phi3Torus [IsAlgClosed L] {q p : ℕ} [NeZero p]
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) {x : ModGL Tag.E6 L}
    (hx : x ∈ twistedTorus (phi3N L) Fr) (hxp : x ^ p = 1) :
    ∃ z : Fin Tag.E6.rank → ZMod p,
      x = rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val) ∧
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q : ZMod p) • z ∧
      torusRootKernel x = rootKernel z ∧ (x ≠ 1 → z ≠ 0) := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
  have hbker : b ∈ (monomialHom (G := Lˣ) (phi3Matrix q)ᵀ).ker :=
    (mem_twistedTorus_rootDiagUnit_iff3 hFr b).1 (by rw [← hb]; exact hx)
  obtain ⟨z, hz⟩ := exists_eq_rootDiagUnit_zetaPow hζ (mem_twistedTorus.1 hx).1 hxp
  have hbz : b = fun i => ζ ^ (z i).val := rootDiagUnit_injective (hb.symm.trans hz)
  have hzc : (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q : ZMod p) • z := by
    rw [← phi3Matrix_transpose_mulVec_eq_zero_iff q z, ← zetaPow_mem_ker_monomialHom_iff hζ,
      ← hbz]
    exact hbker
  refine ⟨z, hz, hzc, ?_, fun hx1 hz0 => hx1 ?_⟩
  · rw [hz, torusRootKernel_rootDiagUnit, rootCharKernel_zetaPow hζ]
  · rw [hz, hz0]
    have : (fun i => ζ ^ ((0 : Fin Tag.E6.rank → ZMod p) i).val) = 1 := by
      funext i
      simp
    rw [this, rootDiagUnit_one]

end CFSG.RankThree.PartOne.KE6
