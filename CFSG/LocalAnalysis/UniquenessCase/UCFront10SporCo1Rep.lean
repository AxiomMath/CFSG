module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSpinCheck

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.KD.Co1K105
  CFSG.EvenSporadicStandard.Induction.AutBound CFSG.Monster.Schur.M24
open scoped Matrix

section Rep

@[expose] def Rep (M : Array ℕ) (p : PM24) : Prop := ∀ v, rho p v = v ᵥ* rowsMatrix 11 M

theorem rep_one : Rep (idRows 11) 1 := fun v => by
  rw [map_one, rowsMatrix_idRows, Matrix.vecMul_one]
  rfl

theorem rep_mul {M N : Array ℕ} {p q : PM24} (hM : Rep M p) (hN : Rep N q) :
    Rep (mulM M N) (p * q) := fun v => by
  rw [map_mul, LinearEquiv.mul_apply, hN v, hM, Matrix.vecMul_vecMul, mulM, rowsMatrix_mulRows]

theorem rep_apply {M : Array ℕ} {p : PM24} (h : Rep M p) (x : ℕ) :
    rho p (toVecD 11 x) = toVecD 11 (vecMulN 11 M x) := by
  rw [h, toVecD_vecMulN]

theorem rep_gen0 : Rep (transposeRows 11 Aa) (gen 0) := fun v => by
  rw [rho_gen0, rowsMatrix_transposeRows, Matrix.vecMul_transpose, Amat]

theorem rep_gen1 : Rep (transposeRows 11 Ba) (gen 1) := fun v => by
  rw [rho_gen1, rowsMatrix_transposeRows, Matrix.vecMul_transpose, Bmat]

theorem rep_foldl (w : List Bool) {M : Array ℕ} {p : PM24} (h : Rep M p) :
    Rep (w.foldl (fun acc c => mulM acc (if c then transposeRows 11 Ba else transposeRows 11 Aa))
      M) (p * eltPos (gen 0) (gen 1) w) := by
  induction w generalizing M p with
  | nil =>
    rw [List.foldl_nil, show eltPos (gen 0) (gen 1) [] = 1 by simp [eltPos], mul_one]
    exact h
  | cons c w ih =>
    rw [List.foldl_cons, eltPos_cons, ← mul_assoc]
    refine ih (rep_mul h ?_)
    cases c
    · exact rep_gen0
    · exact rep_gen1

theorem rep_t24Gen (i : Fin 4) : Rep (gensOf Aa Ba t24Codes)[i.val]! (t24Gen i) := by
  have hi : i.val < t24Codes.length := i.isLt
  have hs : i.val < (gensOf Aa Ba t24Codes).size := by simpa [gensOf] using hi
  have h := rep_foldl (wordOf (t24Codes.getD i.val (0, 0)).1 (t24Codes.getD i.val (0, 0)).2)
    rep_one
  rw [one_mul] at h
  have e : (gensOf Aa Ba t24Codes)[i.val]! = List.foldl
      (fun acc c => mulM acc (if c then transposeRows 11 Ba else transposeRows 11 Aa)) (idRows 11)
      (wordOf (t24Codes.getD i.val (0, 0)).1 (t24Codes.getD i.val (0, 0)).2) := by
    rw [getElem!_pos (gensOf Aa Ba t24Codes) i.val hs, List.getD_eq_getElem _ _ hi]
    simp only [gensOf, List.getElem_toArray, List.getElem_map, wordM]
  rw [e]
  exact h

theorem rho_injective : Function.Injective (rho : PM24 →* _) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have := isSimpleGroup_PM24
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (rho : PM24 →* _).ker).resolve_right
    fun h => ?_
  have h0 : rho (gen 0) = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
  have h1 := rep_apply rep_gen0 1
  rw [h0, show vecMulN 11 (transposeRows 11 Aa) 1 = 2 by decide] at h1
  exact absurd (toVecD_injective (by norm_num) (by norm_num) h1) (by norm_num)

theorem eq_of_rep {M : Array ℕ} {p q : PM24} (hp : Rep M p) (hq : Rep M q) : p = q :=
  rho_injective (LinearEquiv.ext fun v => (hp v).trans (hq v).symm)

end Rep

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
