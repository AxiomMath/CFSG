module

public import CFSG.Timmesfeld.Moufang.J2
import CFSG.Sporadic.J2.Representations.Module12Pack

public section

namespace CFSG.Sporadic.J2.Module12

open CFSG.Timmesfeld.Moufang CFSG.Certificates

@[expose] def toM12 (X : List (List ℕ)) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  Matrix.of fun i j => ((X.getD i.val []).getD j.val 0 : ℕ)

@[expose] def a12 : List (List ℕ) := [
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def b12 : List (List ℕ) := [
  [1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0],
  [0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0],
  [1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1],
  [0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]]

@[expose] def b12i : List (List ℕ) := [
  [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1],
  [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0],
  [0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0],
  [0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1],
  [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

theorem a12_mul : toM12 a12 * toM12 a12 = 1 := by
  have pA : toM12 a12 = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 a12) := by
    decide +kernel
  rw [pA, ← CFSG.KC.F2Mat.matOfF_mulF, ← CFSG.KC.F2Mat.matOfF_idF 12]
  exact congrArg (CFSG.KC.WordPts.matOfF 12) (by decide +kernel)

theorem b12_mul : toM12 b12 * toM12 b12i = 1 := by
  have pB : toM12 b12 = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 b12) := by
    decide +kernel
  have pBi : toM12 b12i = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 b12i) := by
    decide +kernel
  rw [pB, pBi, ← CFSG.KC.F2Mat.matOfF_mulF, ← CFSG.KC.F2Mat.matOfF_idF 12]
  exact congrArg (CFSG.KC.WordPts.matOfF 12) (by decide +kernel)

theorem b12i_mul : toM12 b12i * toM12 b12 = 1 := by
  have pB : toM12 b12 = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 b12) := by
    decide +kernel
  have pBi : toM12 b12i = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 b12i) := by
    decide +kernel
  rw [pB, pBi, ← CFSG.KC.F2Mat.matOfF_mulF, ← CFSG.KC.F2Mat.matOfF_idF 12]
  exact congrArg (CFSG.KC.WordPts.matOfF 12) (by decide +kernel)

@[expose] noncomputable def A12 : GL (Fin 12) (ZMod 2) :=
  ⟨toM12 a12, toM12 a12, a12_mul, a12_mul⟩

@[expose] noncomputable def B12 : GL (Fin 12) (ZMod 2) :=
  ⟨toM12 b12, toM12 b12i, b12_mul, b12i_mul⟩

@[expose] noncomputable def d12 : GL (Fin 12) (ZMod 2) :=
  CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then A12 else B12) J2.wordD

@[expose] noncomputable def uABD12 : ℕ → GL (Fin 12) (ZMod 2)
  | 0 => A12
  | 1 => B12
  | _ => d12

@[expose] noncomputable def gen12 : Fin 7 → GL (Fin 12) (ZMod 2)
  | ⟨0, _⟩ => d12
  | j => CFSG.Sporadic.Bridge.wordProd uABD12 (J2.genWord j.val)

set_option maxRecDepth 100000 in
theorem gen12_relators : ∀ w ∈ lineRels 5 true, signedProd gen12 w = 1 := by
  have pA : toM12 a12 = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 a12) := by
    decide +kernel
  have pB : toM12 b12 = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 b12) := by
    decide +kernel
  have pBi : toM12 b12i = CFSG.KC.WordPts.matOfF 12 (Module12Pack.packL 12 b12i) := by
    decide +kernel
  exact Module12Pack.relators_of_codes (A := A12) (B := B12) pA pA pB pBi uABD12 rfl rfl
    (fun _ => rfl) gen12 (fun _ => rfl) (fun _ _ => rfl) (by decide +kernel)

@[expose] noncomputable def repPres : J2.Pres →* GL (Fin 12) (ZMod 2) :=
  wordsHom (lineRels 5 true) gen12 gen12_relators

set_option maxRecDepth 100000 in
theorem d12_ne_one : d12 ≠ 1 := by
  decide +kernel

theorem gen12_zero : gen12 0 = d12 := rfl

theorem repPres_of_zero : repPres (PresentedGroup.of (0 : Fin 7)) = d12 := by
  rw [repPres, wordsHom_of, gen12_zero]


@[expose] noncomputable def rep12 : CFSG.Blueprint.NativeSporadic.J2 →* GL (Fin 12) (ZMod 2) :=
  repPres.comp (Classical.choice J2.nonempty_mulEquiv).symm.toMonoidHom


theorem isSimpleGroup_native : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
  CFSG.Sporadic.J2.isSimpleGroup_J2

theorem rep12_injective : Function.Injective rep12 := by
  rw [← MonoidHom.ker_eq_bot_iff]
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := isSimpleGroup_native
  haveI := (rep12).normal_ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (rep12).ker with h | h
  · exact h
  · exfalso
    have h1 : rep12 = 1 := by
      ext x i j
      have hx : x ∈ (rep12).ker := by rw [h]; exact Subgroup.mem_top x
      have hm : rep12 x = 1 := by simpa [MonoidHom.mem_ker] using hx
      rw [hm]
      rfl
    apply d12_ne_one
    have hd : rep12 ((Classical.choice J2.nonempty_mulEquiv) (PresentedGroup.of 0)) = d12 := by
      show repPres ((Classical.choice J2.nonempty_mulEquiv).symm
        ((Classical.choice J2.nonempty_mulEquiv) (PresentedGroup.of 0))) = d12
      rw [MulEquiv.symm_apply_apply, repPres_of_zero]
    rw [h1] at hd
    simpa using hd.symm

end CFSG.Sporadic.J2.Module12
