module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H Matrix

variable {K F : Type} [Field K] [Field F]

@[expose] noncomputable def glMapEquiv (e : K ≃+* F) :
    GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 2 ⊕ Fin 2) F :=
  Units.mapEquiv (e.mapMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K ≃+*
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toMulEquiv

theorem coe_glMapEquiv (e : K ≃+* F) (g : GL (Fin 2 ⊕ Fin 2) K) :
    ((glMapEquiv e g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map e := rfl

theorem map_fromBlocks_J (e : K ≃+* F) :
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K)
      (-1 : Matrix (Fin 2) (Fin 2) K) 0).map e =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F)
        (-1 : Matrix (Fin 2) (Fin 2) F) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem map_mem_statedSp (e : K ≃+* F) {g : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ StatedSp 2 K) :
    glMapEquiv e g ∈ StatedSp 2 F := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff] at hg ⊢
  rw [coe_glMapEquiv, ← Matrix.transpose_map, ← map_fromBlocks_J e]
  have h := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M.map e) hg
  simp only [Matrix.map_mul] at h
  rw [map_fromBlocks_J e] at h
  rw [← map_fromBlocks_J e] at h
  exact h

@[expose] noncomputable def mapSp (e : K ≃+* F) : StatedSp 2 K ≃* StatedSp 2 F where
  toFun g := ⟨glMapEquiv e g, map_mem_statedSp e g.2⟩
  invFun g := ⟨glMapEquiv e.symm g, map_mem_statedSp e.symm g.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [coe_glMapEquiv]
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [coe_glMapEquiv]
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (glMapEquiv e) _ _

@[expose] noncomputable def stdMapEquiv (e : K ≃+* F) :
    StdMod (Fin 2 ⊕ Fin 2) K ≃* StdMod (Fin 2 ⊕ Fin 2) F :=
  (AddEquiv.piCongrRight fun _ => e.toAddEquiv).toMultiplicative

theorem stdMapEquiv_apply (e : K ≃+* F) (x : StdMod (Fin 2 ⊕ Fin 2) K) :
    Multiplicative.toAdd (stdMapEquiv e x) = fun i => e (Multiplicative.toAdd x i) := rfl

theorem stdMapEquiv_matAut (e : K ≃+* F) (g : GL (Fin 2 ⊕ Fin 2) K) (x : StdMod (Fin 2 ⊕ Fin 2) K) :
    stdMapEquiv e (matAut g x) = matAut (glMapEquiv e g) (stdMapEquiv e x) := by
  apply Multiplicative.toAdd.injective
  rw [stdMapEquiv_apply]
  have h1 : Multiplicative.toAdd (matAut g x) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Multiplicative.toAdd x := rfl
  have h2 : Multiplicative.toAdd (matAut (glMapEquiv e g) (stdMapEquiv e x)) =
      ((glMapEquiv e g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        Multiplicative.toAdd (stdMapEquiv e x) := rfl
  rw [h1, h2, coe_glMapEquiv, stdMapEquiv_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, map_mul]

end Sp4Inf

end CFSG.Quasithin
