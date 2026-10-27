module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartOne.KFU.OrthChar2

structure QSpace (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module K X] where
  Q : X → K
  B : X →ₗ[K] X →ₗ[K] K
  Q_smul : ∀ (r : K) (x : X), Q (r • x) = r ^ 2 * Q x
  Q_add : ∀ x y : X, Q (x + y) = Q x + Q y + B x y

variable {K : Type} [Field K] {X : Type} [AddCommGroup X] [Module K X]

@[expose] def QSpace.prod {X₁ X₂ : Type} [AddCommGroup X₁] [Module K X₁] [AddCommGroup X₂]
    [Module K X₂] (S₁ : QSpace K X₁) (S₂ : QSpace K X₂) : QSpace K (X₁ × X₂) where
  Q x := S₁.Q x.1 + S₂.Q x.2
  B := S₁.B.compl₁₂ (LinearMap.fst K X₁ X₂) (LinearMap.fst K X₁ X₂) +
    S₂.B.compl₁₂ (LinearMap.snd K X₁ X₂) (LinearMap.snd K X₁ X₂)
  Q_smul r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, S₁.Q_smul, S₂.Q_smul]
    ring
  Q_add x y := by
    simp only [Prod.fst_add, Prod.snd_add, S₁.Q_add, S₂.Q_add, LinearMap.add_apply,
      LinearMap.compl₁₂_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    ring

namespace QSpace

variable (S : QSpace K X)

theorem Q_zero : S.Q 0 = 0 := by
  have h := S.Q_smul 0 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at h

theorem B_symm (x y : X) : S.B x y = S.B y x := by
  have h1 := S.Q_add x y
  have h2 := S.Q_add y x
  rw [add_comm y x] at h2
  linear_combination h2 - h1

theorem B_map {g : X →ₗ[K] X} (hg : ∀ x, S.Q (g x) = S.Q x) (x y : X) :
    S.B (g x) (g y) = S.B x y := by
  have h1 := S.Q_add (g x) (g y)
  have h2 := S.Q_add x y
  rw [← map_add, hg, hg, hg] at h1
  linear_combination h2 - h1

end QSpace

variable (S : QSpace K X)

@[expose] def Qh (d : K × K × X) : K := d.1 * d.2.1 + S.Q d.2.2

@[expose] def Top (w : X) : Module.End K (K × K × X) where
  toFun d := (d.1 + S.B d.2.2 w + S.Q w * d.2.1, d.2.1, d.2.2 + d.2.1 • w)
  map_add' d e := by
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring
    · simp only [Prod.snd_add, Prod.fst_add, add_smul]
      abel
  map_smul' r d := by
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring
    · simp only [Prod.smul_snd, Prod.smul_fst, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply]

theorem Top_apply (w : X) (d : K × K × X) :
    Top S w d = (d.1 + S.B d.2.2 w + S.Q w * d.2.1, d.2.1, d.2.2 + d.2.1 • w) := rfl

theorem Top_zero : Top S (0 : X) = 1 := LinearMap.ext fun d => by
  simp [Top_apply, S.Q_zero]

theorem Top_add (w w' : X) : Top S (w + w') = Top S w * Top S w' :=
  LinearMap.ext fun d => by
    simp only [Module.End.mul_apply, Top_apply]
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [S.Q_add w w', map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, S.B_symm w' w]
      ring
    · simp only [smul_add]
      abel

@[expose] def Tend : Multiplicative X →* Module.End K (K × K × X) where
  toFun w := Top S (Multiplicative.toAdd w)
  map_one' := Top_zero S
  map_mul' _ _ := Top_add S _ _

theorem Qh_Top (h2 : (2 : K) = 0) (w : X) (d : K × K × X) : Qh S (Top S w d) = Qh S d := by
  simp only [Qh, Top_apply, S.Q_add, S.Q_smul, map_smul, smul_eq_mul]
  linear_combination (d.2.1 * S.B d.2.2 w + S.Q w * d.2.1 ^ 2) * h2

@[expose] def Gop (g : X →ₗ[K] X) : Module.End K (K × K × X) where
  toFun d := (d.1, d.2.1, g d.2.2)
  map_add' d e := by simp [map_add]
  map_smul' r d := by simp [map_smul]

@[expose] def Gend : Module.End K X →* Module.End K (K × K × X) where
  toFun := Gop
  map_one' := LinearMap.ext fun d => by simp [Gop]
  map_mul' g h := LinearMap.ext fun d => by simp [Gop]

theorem Gend_apply (g : X →ₗ[K] X) (d : K × K × X) : Gend g d = (d.1, d.2.1, g d.2.2) := rfl

theorem Qh_Gend {g : X →ₗ[K] X} (hg : ∀ x, S.Q (g x) = S.Q x) (d : K × K × X) :
    Qh S (Gend g d) = Qh S d := by
  simp only [Qh, Gend_apply, hg]

theorem Gend_mul_Top {g : X →ₗ[K] X} (hg : ∀ x, S.Q (g x) = S.Q x) (w : X) :
    Gend g * Top S w = Top S (g w) * Gend g := by
  refine LinearMap.ext fun d => ?_
  simp only [Module.End.mul_apply, Gend_apply, Top_apply]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · simp only [S.B_map hg, hg]
  · simp only [map_add, map_smul]

end CFSG.RankThree.PartOne.KFU.OrthChar2
