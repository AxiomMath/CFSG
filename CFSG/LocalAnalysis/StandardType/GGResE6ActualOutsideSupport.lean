module

public import CFSG.LocalAnalysis.StandardType.GGResE7LiteralReflectionSupport
public import CFSG.LocalAnalysis.StandardType.GGResE7LiteralModel
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGResE6Coordinates
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.Blueprint.Chevalley
public import CFSG.Assembly.E6FourCentMask
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Mathlib.Decide.Nodup
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Tactic
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13604
public import Certificates.Certificate13657
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate830101
public import CFSG.LocalAnalysis.StandardType.GGResE6ActualInsideSupport
public import CFSG.LocalAnalysis.StandardType.GGResE6ActualSevenRootSupport

public section

set_option maxRecDepth 10000
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open CFSG.StandardType.E6InsideSpanNormalizer
open scoped Matrix

lemma e6_beta_orthogonal_pair_cover (beta : Fin 6 → ZMod 3)
    (hbeta : beta ⬝ᵥ r ≠ 0) :
    (beta ⬝ᵥ rootVec ⟨5, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨58, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨5, by decide⟩)) (rootVec ⟨58, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨29, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨70, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨29, by decide⟩)) (rootVec ⟨70, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨18, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨52, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨18, by decide⟩)) (rootVec ⟨52, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨33, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨61, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨33, by decide⟩)) (rootVec ⟨61, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨9, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨25, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨9, by decide⟩)) (rootVec ⟨25, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨2, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨49, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨2, by decide⟩)) (rootVec ⟨49, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨11, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨44, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨11, by decide⟩)) (rootVec ⟨44, by decide⟩) = 0) ∨
    (beta ⬝ᵥ rootVec ⟨0, by decide⟩ ≠ 0 ∧
      beta ⬝ᵥ rootVec ⟨3, by decide⟩ ≠ 0 ∧
      e6dot (Cmul (rootVec ⟨0, by decide⟩)) (rootVec ⟨3, by decide⟩) = 0) := by
  revert beta
  decide +kernel

lemma e6_Bform_H_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hB : ∀ i, Bform (h i) = α i)
    (u : Fin 6 → ZMod 3) (w : V) :
    Bform (Fintype.linearCombination (ZMod 3) h u) w =
      e6dot u (fun i => Bform (h i) w) := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    e6dot]

lemma e6_Bform_H_H
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (u v : Fin 6 → ZMod 3) :
    Bform (Fintype.linearCombination (ZMod 3) h u)
        (Fintype.linearCombination (ZMod 3) h v) =
      e6dot u (Cmul v) := by
  have hC : C = cartanE6ModThree := by
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  rw [e6_Bform_H_apply hB u (Fintype.linearCombination (ZMod 3) h v)]
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    e6dot, Cmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hB i, hpair i j, hC]
  ring

lemma e6_reflection_isometry_of_self
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V)
    (hBsymm : ∀ u v, B u v = B v u)
    {a : V} (haa : B a a = 2) :
    ∀ u v, B (u - B a u • a) (v - B a v • a) = B u v := by
  intro u v
  rw [map_sub, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hBsymm u a]
  rw [haa]
  ring

lemma e6_rootRefl_isometry
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    (m : Fin 72) :
    ∀ u v, Bform (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m)) u)
      (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m)) v) = Bform u v := by
  intro u v
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  have hroot : Bform (H (rootVec m)) (H (rootVec m)) = 2 := by
    rw [e6_Bform_H_H hpair hB]
    exact norm_rootVec m
  have hlinR : ∀ x, ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m)) x =
      x - Bform (H (rootVec m)) x • H (rootVec m) := by
    intro x
    exact e6RootRefl_apply_full Bform h α hpair hB hlin hgenB hinv 0
      (rootPath m) (rootVec m) (rootVec_applyWord m) x
  rw [hlinR u, hlinR v]
  exact e6_reflection_isometry_of_self Bform hBsymm hroot u v

lemma e6_pair_action
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (w : V) (m1 m2 : Fin 72)
    (horth : Bform (Hcomb h (rootVec m1)) (Hcomb h (rootVec m2)) = 0) :
    ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w =
      w - Bform (Hcomb h (rootVec m1)) w • Hcomb h (rootVec m1)
        - Bform (Hcomb h (rootVec m2)) w • Hcomb h (rootVec m2) := by
  let v1 : V := Hcomb h (rootVec m1)
  let v2 : V := Hcomb h (rootVec m2)
  have hR1 : ∀ x, ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1)) x = x - Bform v1 x • v1 := by
    intro x
    exact e6RootRefl_apply_full Bform h α hpair hB hlin hgenB hinv 0
      (rootPath m1) (rootVec m1) (rootVec_applyWord m1) x
  have hR2 : ∀ x, ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m2)) x = x - Bform v2 x • v2 := by
    intro x
    exact e6RootRefl_apply_full Bform h α hpair hB hlin hgenB hinv 0
      (rootPath m2) (rootVec m2) (rootVec_applyWord m2) x
  calc
    ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w
        = ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1))
            (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m2)) w) := by
          rw [map_mul, LinearEquiv.mul_apply]
    _ = ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1)) (w - Bform v2 w • v2) := by rw [hR2]
    _ = (w - Bform v2 w • v2) - Bform v1 (w - Bform v2 w • v2) • v1 := by rw [hR1]
    _ = w - Bform v1 w • v1 - Bform v2 w • v2 := by
      rw [map_sub, map_smul, horth, smul_zero, sub_zero]
      module

lemma zmod3_sq_eq_one_of_ne_zero (b : ZMod 3) (hb : b ≠ 0) : b * b = 1 := by
  revert b
  decide +kernel

lemma e6_pair_isometry
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    (m1 m2 : Fin 72) :
    ∀ u v, Bform (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) u)
      (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) v) = Bform u v := by
  intro u v
  rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [e6_rootRefl_isometry Bform h α hpair hB hlin hgenB hinv hBsymm m1]
  rw [e6_rootRefl_isometry Bform h α hpair hB hlin hgenB hinv hBsymm m2]

lemma e6_pair_Bgww
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (w : V) (hww : Bform w w = 1)
    (m1 m2 : Fin 72)
    (horth : Bform (Hcomb h (rootVec m1)) (Hcomb h (rootVec m2)) = 0)
    (hb1 : Bform (Hcomb h (rootVec m1)) w ≠ 0)
    (hb2 : Bform (Hcomb h (rootVec m2)) w ≠ 0) :
    Bform (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w) w = 2 := by
  let v1 : V := Hcomb h (rootVec m1)
  let v2 : V := Hcomb h (rootVec m2)
  have h1 : Bform v1 w * Bform v1 w = 1 :=
    zmod3_sq_eq_one_of_ne_zero (Bform v1 w) hb1
  have h2 : Bform v2 w * Bform v2 w = 1 :=
    zmod3_sq_eq_one_of_ne_zero (Bform v2 w) hb2
  rw [e6_pair_action Bform h α hpair hB hlin hgenB hinv w m1 m2 horth]
  change Bform (w - Bform v1 w • v1 - Bform v2 w • v2) w = 2
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hww, h1, h2]
  decide

lemma e6_pair_Bha
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    (w : V) (hww : Bform w w = 1)
    (m1 m2 : Fin 72)
    (horth : Bform (Hcomb h (rootVec m1)) (Hcomb h (rootVec m2)) = 0)
    (hb1 : Bform (Hcomb h (rootVec m1)) w ≠ 0)
    (hb2 : Bform (Hcomb h (rootVec m2)) w ≠ 0) :
    Bform (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w)
      (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w) = 1 := by
  let g : MulAut ↥Bs := e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)
  have hiso : ∀ u v, Bform (ggLin (p := 3) ι g u) (ggLin (p := 3) ι g v) = Bform u v :=
    e6_pair_isometry Bform h α hpair hB hlin hgenB hinv hBsymm m1 m2
  have hgnorm : Bform (ggLin (p := 3) ι g w) (ggLin (p := 3) ι g w) = 1 := by
    rw [hiso, hww]
  have hBgww : Bform (ggLin (p := 3) ι g w) w = 2 :=
    e6_pair_Bgww Bform h α hpair hB hlin hgenB hinv w hww m1 m2 horth hb1 hb2
  change Bform (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w)
      (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w) = 1
  simp only [map_sub, LinearMap.sub_apply]
  rw [hgnorm, hBsymm w (ggLin (p := 3) ι
    (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w), hww, hBgww]
  decide

lemma e6HComb_add {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (u v : Fin 6 → ZMod 3) :
    Hcomb h (u + v) = Hcomb h u + Hcomb h v := by
  simp [Hcomb, Fintype.linearCombination_apply, Finset.sum_add_distrib, add_smul]

lemma e6HComb_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (a : ZMod 3) (u : Fin 6 → ZMod 3) :
    Hcomb h (a • u) = a • Hcomb h u := by
  simp [Hcomb, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]

lemma e6_pair_coords
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    (w : V) (hww : Bform w w = 1)
    (m1 m2 : Fin 72)
    (horth : Bform (Hcomb h (rootVec m1)) (Hcomb h (rootVec m2)) = 0)
    (hb1 : Bform (Hcomb h (rootVec m1)) w ≠ 0)
    (hb2 : Bform (Hcomb h (rootVec m2)) w ≠ 0) :
    ∃ s : Fin 6 → ZMod 3,
      Hcomb h s =
        ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w ∧
      norm s = 1 := by
  let v1 : V := Hcomb h (rootVec m1)
  let v2 : V := Hcomb h (rootVec m2)
  let b1 : ZMod 3 := Bform v1 w
  let b2 : ZMod 3 := Bform v2 w
  let s : Fin 6 → ZMod 3 := fun i => -b1 * rootVec m1 i - b2 * rootVec m2 i
  have hs : s = (-b1) • rootVec m1 + (-b2) • rootVec m2 := by
    funext i
    simp only [s, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcomb : Hcomb h s = -b1 • v1 - b2 • v2 := by
    rw [hs, e6HComb_add, e6HComb_smul, e6HComb_smul]
    simp [v1, v2]
    module
  refine ⟨s, ?_, ?_⟩
  · rw [hcomb]
    rw [e6_pair_action Bform h α hpair hB hlin hgenB hinv w m1 m2 horth]
    module
  · have hBha : Bform (ggLin (p := 3) ι
        (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w)
        (ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w) = 1 :=
      e6_pair_Bha Bform h α hpair hB hlin hgenB hinv hBsymm w hww m1 m2 horth hb1 hb2
    have hBHs : Bform (Hcomb h s) (Hcomb h s) = norm s := by
      change Bform (Fintype.linearCombination (ZMod 3) h s)
        (Fintype.linearCombination (ZMod 3) h s) = norm s
      rw [e6_Bform_H_H hpair hB]
      rfl
    rw [← hBHs, hcomb]
    have hneg : -b1 • v1 - b2 • v2 =
        ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m1) * e6RootRefl φL 0 (rootPath m2)) w - w := by
      rw [e6_pair_action Bform h α hpair hB hlin hgenB hinv w m1 m2 horth]
      module
    rw [hneg]
    exact hBha

lemma e6_Bform_root_w_ne_zero
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hB : ∀ i, Bform (h i) = α i)
    (u : Fin 6 → ZMod 3) (w : V)
    (hval : e6dot (fun i => Bform (h i) w) u ≠ 0) :
    Bform (Hcomb h u) w ≠ 0 := by
  rw [Hcomb, e6_Bform_H_apply hB]
  rwa [e6dot_comm]

lemma e6_Bform_root_root_eq_zero
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (u v : Fin 6 → ZMod 3)
    (hval : e6dot (Cmul u) v = 0) :
    Bform (Hcomb h u) (Hcomb h v) = 0 := by
  rw [Hcomb, Hcomb, e6_Bform_H_H hpair hB, e6dot_comm, ← e6dot_Cmul_swap]
  exact hval

lemma e6_beta_pair_exists
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (w : V)
    (hbeta : (fun i => Bform (h i) w) ⬝ᵥ r ≠ 0) :
    ∃ m1 m2 : Fin 72,
      Bform (Hcomb h (rootVec m1)) (Hcomb h (rootVec m2)) = 0 ∧
      Bform (Hcomb h (rootVec m1)) w ≠ 0 ∧
      Bform (Hcomb h (rootVec m2)) w ≠ 0 := by
  let beta : Fin 6 → ZMod 3 := fun i => Bform (h i) w
  have hbeta' : beta ⬝ᵥ r ≠ 0 := hbeta
  rcases e6_beta_orthogonal_pair_cover beta hbeta' with
    ⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩ |
    ⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩
  · refine ⟨⟨5, by decide⟩, ⟨58, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨29, by decide⟩, ⟨70, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨18, by decide⟩, ⟨52, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨33, by decide⟩, ⟨61, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨9, by decide⟩, ⟨25, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨2, by decide⟩, ⟨49, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨11, by decide⟩, ⟨44, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)
  · refine ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ?_, ?_, ?_⟩
    · exact e6_Bform_root_root_eq_zero hpair hB _ _ ho
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h1)
    · exact e6_Bform_root_w_ne_zero hB _ w (by simpa [e6dot, dotProduct] using h2)

lemma e6_reflection_inv_eq_self
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {F : MulAut ↥Bs} {aa : Module.Dual (ZMod 3) V} {w : V}
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2) :
    F⁻¹ = F := by
  apply inv_eq_of_mul_eq_one_right
  apply ggLin_injective (p := 3) ι
  ext v
  rw [map_mul, LinearEquiv.mul_apply]
  have h2 : ggLin (p := 3) ι F (ggLin (p := 3) ι F v) = v := by
    rw [hFlin, hFlin, map_sub, map_smul, hself]
    module
  rw [h2]
  have hone : ggLin (p := 3) ι (1 : MulAut ↥Bs) = 1 := map_one _
  rw [hone]
  rfl

lemma e6_conj_reflection_apply
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {F : MulAut ↥Bs} {aa : Module.Dual (ZMod 3) V} {w : V}
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hU : MulAut ↥Bs) :
    ∀ v, ggLin (p := 3) ι (hU * F * hU⁻¹) v =
      v - (aa.comp ((ggLin (p := 3) ι hU).symm : V →ₗ[ZMod 3] V)) v •
        ggLin (p := 3) ι hU w := by
  intro v
  rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hinv : (ggLin (p := 3) ι hU)⁻¹ v = (ggLin (p := 3) ι hU).symm v := rfl
  rw [hinv, hFlin]
  simp [map_sub, map_smul]

lemma e6_norm1_conj_coroot
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V)
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    (F : MulAut ↥Bs) (aa : Module.Dual (ZMod 3) V) (w : V)
    (g : MulAut ↥Bs) (s : Fin 6 → ZMod 3)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (haa : ∀ v, aa v = 2 * Bform w v)
    (hBgww : Bform (ggLin (p := 3) ι g w) w = 2)
    (hha : Hcomb h s = ggLin (p := 3) ι g w - w) :
    ggLin (p := 3) ι (F * g) w = Hcomb h s := by
  rw [map_mul, LinearEquiv.mul_apply, hFlin]
  have hA : aa (ggLin (p := 3) ι g w) = 1 := by
    rw [haa, hBsymm w (ggLin (p := 3) ι g w), hBgww]
    decide
  rw [hA]
  simpa [hha]

lemma e6_norm1_conj_restriction
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    (F : MulAut ↥Bs) (aa : Module.Dual (ZMod 3) V) (w : V)
    (g : MulAut ↥Bs) (s : Fin 6 → ZMod 3)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2)
    (haa : ∀ v, aa v = 2 * Bform w v)
    (hgiso : ∀ u v, Bform (ggLin (p := 3) ι g u) (ggLin (p := 3) ι g v) = Bform u v)
    (hBgww : Bform (ggLin (p := 3) ι g w) w = 2)
    (hha : Hcomb h s = ggLin (p := 3) ι g w - w) :
    ∀ u, (aa.comp ((ggLin (p := 3) ι (F * g)).symm : V →ₗ[ZMod 3] V))
        (Hcomb h u) = 2 * e6dot (Cmul s) u := by
  intro u
  have hFinv : F⁻¹ = F := e6_reflection_inv_eq_self hFlin hself
  let v : V := Hcomb h u
  have hInvApply : (ggLin (p := 3) ι (F * g)).symm v =
      ggLin (p := 3) ι g⁻¹ (ggLin (p := 3) ι F v) := by
    change ((ggLin (p := 3) ι (F * g))⁻¹) v =
      ggLin (p := 3) ι g⁻¹ (ggLin (p := 3) ι F v)
    rw [← map_inv]
    rw [show (F * g)⁻¹ = g⁻¹ * F by simp [hFinv, mul_assoc]]
    rw [map_mul, LinearEquiv.mul_apply]
  change aa ((ggLin (p := 3) ι (F * g)).symm v) = 2 * e6dot (Cmul s) u
  rw [hInvApply, hFlin v]
  rw [map_sub, map_smul]
  have h1 : aa (ggLin (p := 3) ι g⁻¹ v) = 2 * Bform (ggLin (p := 3) ι g w) v := by
    rw [haa]
    congr 1
    have his := hgiso w (ggLin (p := 3) ι g⁻¹ v)
    rw [← his]
    simp
  have h2 : aa v = 2 * Bform w v := haa v
  have h3 : aa (ggLin (p := 3) ι g⁻¹ w) = 1 := by
    rw [haa]
    have his := hgiso w (ggLin (p := 3) ι g⁻¹ w)
    rw [← his]
    simp [hBgww]
    decide
  rw [map_sub, map_smul]
  rw [h1, h2, h3]
  simp only [smul_eq_mul, mul_one]
  have hdiff : Bform (ggLin (p := 3) ι g w) v - Bform w v =
      Bform (Hcomb h s) v := by
    calc
      Bform (ggLin (p := 3) ι g w) v - Bform w v =
          Bform (ggLin (p := 3) ι g w - w) v := by
            rw [map_sub, LinearMap.sub_apply]
      _ = Bform (Hcomb h s) v := by rw [← hha]
  have hBdot : Bform (Hcomb h s) v = e6dot (Cmul s) u := by
    change Bform (Fintype.linearCombination (ZMod 3) h s)
      (Fintype.linearCombination (ZMod 3) h u) = e6dot (Cmul s) u
    rw [e6_Bform_H_H hpair hB, e6dot_comm, ← e6dot_Cmul_swap]
  have htwo : 2 * Bform (ggLin (p := 3) ι g w) v - 2 * Bform w v =
      2 * (Bform (ggLin (p := 3) ι g w) v - Bform w v) := by ring
  rw [htwo, hdiff, hBdot]

lemma e6HComb_neg {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (u : Fin 6 → ZMod 3) :
    Hcomb h (-u) = -Hcomb h u := by
  rw [show -u = (-1 : ZMod 3) • u by simp, e6HComb_smul]
  simp

lemma e6HComb_sub {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (u v : Fin 6 → ZMod 3) :
    Hcomb h (u - v) = Hcomb h u - Hcomb h v := by
  rw [sub_eq_add_neg, e6HComb_add, e6HComb_neg]
  abel

lemma e6HComb_sub_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (u : Fin 6 → ZMod 3) (c : ZMod 3) (v : Fin 6 → ZMod 3) :
    Hcomb h (u - c • v) = Hcomb h u - c • Hcomb h v := by
  rw [e6HComb_sub, e6HComb_smul]

lemma zmod3_two_mul_eq_two (x : ZMod 3) (h : 2 * x = 2) : x = 1 := by
  revert x
  decide +kernel

theorem e6_actual_norm1_outside_false
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {φL : Fin 6 → MulAut ↥Bs}
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    {F : MulAut ↥Bs} {w : V} {aa : Module.Dual (ZMod 3) V}
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2)
    (haa : ∀ v, aa v = 2 * Bform w v)
    (hbeta : (fun i => Bform (h i) w) ⬝ᵥ r ≠ 0)
    {lam : ZMod 3}
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r) :
    False := by
  classical
  have hww : Bform w w = 1 := by
    apply zmod3_two_mul_eq_two
    have h := hself
    rwa [haa w] at h
  obtain ⟨m1, m2, horth, hb1, hb2⟩ :=
    e6_beta_pair_exists hpair hB w hbeta
  let R1 : MulAut ↥Bs := e6RootRefl φL 0 (rootPath m1)
  let R2 : MulAut ↥Bs := e6RootRefl φL 0 (rootPath m2)
  let g : MulAut ↥Bs := R1 * R2
  have hgmem : g ∈ ggAutomizer L Bs := by
    dsimp [g, R1, R2]
    exact mul_mem (e6RootRefl_mem hgenL 0 (rootPath m1))
      (e6RootRefl_mem hgenL 0 (rootPath m2))
  have hgjoin : g ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    Subgroup.mem_sup_left hgmem
  obtain ⟨s, hha, hnorm⟩ :=
    e6_pair_coords Bform h α hpair hB hlin hgenB hinv hBsymm w hww m1 m2 horth hb1 hb2
  have hgiso : ∀ u v,
      Bform (ggLin (p := 3) ι g u) (ggLin (p := 3) ι g v) = Bform u v := by
    dsimp [g, R1, R2]
    exact e6_pair_isometry Bform h α hpair hB hlin hgenB hinv hBsymm m1 m2
  have hBgww : Bform (ggLin (p := 3) ι g w) w = 2 := by
    dsimp [g, R1, R2]
    exact e6_pair_Bgww Bform h α hpair hB hlin hgenB hinv w hww m1 m2 horth hb1 hb2
  let hU : MulAut ↥Bs := F * g
  have hUjoin : hU ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := mul_mem hF hgjoin
  let Fnew : MulAut ↥Bs := hU * F * hU⁻¹
  have hFnewjoin : Fnew ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    dsimp [Fnew]
    exact mul_mem (mul_mem hUjoin hF) (inv_mem hUjoin)
  let aa_new : Module.Dual (ZMod 3) V :=
    aa.comp ((ggLin (p := 3) ι hU).symm : V →ₗ[ZMod 3] V)
  have hFnewlin : ∀ v,
      ggLin (p := 3) ι Fnew v = v - aa_new v • ggLin (p := 3) ι hU w := by
    dsimp [Fnew, aa_new]
    exact e6_conj_reflection_apply hFlin hU
  have hha_new : ggLin (p := 3) ι hU w = Hcomb h s := by
    dsimp [hU, g, R1, R2]
    exact e6_norm1_conj_coroot Bform h hBsymm F aa w g s hFlin haa hBgww hha
  have hha_newF : ggLin (p := 3) ι hU w =
      Fintype.linearCombination (ZMod 3) h s := by
    simpa only [Hcomb] using hha_new
  have hres : ∀ u : Fin 6 → ZMod 3,
      aa_new (Hcomb h u) = 2 * e6dot (Cmul s) u := by
    intro u
    exact e6_norm1_conj_restriction Bform h α hpair hB hBsymm F aa w g s
      hFlin hself haa hgiso hBgww hha u
  have hresF : ∀ u : Fin 6 → ZMod 3,
      aa_new (Fintype.linearCombination (ZMod 3) h u) =
        2 * e6dot (Cmul s) u := by
    intro u
    simpa only [Hcomb] using hres u
  have hself_new : aa_new (ggLin (p := 3) ι hU w) = 2 := by
    rw [hha_newF]
    rw [hresF s, e6dot_Cmul_self, hnorm]
    decide
  have hFnewA : Fnew ∈ ggAutomizer L Bs :=
    e6_actual_insideU_membership_original hH hx hLNoncyclic hLI hpair hB hlin hgenB hinv
      hgenL hclosL hFnewjoin hFnewlin hself_new hha_newF hxvec hresF
  have hconj : ∀ i j : Fin 6, ∃ m : Fin 72,
      ggLin (p := 3) ι (Fnew * φL i * Fnew⁻¹)
        (Fintype.linearCombination (ZMod 3) h (unitRoot j)) =
        Fintype.linearCombination (ZMod 3) h (rootVec m) := by
    intro i j
    have hmem : Fnew * φL i * Fnew⁻¹ ∈ ggAutomizer L Bs :=
      mul_mem (mul_mem hFnewA (hgenL i)) (inv_mem hFnewA)
    obtain ⟨m0, hm0⟩ := unitRoot_mem_rootVec j
    obtain ⟨m1', hm1'⟩ :=
      e6_AL_preserves_rootVec hpair hlin hinv hclosL hmem m0
    refine ⟨m1', ?_⟩
    rw [← hm0]
    exact hm1'
  have hFrestrict : ∀ u : Fin 6 → ZMod 3,
      ggLin (p := 3) ι Fnew (Fintype.linearCombination (ZMod 3) h u) =
        Fintype.linearCombination (ZMod 3) h (refl s u) := by
    intro u
    rw [hFnewlin, hha_newF, hresF u]
    rw [refl_apply]
    rw [show (2 : ZMod 3) * (norm s)⁻¹ = 2 by rw [hnorm]; decide +kernel]
    change Fintype.linearCombination (ZMod 3) h u -
        (2 * (∑ i, Cmul s i * u i)) • Fintype.linearCombination (ZMod 3) h s =
      Hcomb h (u - (2 * (∑ i, Cmul s i * u i)) • s)
    rw [e6HComb_sub_smul]
    simp only [Hcomb]
  have hnorm_ne : norm s ≠ 0 := by
    rw [hnorm]
    decide
  obtain ⟨m, hm⟩ :=
    e6_actual_literal_axis_of_finite_test
      (V := V) (ι := ι) (h := h) (α := α) (φL := φL)
      (F := Fnew) (ha := ggLin (p := 3) ι hU w) (aa := aa_new) (w := s)
      (hLI := hLI) (hpair := hpair) (hlin := hlin) (hha := hha_newF)
      (hnorm := hnorm_ne) (hFlin := hFnewlin) (hselfF := hself_new)
      (hFrestrict := hFrestrict) (hconj := hconj)
  have hm_e6 : Hcomb h (rootVec m) = Hcomb h s := by
    calc
      Hcomb h (rootVec m) = ggLin (p := 3) ι hU w := hm
      _ = Hcomb h s := hha_newF
  have hBha : Bform (Hcomb h s) (Hcomb h s) = 1 := by
    rw [Hcomb, e6_Bform_H_H hpair hB, e6dot_comm, e6dot_Cmul_self, hnorm]
  have hBroot : Bform (Hcomb h (rootVec m)) (Hcomb h (rootVec m)) = 2 := by
    rw [Hcomb, e6_Bform_H_H hpair hB, e6dot_comm, e6dot_Cmul_self]
    exact norm_rootVec m
  rw [hm_e6] at hBroot
  rw [hBha] at hBroot
  exact (by decide : (1 : ZMod 3) ≠ 2) hBroot
end E6Seven
end CFSG.StandardType
end

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module CFSG.StandardType.E6NormWordOrbit CFSG.StandardType.E6QTwo
open scoped Matrix

theorem e6_actual_outside_scale_eq_one_of_norm1_exclusion
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {φL : Fin 6 → MulAut ↥Bs}
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hBsymm : ∀ u v, Bform u v = Bform v u)
    {F : MulAut ↥Bs} {w : V} {aa : Module.Dual (ZMod 3) V}
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2)
    {mu : ZMod 3} (hmu : mu ≠ 0)
    (haa : ∀ v, aa v = mu * Bform w v)
    (hbeta : (fun i => Bform (h i) w) ⬝ᵥ r ≠ 0)
    {lam : ZMod 3}
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r) :
    mu = 1 ∧ Bform w w = 2 ∧
      (∀ v, aa v = Bform w v) ∧
      (∀ v, ggLin (p := 3) ι F v = v - Bform w v • w) ∧
      (∀ u v, Bform (ggLin (p := 3) ι F u) (ggLin (p := 3) ι F v) = Bform u v) := by
  classical
  have hself_mu : mu * Bform w w = 2 := by
    rw [← haa w]
    exact hself
  have hmu2 : mu ≠ 2 := by
    intro hm
    have hww : Bform w w = 1 := by
      have heq : (2 : ZMod 3) * Bform w w = 2 * 1 := by
        simpa only [hm, mul_one] using hself_mu
      exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) heq
    have haa2 : ∀ v, aa v = 2 * Bform w v := by
      intro v
      simpa only [hm] using haa v
    exact e6_actual_norm1_outside_false hH hx hLNoncyclic hLI hpair hB hlin hgenB hinv
      hgenL hclosL hBsymm hF hFlin hself haa2 hbeta hxvec
  have hmu1 : mu = 1 := by
    have ht : ∀ a : ZMod 3, a ≠ 0 → a ≠ 2 → a = 1 := by decide +kernel
    exact ht mu hmu hmu2
  have hww2 : Bform w w = 2 := by
    simpa only [hmu1, one_mul] using hself_mu
  have hfull : ∀ v, aa v = Bform w v := by
    intro v
    simpa only [hmu1, one_mul] using haa v
  have haction : ∀ v, ggLin (p := 3) ι F v = v - Bform w v • w := by
    intro v
    rw [hFlin, hfull]
  refine ⟨hmu1, hww2, hfull, haction, ?_⟩
  intro u v
  rw [haction u, haction v]
  exact e6_reflection_isometry_of_self Bform hBsymm hww2 u v

end CFSG.StandardType.E6Seven

public section
namespace CFSG.StandardType.E6Seven
open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

@[expose] def outsideCoords (s : Fin 6 → ZMod 3) (k : ZMod 3) : Fin 7 → ZMod 3 :=
  (∑ i : Fin 6, s i • Pi.single i.castSucc 1) + k • Pi.single (Fin.last 6) 1

theorem outside_form_choice_of_eval
    (C : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (c s : Fin 6 → ZMod 3) (k b : ZMod 3)
    (a : (Fin 7 → ZMod 3) →ₗ[ZMod 3] ZMod 3)
    (mu : ZMod 3)
    (h_ei : ∀ i : Fin 6, a (Pi.single i.castSucc 1) =
      mu * B7 C c b (outsideCoords s k) (Pi.single i.castSucc 1))
    (h_e6 : a (Pi.single (Fin.last 6) 1) =
      mu * B7 C c b (outsideCoords s k) (Pi.single (Fin.last 6) 1)) :
    a = mu • (B7 C c b (outsideCoords s k)) := by
  let Bb : (Fin 7 → ZMod 3) →ₗ[ZMod 3] ZMod 3 := B7 C c b (outsideCoords s k)
  have h_ei' : ∀ i : Fin 6, a (Pi.single i.castSucc 1) =
      mu * Bb (Pi.single i.castSucc 1) := h_ei
  have h_e6' : a (Pi.single (Fin.last 6) 1) =
      mu * Bb (Pi.single (Fin.last 6) 1) := h_e6
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i : Fin 7, v i • Pi.single i (1 : ZMod 3) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum, map_sum]
  conv_lhs => rw [Fin.sum_univ_castSucc]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [map_smul, smul_eq_mul, h_ei', h_e6', Bb, LinearMap.smul_apply]

theorem not_mem_span_of_chart_last
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (z : V) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (hchart_h : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (hchart_z : chart z = Pi.single (Fin.last 6) 1) :
    z ∉ Submodule.span (ZMod 3) (Set.range h) := by
  intro hzmem
  have hmem : chart z ∈ Submodule.span (ZMod 3)
      (Set.range fun i : Fin 6 => chart (h i)) := by
    have h1 : chart z ∈ Submodule.map chart.toLinearMap
        (Submodule.span (ZMod 3) (Set.range h)) :=
      Submodule.mem_map_of_mem (f := chart.toLinearMap) hzmem
    rw [Submodule.map_span] at h1
    have hset : chart.toLinearMap '' Set.range h =
        Set.range (fun i : Fin 6 => chart (h i)) := by
      ext v
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨h i, ⟨i, rfl⟩, rfl⟩
    rwa [hset] at h1
  rw [show (fun i : Fin 6 => chart (h i)) =
      (fun i : Fin 6 => Pi.single i.castSucc 1) from funext hchart_h] at hmem
  rw [hchart_z] at hmem
  let f : (Fin 7 → ZMod 3) →ₗ[ZMod 3] ZMod 3 := LinearMap.proj (Fin.last 6)
  have hf0 : ∀ i : Fin 6, f (Pi.single i.castSucc 1) = 0 := by
    intro i
    have hne : (i.castSucc : Fin 7) ≠ Fin.last 6 := i.castSucc_lt_last.ne
    change (Pi.single i.castSucc (1 : ZMod 3) : Fin 7 → ZMod 3) (Fin.last 6) = 0
    rw [Pi.single_eq_of_ne hne.symm]
  have hf6 : f (Pi.single (Fin.last 6) 1) = 1 := by simp [f]
  have hzero : f (Pi.single (Fin.last 6) 1) = 0 := by
    refine Submodule.span_induction (p := fun v _ => f v = 0) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨i, rfl⟩
      exact hf0 i
    · simp
    · intro a b _ _ ha hb
      simp [map_add, ha, hb]
    · intro a b _ hb
      simp [map_smul, hb]
  rw [hf6] at hzero
  exact one_ne_zero hzero

theorem c_dot_kernelVec_ne_zero_of_commonKernel_le_line
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (hLI : LinearIndependent (ZMod 3) h)
    (z : V) (hz : z ∉ Submodule.span (ZMod 3) (Set.range h))
    (α : Fin 6 → Module.Dual (ZMod 3) V)
    (c : Fin 6 → ZMod 3)
    (hzc : ∀ i, α i z = c i)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (x : V) (hfix : ∀ w, (∀ i, α i w = 0) → ∃ lam : ZMod 3, w = lam • x) :
    c ⬝ᵥ cartanE6KernelVec ≠ 0 := by
  intro hc
  let r : Fin 6 → ZMod 3 := cartanE6KernelVec
  let wr : V := Fintype.linearCombination (ZMod 3) h r
  have hwr_kill : ∀ i, α i wr = 0 := by
    intro i
    change α i (Fintype.linearCombination (ZMod 3) h r) = 0
    rw [apply_linearCombination_eq_cartanE6ModThree (h := h) (α := α) hpair i r]
    exact congr_fun cartanE6ModThree_mulVec_cartanE6KernelVec i
  have hwr_ne : wr ≠ 0 := by
    intro h0
    have hcoeff : r = 0 :=
      hLI.fintypeLinearCombination_injective (by simpa [wr] using h0)
    exact cartanE6KernelVec_ne_zero hcoeff
  obtain ⟨lr, hwr_eq⟩ := hfix wr hwr_kill
  have hlr_ne : lr ≠ 0 := by
    intro h0
    exact hwr_ne (by rw [hwr_eq, h0, zero_smul])
  have hC : E6NormWordOrbit.C = cartanE6ModThree := by
    rw [E6NormWordOrbit.C_eq_mathlib]
    rfl
  have hr : E6NormWordOrbit.r = cartanE6KernelVec := rfl
  obtain ⟨u, hu⟩ := E6NormWordOrbit.exists_mulVec_eq_of_dot_radical_eq_zero c
    (by simpa only [hr] using hc)
  rw [hC] at hu
  let w : V := Fintype.linearCombination (ZMod 3) h u + z
  have hw_kill : ∀ i, α i w = 0 := by
    intro i
    change α i (Fintype.linearCombination (ZMod 3) h u + z) = 0
    rw [map_add, apply_linearCombination_eq_cartanE6ModThree (h := h) (α := α) hpair i u,
      hzc i]
    have h := congr_fun hu i
    rw [Matrix.mulVec, dotProduct] at h
    rw [Matrix.mulVec, dotProduct]
    rw [h]
    change -(c i) + c i = 0
    exact neg_add_cancel (c i)
  obtain ⟨lw, hw_eq⟩ := hfix w hw_kill
  let μ : ZMod 3 := lw * lr⁻¹
  have hw_mu : w = μ • wr := by
    change w = (lw * lr⁻¹) • wr
    rw [hw_eq, hwr_eq, smul_smul]
    congr 1
    field_simp [hlr_ne]
  have hzero : w - μ • wr = 0 := sub_eq_zero.mpr hw_mu
  have hexp : w - μ • wr =
      Fintype.linearCombination (ZMod 3) h (u - μ • r) + z := by
    simp [w, wr, Fintype.linearCombination_apply, Finset.sum_sub_distrib, Finset.smul_sum,
      sub_smul, smul_sub, mul_smul]
    abel
  have hz_eq : z = -Fintype.linearCombination (ZMod 3) h (u - μ • r) := by
    rw [hexp] at hzero
    rw [add_comm] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  apply hz
  rw [hz_eq]
  refine Submodule.neg_mem _ ?_
  rw [← Fintype.range_linearCombination (R := ZMod 3) (v := h)]
  exact LinearMap.mem_range_self _ _

end CFSG.StandardType.E6Seven
end

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

theorem eq_outsideCoords (x : Fin 7 → ZMod 3) :
    x = outsideCoords (fun i => x i.castSucc) (x (Fin.last 6)) := by
  have hx : x = ∑ i : Fin 7, x i • Pi.single i (1 : ZMod 3) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  conv_lhs => rw [Fin.sum_univ_castSucc]
  rfl

theorem chart_last_ne_zero_of_not_mem_span
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h' : Fin 6 → V) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (hchart_h : ∀ i, chart (h' i) = Pi.single i.castSucc 1)
    (w : V) (hw : w ∉ Submodule.span (ZMod 3) (Set.range h')) :
    chart w (Fin.last 6) ≠ 0 := by
  intro hk
  apply hw
  have hcoords : chart w =
      ∑ i : Fin 6, (chart w i.castSucc) • Pi.single i.castSucc 1 := by
    have hx : chart w = ∑ i : Fin 7, (chart w i) • Pi.single i (1 : ZMod 3) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    conv_lhs => rw [Fin.sum_univ_castSucc]
    simp [Pi.single_apply]
    simpa using hk
  have hw' : w = ∑ i : Fin 6, (chart w i.castSucc) • h' i := by
    calc
      w = chart.symm (chart w) := (chart.symm_apply_apply w).symm
      _ = chart.symm (∑ i : Fin 6, (chart w i.castSucc) • Pi.single i.castSucc 1) := by
        exact congrArg chart.symm hcoords
      _ = ∑ i : Fin 6, (chart w i.castSucc) • h' i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        congr 1
        rw [← hchart_h i, chart.symm_apply_apply]
  rw [hw']
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

end E6Seven
end CFSG.StandardType

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

theorem e6_restriction_nonzero_sameWitness
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (rootRefl : Fin 72 → MulAut ↥Bs)
    (hRootMem : ∀ m, rootRefl m ∈ ggAutomizer L Bs)
    (hRootAction : ∀ m v, ggLin (p := 3) ι (rootRefl m) v =
      v - Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) v •
        Fintype.linearCombination (ZMod 3) h (rootVec m))
    (hRootSelf : ∀ m, Bform (Fintype.linearCombination (ZMod 3) h (rootVec m))
      (Fintype.linearCombination (ZMod 3) h (rootVec m)) = 2)
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2)
    (hspan : ∃ u : Fin 6 → ZMod 3,
      Bform (Fintype.linearCombination (ZMod 3) h u) w ≠ 0) :
    ∃ mu : ZMod 3, mu ≠ 0 ∧ ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) =
        mu * Bform (Fintype.linearCombination (ZMod 3) h u) w := by
  obtain ⟨mu, hres⟩ := e6_restriction_proportional_sameWitness
    hH ι h α Bform rootRefl hRootMem hRootAction hRootSelf F w aa hF hFlin hself
  refine ⟨mu, ?_, hres⟩
  intro hzero
  have haa : ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) = 0 := by
    intro u
    rw [hres u, hzero, zero_mul]
  have hroots : ∀ m : Fin 72,
      Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) w = 0 := by
    intro m
    exact (e6_actual_cross_zero_iff hH ι hF
      ((show ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs from le_sup_left)
        (hRootMem m)) hFlin (hRootAction m) hself (hRootSelf m)).mp
      (haa (rootVec m))
  have hbase : ∀ i : Fin 6, Bform (h i) w = 0 := by
    intro i
    obtain ⟨m, hm⟩ := CFSG.StandardType.unitRoot_mem_rootVec i
    have hroot := hroots m
    simpa only [hm, unitRoot, Fintype.linearCombination_apply_single, one_smul] using hroot
  obtain ⟨u, hu⟩ := hspan
  apply hu
  simp [Fintype.linearCombination_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, hbase]

theorem outside_coordinate_pair_ne_zero (c s : Fin 6 → ZMod 3) (k : ZMod 3)
    (hk : k ≠ 0) (hc : c ⬝ᵥ r ≠ 0) :
    (Cmul s + k • c) ⬝ᵥ r ≠ 0 := by
  have hzero : Cmul s ⬝ᵥ r = 0 := by
    change e6dot (Cmul s) r = 0
    rw [e6dot_Cmul_swap s r, Cmul_r]
    simp [e6dot]
  rw [add_dotProduct, smul_dotProduct, hzero, zero_add, smul_eq_mul]
  exact mul_ne_zero hk hc

end CFSG.StandardType.E6Seven

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

theorem outside_B7_castSucc (c s : Fin 6 → ZMod 3) (k b : ZMod 3) (i : Fin 6) :
    B7 cartanE6ModThree c b (outsideCoords s k) (Pi.single i.castSucc 1) =
      (cartanE6ModThree *ᵥ s + k • c) i := by
  have hlast : B7 cartanE6ModThree c b (Pi.single (Fin.last 6) 1)
      (Pi.single i.castSucc 1) = c i := by
    rw [(B7_isSymm cartanE6ModThree c b (by
      ext u v; exact cartanE6ModThree_symm v u)).eq]
    rw [B7_single_single, gram7_castSucc_last]
  have hsix : ∀ j : Fin 6, B7 cartanE6ModThree c b (Pi.single j.castSucc 1)
      (Pi.single i.castSucc 1) = cartanE6ModThree j i := by
    intro j
    rw [B7_single_single, gram7_castSucc_castSucc]
  have hsum : (∑ j : Fin 6, s j * cartanE6ModThree j i) =
      (cartanE6ModThree *ᵥ s) i := by
    change (∑ j : Fin 6, s j * cartanE6ModThree j i) =
      ∑ j : Fin 6, cartanE6ModThree i j * s j
    apply Finset.sum_congr rfl
    intro j _
    rw [cartanE6ModThree_symm j i, mul_comm]
  simp only [outsideCoords, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hsix, hlast]
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    congrArg (fun t : ZMod 3 => t + k * c i) hsum

theorem outside_B7_last (c s : Fin 6 → ZMod 3) (k b : ZMod 3) :
    B7 cartanE6ModThree c b (outsideCoords s k) (Pi.single (Fin.last 6) 1) =
      c ⬝ᵥ s + k * b := by
  have hsix : ∀ j : Fin 6, B7 cartanE6ModThree c b (Pi.single j.castSucc 1)
      (Pi.single (Fin.last 6) 1) = c j := by
    intro j
    rw [B7_single_single, gram7_castSucc_last]
  have hlast : B7 cartanE6ModThree c b (Pi.single (Fin.last 6) 1)
      (Pi.single (Fin.last 6) 1) = b := by
    rw [B7_single_single, gram7_last_last]
  have hsum : (∑ j : Fin 6, s j * c j) = c ⬝ᵥ s := by
    change (∑ j : Fin 6, s j * c j) = ∑ j : Fin 6, c j * s j
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  simp only [outsideCoords, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hsix, hlast]
  exact congrArg (fun t : ZMod 3 => t + k * b) hsum

theorem outside_exists_form (c s : Fin 6 → ZMod 3) (k : ZMod 3)
    (a : Module.Dual (ZMod 3) (Fin 7 → ZMod 3)) (mu : ZMod 3)
    (hk : k ≠ 0) (hmu : mu ≠ 0)
    (hfirst : ∀ i : Fin 6, a (Pi.single i.castSucc 1) =
      mu * B7 cartanE6ModThree c 0 (outsideCoords s k) (Pi.single i.castSucc 1)) :
    ∃ b : ZMod 3, a = mu • B7 cartanE6ModThree c b (outsideCoords s k) := by
  let b := (a (Pi.single (Fin.last 6) 1) / mu - c ⬝ᵥ s) / k
  refine ⟨b, outside_form_choice_of_eval cartanE6ModThree c s k b a mu ?_ ?_⟩
  · intro i
    rw [hfirst i, outside_B7_castSucc, outside_B7_castSucc]
  · rw [outside_B7_last]
    dsimp [b]
    field_simp
    <;> ring

end CFSG.StandardType.E6Seven

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

theorem e6_outside_actual_form_sameWitness
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (rootRefl : Fin 72 → MulAut ↥Bs)
    (hRootMem : ∀ m, rootRefl m ∈ ggAutomizer L Bs)
    (hRootAction : ∀ m v, ggLin (p := 3) ι (rootRefl m) v =
      v - Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) v •
        Fintype.linearCombination (ZMod 3) h (rootVec m))
    (hRootSelf : ∀ m, Bform (Fintype.linearCombination (ZMod 3) h (rootVec m))
      (Fintype.linearCombination (ZMod 3) h (rootVec m)) = 2)
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2)
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (c : Fin 6 → ZMod 3)
    (hchart_h : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (hform_h : ∀ i, Bform (h i) = α i)
    (hBform : Bform = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap)
    (s : Fin 6 → ZMod 3) (k : ZMod 3)
    (hchart_w : chart w = outsideCoords s k) (hk : k ≠ 0)
    (hc : c ⬝ᵥ cartanE6KernelVec ≠ 0) :
    ∃ (b : ZMod 3) (mu : ZMod 3),
      mu ≠ 0 ∧
      (∀ v, aa v = mu * B7 cartanE6ModThree c b (outsideCoords s k) (chart v)) ∧
      (∀ v, ggLin (p := 3) ι F v = v -
        (mu * B7 cartanE6ModThree c b (outsideCoords s k) (chart v)) • w) := by
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  let beta : Fin 6 → ZMod 3 := fun i => Bform (h i) w
  have hC_symm : cartanE6ModThree.IsSymm := by
    ext i j
    exact (cartanE6ModThree_symm i j).symm
  have hB7_symm : (B7 cartanE6ModThree c 0).IsSymm :=
    B7_isSymm cartanE6ModThree c 0 hC_symm
  have hUnit : ∀ i : Fin 6, H (unitRoot i) = h i := by
    intro i
    change Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i
    rw [unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hCmul : Cmul s = cartanE6ModThree *ᵥ s := by
    rw [Cmul_eq_mulVec]
    congr 1
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  have hbeta_eq : beta = Cmul s + k • c := by
    funext i
    change Bform (h i) w = (Cmul s + k • c) i
    rw [hBform]
    change B7 cartanE6ModThree c 0 (chart (h i)) (chart w) =
      (Cmul s + k • c) i
    rw [hchart_h i, hchart_w, hB7_symm.eq, hCmul]
    exact outside_B7_castSucc c s k 0 i
  have hbeta_ne : beta ⬝ᵥ cartanE6KernelVec ≠ 0 := by
    rw [hbeta_eq]
    exact outside_coordinate_pair_ne_zero c s k hk hc
  have hBlin : ∀ u : Fin 6 → ZMod 3, Bform (H u) w = e6Eval beta u := by
    intro u
    change Bform (Fintype.linearCombination (ZMod 3) h u) w = e6Eval beta u
    rw [Fintype.linearCombination_apply, map_sum, e6Eval]
    rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  have hspan : ∃ u : Fin 6 → ZMod 3, Bform (H u) w ≠ 0 := by
    refine ⟨cartanE6KernelVec, ?_⟩
    rw [hBlin]
    simpa [e6Eval, dotProduct] using hbeta_ne
  obtain ⟨mu, hmu, hres⟩ := e6_restriction_nonzero_sameWitness
    hH ι h α Bform rootRefl hRootMem hRootAction hRootSelf F w aa hF hFlin hself hspan
  let a : (Fin 7 → ZMod 3) →ₗ[ZMod 3] ZMod 3 := aa.comp chart.symm.toLinearMap
  have ha_h : ∀ i : Fin 6, a (Pi.single i.castSucc 1) = aa (h i) := by
    intro i
    change aa (chart.symm (Pi.single i.castSucc 1)) = aa (h i)
    rw [← hchart_h i, chart.symm_apply_apply]
  have hfirst : ∀ i : Fin 6, a (Pi.single i.castSucc 1) =
      mu * B7 cartanE6ModThree c 0 (outsideCoords s k) (Pi.single i.castSucc 1) := by
    intro i
    rw [ha_h i, ← hUnit i, hres (unitRoot i)]
    congr 1
    change Bform (H (unitRoot i)) w =
      B7 cartanE6ModThree c 0 (outsideCoords s k) (Pi.single i.castSucc 1)
    rw [hUnit i, hBform]
    change B7 cartanE6ModThree c 0 (chart (h i)) (chart w) =
      B7 cartanE6ModThree c 0 (outsideCoords s k) (Pi.single i.castSucc 1)
    rw [hchart_h i, hchart_w, hB7_symm.eq]
  obtain ⟨b, hb⟩ := outside_exists_form c s k a mu hk hmu hfirst
  have hfull : ∀ v : V, aa v = mu * B7 cartanE6ModThree c b (outsideCoords s k) (chart v) := by
    intro v
    have := congrArg (fun f => f (chart v)) hb
    simpa [a, chart.symm_apply_apply] using this
  refine ⟨b, mu, hmu, hfull, ?_⟩
  intro v
  rw [hFlin v, hfull v]

end E6Seven
end CFSG.StandardType

public section
namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

theorem e6_B7_first_row_eq_any_entry (c : Fin 6 → ZMod 3) (b d : ZMod 3)
    (i : Fin 6) (v : Fin 7 → ZMod 3) :
    B7 cartanE6ModThree c b (Pi.single i.castSucc 1) v =
      B7 cartanE6ModThree c d (Pi.single i.castSucc 1) v := by
  have hC : cartanE6ModThree.IsSymm := by
    ext i j
    exact (cartanE6ModThree_symm i j).symm
  rw [(B7_isSymm cartanE6ModThree c b hC).eq,
    (B7_isSymm cartanE6ModThree c d hC).eq, eq_outsideCoords v,
    outside_B7_castSucc, outside_B7_castSucc]

theorem e6_B7_H_second_eq_any_entry
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (hchart : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (c : Fin 6 → ZMod 3) (b d : ZMod 3) (w : V) (u : Fin 6 → ZMod 3) :
    B7 cartanE6ModThree c b (chart w)
      (chart (Fintype.linearCombination (ZMod 3) h u)) =
    B7 cartanE6ModThree c d (chart w)
      (chart (Fintype.linearCombination (ZMod 3) h u)) := by
  have hC : cartanE6ModThree.IsSymm := by
    ext i j
    exact (cartanE6ModThree_symm i j).symm
  rw [(B7_isSymm cartanE6ModThree c b hC).eq,
    (B7_isSymm cartanE6ModThree c d hC).eq]
  rw [Fintype.linearCombination_apply, map_sum, map_sum, map_sum,
    LinearMap.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    hchart i, e6_B7_first_row_eq_any_entry c b d]

theorem e6_actual_unit_restriction_all_from_original
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs)
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v, Bform (ggLin (p := 3) ι (φL i) u)
      (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (rootRefl : Fin 72 → MulAut ↥Bs)
    (hRootMem : ∀ m, rootRefl m ∈ ggAutomizer L Bs)
    (hRootAction : ∀ m v, ggLin (p := 3) ι (rootRefl m) v =
      v - Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) v •
        Fintype.linearCombination (ZMod 3) h (rootVec m))
    (hRootSelf : ∀ m, Bform (Fintype.linearCombination (ZMod 3) h (rootVec m))
      (Fintype.linearCombination (ZMod 3) h (rootVec m)) = 2)
    (lam : ZMod 3)
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r)
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3)) (c : Fin 6 → ZMod 3)
    (hchart : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (hform : Bform = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap)
    (hc : c ⬝ᵥ cartanE6KernelVec ≠ 0)
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2) :
    ∀ u : Fin 6 → ZMod 3, aa (Fintype.linearCombination (ZMod 3) h u) =
      Bform w (Fintype.linearCombination (ZMod 3) h u) := by
  classical
  let s : Fin 6 → ZMod 3 := fun i => chart w i.castSucc
  let k : ZMod 3 := chart w (Fin.last 6)
  have hcw : chart w = outsideCoords s k := eq_outsideCoords (chart w)
  by_cases hk : k = 0
  · have hws : w = Fintype.linearCombination (ZMod 3) h s := by
      apply chart.injective
      rw [hcw, hk]
      simp only [outsideCoords, zero_smul, add_zero,
        Fintype.linearCombination_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hchart i]
    obtain ⟨_, _, hfull⟩ := e6_actual_inside_unit_functional_from_original
      hH hx hLNoncyclic ι Bform h α φL hLI hpair hB hlin hgenB hinv hgenL hclosL
      rootRefl hRootMem hRootAction hRootSelf lam hxvec F w aa hF hFlin hself s hws
    exact fun u => hfull _
  · obtain ⟨b, mu, hmu, haa, _⟩ := e6_outside_actual_form_sameWitness hH ι h α Bform
      rootRefl hRootMem hRootAction hRootSelf F w aa hF hFlin hself chart c
      hchart hB hform s k hcw hk hc
    let Bb : LinearMap.BilinForm (ZMod 3) V :=
      (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap
    have hBb : ∀ i, Bb (h i) = α i := by
      intro i
      apply LinearMap.ext
      intro v
      change B7 cartanE6ModThree c b (chart (h i)) (chart v) = α i v
      rw [hchart i, e6_B7_first_row_eq_any_entry c b 0]
      have hh := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f v) (hB i)
      rw [hform] at hh
      simpa [LinearMap.BilinForm.comp_apply, hchart i] using hh
    have hC : cartanE6ModThree.IsSymm := by
      ext i j
      exact (cartanE6ModThree_symm i j).symm
    have hsymm : ∀ u v, Bb u v = Bb v u := by
      intro u v
      exact (B7_isSymm cartanE6ModThree c b hC).eq (chart u) (chart v)
    have hdiag : ∀ i : Fin 6, gram7 cartanE6ModThree c b i.castSucc i.castSucc = 2 := by
      intro i
      rw [gram7_castSucc_castSucc]
      fin_cases i <;> rfl
    have hgenBb : ∀ i u v, Bb (ggLin (p := 3) ι (φL i) u)
        (ggLin (p := 3) ι (φL i) v) = Bb u v :=
      chart_generator_invariant h α φL ι hlin chart c b hchart hBb
        (gram7_symm cartanE6ModThree c b hC) hdiag
    have haaBb : ∀ v, aa v = mu * Bb w v := by
      intro v
      rw [haa v]
      change mu * B7 cartanE6ModThree c b (outsideCoords s k) (chart v) =
        mu * B7 cartanE6ModThree c b (chart w) (chart v)
      rw [hcw]
    have hbeta : (fun i => Bb (h i) w) ⬝ᵥ r ≠ 0 := by
      have heq : (fun i => Bb (h i) w) = cartanE6ModThree *ᵥ s + k • c := by
        funext i
        change B7 cartanE6ModThree c b (chart (h i)) (chart w) = _
        rw [hchart i, hcw, (B7_isSymm cartanE6ModThree c b hC).eq,
          outside_B7_castSucc]
      rw [heq]
      have hCmul : Cmul s = cartanE6ModThree *ᵥ s := by
        rw [Cmul_eq_mulVec]
        congr 1
        ext i j
        rw [C_eq_mathlib]
        simp [cartanE6ModThree]
      rw [← hCmul]
      exact outside_coordinate_pair_ne_zero c s k hk hc
    obtain ⟨_, _, hfull, _, _⟩ := e6_actual_outside_scale_eq_one_of_norm1_exclusion
      hH hx hLNoncyclic hLI hpair hBb hlin hgenBb hinv hgenL hclosL hsymm
      hF hFlin hself hmu haaBb hbeta hxvec
    intro u
    rw [hfull, hform]
    exact e6_B7_H_second_eq_any_entry h chart hchart c b 0 w u

end CFSG.StandardType.E6Seven

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end E6Seven
end CFSG.StandardType

public section

namespace CFSG.StandardType

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.StandardType

end

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_raw_outside_consumer_with_chart_independent_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ) {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hS : S.card = 2)
    (hΛa1 : 1 ≤ Nat.card Λa) (hΛa2 : Nat.card Λa ≤ 3)
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) fun i : Λ => h (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hFix : GGTBFixInput)
    (hcard : Nat.card Bs = 3 ^ 7)
    (hxBs : x ∈ Bs)
    (e : Fin 6 ≃ Λ)
    (hML' : ML = CoxeterMatrix.E₆.reindex e)
    (a : Λa)
    (ha : h (Sum.inr a) ∉
      Submodule.span (ZMod 3) (Set.range (fun i : Λ => h (Sum.inl i)))) :
    ∃ (z : V) (c : Fin 6 → ZMod 3) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
      (Bform : LinearMap.BilinForm (ZMod 3) V) (rootRefl : Fin 72 → MulAut ↥Bs)
      (b mu : ZMod 3),
      mu ≠ 0 ∧
      (∀ i : Fin 6, chart (h (Sum.inl (e i))) = Pi.single i.castSucc 1) ∧
      chart z = Pi.single (Fin.last 6) 1 ∧
      Bform = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap ∧
      c ⬝ᵥ cartanE6KernelVec ≠ 0 ∧
      chart (h (Sum.inr a)) (Fin.last 6) ≠ 0 ∧
      (∀ i : Fin 6, Bform (h (Sum.inl (e i))) = α (Sum.inl (e i))) ∧
      (∀ i j : Fin 6, Bform (h (Sum.inl (e i))) (h (Sum.inl (e j))) =
        cartanE6ModThree i j) ∧
      (∀ i : Fin 6, Bform (h (Sum.inl (e i))) z = α (Sum.inl (e i)) z) ∧
      Bform z z = 0 ∧
      rootRefl = (fun m => e6RootRefl (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m)) ∧
      (∀ m, rootRefl m ∈ ggAutomizer L Bs) ∧
      (∀ m v, ggLin (p := 3) ι (rootRefl m) v =
        v - Bform (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => h (Sum.inl (e i))) (rootVec m)) v •
          Fintype.linearCombination (ZMod 3)
            (fun i : Fin 6 => h (Sum.inl (e i))) (rootVec m)) ∧
      (∀ m, Bform (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => h (Sum.inl (e i))) (rootVec m))
        (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => h (Sum.inl (e i))) (rootVec m)) = 2) ∧
      (∀ v : V, α (Sum.inr a) v =
        mu * B7 cartanE6ModThree c b
          (outsideCoords (fun i => chart (h (Sum.inr a)) i.castSucc)
            (chart (h (Sum.inr a)) (Fin.last 6))) (chart v)) ∧
      (∀ v : V, ggLin (p := 3) ι (φ (Sum.inr a)) v =
        v - (mu * B7 cartanE6ModThree c b
          (outsideCoords (fun i => chart (h (Sum.inr a)) i.castSucc)
            (chart (h (Sum.inr a)) (Fin.last 6))) (chart v)) • h (Sum.inr a)) := by
  classical
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  have hLI : LinearIndependent (ZMod 3) h' := hsel.comp e e.injective
  have hpair' : ∀ i j, α' i (h' j) = cartanE6ModThree i j := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML']
    simp [cartanE6ModThree]
  obtain ⟨z, c, chart, Bform, hchart_h, hchart_z, hform_h, hform_hh, hform_hz, hform_zz,
    hBform, hRootMem, hRootAction, hRootSelf⟩ :=
    e6_raw_chart_root_actions hML hCL ι φ h α hlin hsel hpair hrefl hclosL e hML' hcard
  have hfix : ∀ w : V, (∀ i : Fin 6, α' i w = 0) →
      ∃ lam : ZMod 3,
        w = lam • ι (Additive.ofMul ⟨x, hxBs⟩) := by
    intro w hw
    have hw0 : ∀ i : Λ, α (Sum.inl i) w = 0 := by
      intro i
      have := hw (e.symm i)
      simpa [α', h'] using this
    exact ggRes_raw_commonKernel_le_xline hFix hH a ι φ h α hlin hclosL w hw0
  have hz : z ∉ Submodule.span (ZMod 3) (Set.range h') :=
    not_mem_span_of_chart_last h' z chart hchart_h hchart_z
  have hzc : ∀ i : Fin 6, α' i z = c i := by
    intro i
    have h1 : α' i z = Bform (h' i) z := by rw [hform_h i]
    rw [h1, hBform]
    change B7 cartanE6ModThree c 0 (chart (h' i)) (chart z) = c i
    rw [hchart_h i, hchart_z, B7_single_single, gram7_castSucc_last]
  have hc : c ⬝ᵥ cartanE6KernelVec ≠ 0 :=
    c_dot_kernelVec_ne_zero_of_commonKernel_le_line h' hLI z hz α' c hzc hpair'
      (ι (Additive.ofMul ⟨x, hxBs⟩)) hfix
  let F : MulAut ↥Bs := φ (Sum.inr a)
  let w : V := h (Sum.inr a)
  let aa : Module.Dual (ZMod 3) V := α (Sum.inr a)
  have hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w := by
    intro v
    exact hlin (Sum.inr a) v
  have hself : aa w = 2 := by
    have hpair_a : α (Sum.map Subtype.val id (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa))
        (h (Sum.map Subtype.val id (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa))) =
        (CK (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa)
          (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa) : ZMod 3) :=
      hpairK (Sum.inr a) (Sum.inr a)
    have hCK_a : CK (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa)
        (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa) = 2 := hCK.1 (Sum.inr a)
    change α (Sum.inr a : Λ ⊕ Λa) (h (Sum.inr a : Λ ⊕ Λa)) = 2
    simpa [Sum.map] using hpair_a.trans (by rw [hCK_a]; norm_num)
  obtain ⟨fK, hfK⟩ := hfK
  have hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    apply (show ggAutomizer K Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs from le_sup_right)
    have hFK : (fK (MK.simple (Sum.inr a)) : MulAut ↥Bs) = F := by
      simpa [F] using hfK (Sum.inr a : {i : Λ // i ∉ S} ⊕ Λa)
    rw [← hFK]
    exact (fK (MK.simple (Sum.inr a))).2
  have hrange : Set.range h' = Set.range (fun i : Λ => h (Sum.inl i)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [h']⟩
  have ha' : h (Sum.inr a) ∉ Submodule.span (ZMod 3) (Set.range h') := by
    rwa [hrange]
  let s : Fin 6 → ZMod 3 := fun i => chart w i.castSucc
  let k : ZMod 3 := chart w (Fin.last 6)
  have hk : k ≠ 0 := chart_last_ne_zero_of_not_mem_span h' chart hchart_h (h (Sum.inr a)) ha' 
  have hchart_w : chart w = outsideCoords s k := eq_outsideCoords (chart w)
  obtain ⟨b, mu, hmu, hfull, haction⟩ :=
    e6_outside_actual_form_sameWitness hH ι h' α' Bform
      (fun m => e6RootRefl (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m))
      hRootMem hRootAction hRootSelf F w aa hF hFlin hself chart c hchart_h hform_h hBform
      s k hchart_w hk hc
  refine ⟨z, c, chart, Bform,
    fun m => e6RootRefl (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m),
    b, mu, hmu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hchart_h i
  · exact hchart_z
  · exact hBform
  · exact hc
  · simpa [k, w] using hk
  · intro i
    exact hform_h i
  · intro i j
    exact hform_hh i j
  · intro i
    exact hform_hz i
  · exact hform_zz
  · rfl
  · intro m
    exact hRootMem m
  · intro m v
    exact hRootAction m v
  · intro m
    exact hRootSelf m
  · intro v
    exact hfull v
  · intro v
    exact haction v

end E6Seven
end CFSG.StandardType

public section

namespace CFSG.StandardType

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open CFSG.StandardType.E7F3
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_raw_outside_unit_form_with_chart_basis_actual_inside_witnesslinks_independent_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFix : GGTBFixInput)
    (hcard : Nat.card Bs = 3 ^ 7)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ) (hS : S.card = 2)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (hΛa1 : 1 ≤ Nat.card Λa) (hΛa2 : Nat.card Λa ≤ 3)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Λ)
    (hML' : ML = CoxeterMatrix.E₆.reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (hV : Λ ⊕ Λa → V)
    (αV : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - αV o w • hV o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hpair : ∀ i j : Λ,
      αV (Sum.inl i) (hV (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      αV (o.map Subtype.val id) (hV (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hselII : LinearIndependent (ZMod 3) (fun i : Λ => hV (Sum.inl i)))
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hconn : GGDeletedConnectedS ML S)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)))
    (a : Λa)
    (ha_out : hV (Sum.inr a) ∉ Submodule.span (ZMod 3)
      (Set.range fun i : Λ => hV (Sum.inl i))) :
    ∃ (z : V) (c : Fin 6 → ZMod 3) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
      (b : ZMod 3) (Bb : LinearMap.BilinForm (ZMod 3) V)
      (chi : V ≃ₗ[ZMod 3] V7)
      (Bform0 : LinearMap.BilinForm (ZMod 3) V)
      (rootRefl : Fin 72 → MulAut ↥Bs) (lam : ZMod 3),
      Bb = (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap ∧
      (∀ i : Fin 6, chart (hV (Sum.inl (e i))) = Pi.single i.castSucc 1) ∧
      chart z = Pi.single (Fin.last 6) 1 ∧
      c ⬝ᵥ cartanE6KernelVec ≠ 0 ∧
      chart (hV (Sum.inr a)) (Fin.last 6) ≠ 0 ∧
      (∀ i : Fin 6, Bb (hV (Sum.inl (e i))) = αV (Sum.inl (e i))) ∧
      (∀ i j : Fin 6,
        Bb (hV (Sum.inl (e i))) (hV (Sum.inl (e j))) = cartanE6ModThree i j) ∧
      (∀ v, αV (Sum.inr a) v = Bb (hV (Sum.inr a)) v) ∧
      (∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v =
        v - Bb (hV (Sum.inr a)) v • hV (Sum.inr a)) ∧
      Bb (hV (Sum.inr a)) (hV (Sum.inr a)) = 2 ∧
      (∀ u v, Bb (ggLin (p := 3) ι (φ (Sum.inr a)) u)
        (ggLin (p := 3) ι (φ (Sum.inr a)) v) = Bb u v) ∧
      Bb z z = b ∧
      (∀ i : Fin 6, chi (hV (Sum.inl (e i))) = Pi.single i.castSucc 1) ∧
      chi (Fintype.linearCombination (ZMod 3)
        (fun i : Fin 6 => hV (Sum.inl (e i))) cartanE6KernelVec) = rvec ∧
      (∀ u v, Bb u v = pair (chi u) (chi v)) ∧
      CFSG.StandardType.E7F3.norm (chi (hV (Sum.inr a))) = 2 ∧
      chi (hV (Sum.inr a)) (Fin.last 6) ≠ 0 ∧
      (∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v =
        v - pair (chi (hV (Sum.inr a))) (chi v) • hV (Sum.inr a)) ∧
      (∀ (v : V7) (hn : CFSG.StandardType.E7F3.norm v = 2), v 6 = 0 →
        reflPerm v hn ∈
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (chartConjHom chi ι) →
        reflPerm v hn ∈ CFSG.StandardType.E7F3.L) ∧
      Bform0 = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap ∧
      (∀ i : Fin 6, Bform0 (hV (Sum.inl (e i))) = αV (Sum.inl (e i))) ∧
      (∀ i j : Fin 6,
        Bform0 (hV (Sum.inl (e i))) (hV (Sum.inl (e j))) = cartanE6ModThree i j) ∧
      (∀ i : Fin 6, Bform0 (hV (Sum.inl (e i))) z = αV (Sum.inl (e i)) z) ∧
      Bform0 z z = 0 ∧
      rootRefl = (fun m => e6RootRefl
        (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m)) ∧
      (∀ m, rootRefl m ∈ ggAutomizer L Bs) ∧
      (∀ m v, ggLin (p := 3) ι (rootRefl m) v =
        v - Bform0 (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) v •
          Fintype.linearCombination (ZMod 3)
            (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) ∧
      (∀ m, Bform0 (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m))
        (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) = 2) ∧
      ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) =
        lam • Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) r ∧
      (∀ i u v,
        Bform0 (ggLin (p := 3) ι ((fun j : Fin 6 => φ (Sum.inl (e j))) i) u)
          (ggLin (p := 3) ι ((fun j : Fin 6 => φ (Sum.inl (e j))) i) v) =
        Bform0 u v) := by

  classical
  let h' : Fin 6 → V := fun i => hV (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => αV (Sum.inl (e i))
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  have hLI : LinearIndependent (ZMod 3) h' := hselII.comp e e.injective
  have hpair' : ∀ i j, α' i (h' j) = cartanE6ModThree i j := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML']
    simp [cartanE6ModThree]
  have hlinL : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α' i v • h' i := by
    intro i v
    exact hlin (Sum.inl (e i)) v
  have hclosL' : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
  have hgenL : ∀ i, φL i ∈ ggAutomizer L Bs := by
    intro i
    rw [hclosL']
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hinv : ∀ i, φL i * φL i = 1 := by
    intro i
    have := (hrefl (Sum.inl (e i))).1
    simpa [φL, pow_two] using this
  obtain ⟨z, c, chart, Bform0, rootRefl, b, mu, hmu, hchart_h, hchart_z, hBform0,
    hc, hk, hform_h0, hform_hh0, hform_hz0, hform_zz0, hRootEq, hRootMem,
    hRootAction0, hRootSelf0, hfull, haction0⟩ :=
    e6_raw_outside_consumer_with_chart_independent_L hH S ML CL MK CK ι φ hV αV
      hS hΛa1 hΛa2 hML hCL hMK hCK hlin hrefl hpair hpairK hselII hfK hclosL hFix hcard
      hH.1.tableB_facts.2.2.1 e hML' a ha_out
  let Bb : LinearMap.BilinForm (ZMod 3) V :=
    (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap
  have hB : ∀ i : Fin 6, Bb (h' i) = α' i := by
    intro i
    apply LinearMap.ext
    intro v
    have h0 : B7 cartanE6ModThree c 0 (Pi.single i.castSucc 1) (chart v) = α' i v := by
      have hthis := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f v) (hform_h0 i)
      rw [hBform0] at hthis
      simpa [LinearMap.BilinForm.comp_apply, hchart_h i] using hthis
    change B7 cartanE6ModThree c b (chart (h' i)) (chart v) = α' i v
    rw [hchart_h i, e6_B7_first_row_eq_any_entry c b 0 i (chart v), h0]
  have hC_symm : cartanE6ModThree.IsSymm := by
    ext i j
    exact (cartanE6ModThree_symm i j).symm
  have hBsymm : ∀ u v, Bb u v = Bb v u := by
    intro u v
    change B7 cartanE6ModThree c b (chart u) (chart v) =
      B7 cartanE6ModThree c b (chart v) (chart u)
    exact (B7_isSymm cartanE6ModThree c b hC_symm).eq (chart u) (chart v)
  have hsymm_b : (gram7 cartanE6ModThree c b).IsSymm := by
    apply gram7_symm
    exact hC_symm
  have hdiag_b : ∀ i : Fin 6, gram7 cartanE6ModThree c b i.castSucc i.castSucc = 2 := by
    intro i
    rw [gram7_castSucc_castSucc]
    fin_cases i <;> rfl
  have hsymm0 : (gram7 cartanE6ModThree c 0).IsSymm := by
    apply gram7_symm
    exact hC_symm
  have hdiag0 : ∀ i : Fin 6, gram7 cartanE6ModThree c 0 i.castSucc i.castSucc = 2 := by
    intro i
    rw [gram7_castSucc_castSucc]
    fin_cases i <;> rfl
  have hB0' : ∀ i : Fin 6,
      ((B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap) (h' i) = α' i := by
    intro i
    rw [← hBform0]
    exact hform_h0 i
  have hgenB0 : ∀ i u v,
      Bform0 (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform0 u v := by
    intro i u v
    rw [hBform0]
    exact chart_generator_invariant h' α' φL ι hlinL chart c 0 hchart_h hB0' hsymm0 hdiag0 i u v

  have hgenB : ∀ i u v,
      Bb (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bb u v := by
    intro i u v
    change (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap
      (ggLin (p := 3) ι (φL i) u)
      (ggLin (p := 3) ι (φL i) v) = Bb u v
    exact chart_generator_invariant h' α' φL ι hlinL chart c b hchart_h hB hsymm_b hdiag_b i u v
  let F : MulAut ↥Bs := φ (Sum.inr a)
  let w : V := hV (Sum.inr a)
  let aa : Module.Dual (ZMod 3) V := αV (Sum.inr a)
  have hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w := by
    intro v
    exact hlin (Sum.inr a) v
  have hself : aa w = 2 := by
    dsimp [aa, w]
    have hp : αV (Sum.inr a) (hV (Sum.inr a)) =
        (CK (Sum.inr a) (Sum.inr a) : ZMod 3) := by
      simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a) (Sum.inr a)
    rw [hp, hCK.1 (Sum.inr a)]
    rfl
  obtain ⟨fK, hfK'⟩ := hfK
  have hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    apply Subgroup.mem_sup_right
    have hFK : (fK (MK.simple (Sum.inr a)) : MulAut ↥Bs) = F := by
      simpa [F] using hfK' (Sum.inr a)
    rw [← hFK]
    exact (fK (MK.simple (Sum.inr a))).2
  obtain ⟨lam, hxvec⟩ :=
    e6_raw_radical_alignment hFix hH hcard hML hCL ι φ hV αV hlin hselII hpair hclosL e hML'
      hΛa1
  let s : Fin 6 → ZMod 3 := fun i => chart w i.castSucc
  let k : ZMod 3 := chart w (Fin.last 6)
  have hchart_w : chart w = outsideCoords s k := eq_outsideCoords (chart w)
  have hk0 : k ≠ 0 := hk
  have hfull' : ∀ v : V, αV (Sum.inr a) v =
      mu * B7 cartanE6ModThree c b (outsideCoords s k) (chart v) := by
    intro v
    simpa [s, k, w] using hfull v
  have haa : ∀ v, aa v = mu * Bb w v := by
    intro v
    rw [hfull' v]
    congr 1
    change B7 cartanE6ModThree c b (outsideCoords s k) (chart v) =
      B7 cartanE6ModThree c b (chart w) (chart v)
    rw [hchart_w]
  have hCmul : Cmul s = cartanE6ModThree *ᵥ s := by
    rw [Cmul_eq_mulVec]
    congr 1
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  let beta : Fin 6 → ZMod 3 := fun i => Bb (h' i) w
  have hbeta_eq : beta = Cmul s + k • c := by
    funext i
    change B7 cartanE6ModThree c b (chart (h' i)) (chart w) = (Cmul s + k • c) i
    rw [hchart_h i, hchart_w, hCmul]
    rw [(B7_isSymm cartanE6ModThree c b hC_symm).eq]
    exact outside_B7_castSucc c s k b i
  have hbeta : beta ⬝ᵥ cartanE6KernelVec ≠ 0 := by
    rw [hbeta_eq]
    exact outside_coordinate_pair_ne_zero c s k hk0 hc
  have hLNoncyclic : GGLNoncyclicInput := ggLNoncyclicInput_holds
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨hmu1, hww2, hfull_aa, haction, hiso⟩ :=
    e6_actual_outside_scale_eq_one_of_norm1_exclusion hH hx hLNoncyclic hLI hpair' hB
      hlinL hgenB hinv hgenL hclosL' hBsymm hF hFlin hself hmu haa hbeta hxvec
  obtain ⟨chi, hchi, hchi_r, _hchi_rvec, hform_pair⟩ :=
    exists_normalized_chart chart h' c b hchart_h hc
  have hBb : Bb = (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap := rfl
  have hpairB : ∀ i j : Fin 6,
      Bb (h' i) (h' j) = cartanE6ModThree i j := by
    intro i j
    rw [hB i]
    exact hpair' i j
  have hform_Bb : ∀ u v, Bb u v = pair (chi u) (chi v) := by
    intro u v
    rw [hBb]
    exact hform_pair u v
  have hnorm : CFSG.StandardType.E7F3.norm (chi w) = 2 := by
    rw [CFSG.StandardType.E7F3.norm, ← hform_Bb w w]
    exact hww2
  have hlast : chi w (Fin.last 6) ≠ 0 := by
    intro hlast0
    let s : Fin 6 → ZMod 3 := fun i => chi w i.castSucc
    have hchiH : chi (Fintype.linearCombination (ZMod 3) h' s) = chi w := by
      ext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [normalized_chart_H_last chi h' hchi s]
        exact hlast0.symm
      · rw [normalized_chart_H_castSucc chi h' hchi s i]
    have hw_eq : w = Fintype.linearCombination (ZMod 3) h' s := by
      apply chi.injective
      exact hchiH.symm
    have hspan : w ∈ Submodule.span (ZMod 3)
        (Set.range fun i : Λ => hV (Sum.inl i)) := by
      rw [hw_eq, Fintype.linearCombination_apply]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e i, rfl⟩)
    exact ha_out hspan
  have haction_norm : ∀ v, ggLin (p := 3) ι F v =
      v - pair (chi w) (chi v) • w := by
    intro v
    rw [haction v, hform_Bb w v]
  have hInside := normalized_chart_inside_reflections_mem_literalL hH hx hLNoncyclic ι Bb h' α' φL
    hLI hpair' hB hlinL hgenB hinv hgenL hclosL' chi hchi hform_Bb lam hxvec

  have hzz : Bb z z = b := by
    change B7 cartanE6ModThree c b (chart z) (chart z) = b
    rw [hchart_z, B7_single_single]
    exact gram7_last_last c b
  refine ⟨z, c, chart, b, Bb, chi, Bform0, rootRefl, lam, ?_⟩
  exact ⟨hBb, hchart_h, hchart_z, hc, hk, hB, hpairB, hfull_aa, haction, hww2, hiso,
    hzz, hchi, hchi_r, hform_Bb, hnorm, hlast, haction_norm, hInside,
    hBform0, hform_h0, hform_hh0, hform_hz0, hform_zz0, hRootEq, hRootMem,
    hRootAction0, hRootSelf0, hxvec, hgenB0⟩

end CFSG.StandardType

end

public section
namespace CFSG.StandardType.E6Seven
open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

theorem e6_conj_reflection_action
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) {F H : MulAut ↥Bs}
    {w u : V} {aa bb : Module.Dual (ZMod 3) V}
    (hH2 : H * H = 1) (hHself : bb u = 2)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hHlin : ∀ v, ggLin (p := 3) ι H v = v - bb v • u)
    (x : V) :
    ggLin (p := 3) ι (H * F * H⁻¹) x =
      x - (aa x - aa u * bb x) • (w - bb w • u) := by
  have hHinv : H⁻¹ = H := by
    exact inv_eq_of_mul_eq_one_right hH2
  rw [hHinv]
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hHlin, hFlin, hHlin]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hHself]
  module

theorem e6_unit_restriction_cross_eq
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (U : Submodule (ZMod 3) V)
    (B : LinearMap.BilinForm (ZMod 3) V)
    {w_i w_j : V} {aa_i aa_j : Module.Dual (ZMod 3) V}
    (hunit_i : ∀ u ∈ U, aa_i u = B w_i u)
    (hunit_j : ∀ u ∈ U, aa_j u = B w_j u)
    (hunit_conj : ∀ u ∈ U,
      aa_i u - aa_i w_j * aa_j u =
        B (w_i - aa_j w_i • w_j) u)
    (hne : ∃ u ∈ U, B w_j u ≠ 0) :
    aa_i w_j = aa_j w_i := by
  obtain ⟨u, huU, hneu⟩ := hne
  have hconj := hunit_conj u huU
  have hsub : B (w_i - aa_j w_i • w_j) u =
      B w_i u - aa_j w_i * B w_j u := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
  rw [hsub, hunit_i u huU, hunit_j u huU] at hconj
  have hcancel : aa_i w_j * B w_j u = aa_j w_i * B w_j u := by
    linear_combination -hconj
  exact mul_right_cancel₀ hneu hcancel

theorem e6_conj_selfpair
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (w u : V) (aa bb : Module.Dual (ZMod 3) V)
    (hFself : aa w = 2) (hHself : bb u = 2) :
    (aa - aa u • bb) (w - bb w • u) = 2 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_sub, map_smul]
  rw [hFself, hHself]
  ring_nf

theorem e6_six_span_and_outside_decomposition
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (hchart : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (u : V) (hu : chart u (Fin.last 6) ≠ 0) :
    ∀ v, ∃ (s : Fin 6 → ZMod 3) (k : ZMod 3),
      v = Fintype.linearCombination (ZMod 3) h s + k • u := by
  intro v
  let k : ZMod 3 := chart v (Fin.last 6) / chart u (Fin.last 6)
  let s : Fin 6 → ZMod 3 := fun i => chart v i.castSucc - k * chart u i.castSucc
  have hHs : chart (Fintype.linearCombination (ZMod 3) h s) =
      ∑ i : Fin 6, s i • Pi.single i.castSucc 1 := by
    rw [Fintype.linearCombination_apply, map_sum]
    simp_rw [map_smul, hchart]
  have hlast : chart (Fintype.linearCombination (ZMod 3) h s) (Fin.last 6) = 0 := by
    rw [hHs]
    have hne (i : Fin 6) : (6 : Fin 7) ≠ i.castSucc := by
      intro heq
      have heq' := congrArg Fin.val heq
      change (6 : ℕ) = i.val at heq'
      omega
    simp [Finset.sum_apply, Pi.single_apply, hne]
  have hcast (i : Fin 6) :
      chart (Fintype.linearCombination (ZMod 3) h s) i.castSucc = s i := by
    rw [hHs]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Fin.castSucc_inj]
    simp
  refine ⟨s, k, ?_⟩
  apply chart.injective
  rw [map_add, map_smul]
  ext j
  change chart v j = chart (Fintype.linearCombination (ZMod 3) h s) j +
    k * chart u j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [hlast]
    change chart v (Fin.last 6) = 0 + k * chart u (Fin.last 6)
    rw [zero_add]
    dsimp [k]
    exact (div_mul_cancel₀ (chart v (Fin.last 6)) hu).symm
  · rw [hcast i]
    change chart v i.castSucc = s i + k * chart u i.castSucc
    dsimp [s]
    ring

theorem e6_full_form_of_universal_actual_restriction
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    (Bform : LinearMap.BilinForm (ZMod 3) V) (h : Fin 6 → V)
    (hsymm : ∀ v w, Bform v w = Bform w v)
    (hRestr : ∀ (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V),
      F ∈ A → (∀ v, ggLin (p := 3) ι F v = v - aa v • w) → aa w = 2 →
      ∀ s, aa (Fintype.linearCombination (ZMod 3) h s) =
        Bform w (Fintype.linearCombination (ZMod 3) h s))
    (H : MulAut ↥Bs) (u : V) (bb : Module.Dual (ZMod 3) V)
    (hH : H ∈ A) (hH2 : H * H = 1)
    (hHlin : ∀ v, ggLin (p := 3) ι H v = v - bb v • u)
    (hHself : bb u = 2) (hHfull : ∀ v, bb v = Bform u v)
    (hBeta : ∃ s, Bform u (Fintype.linearCombination (ZMod 3) h s) ≠ 0)
    (hspan : ∀ v, ∃ (s : Fin 6 → ZMod 3) (k : ZMod 3),
      v = Fintype.linearCombination (ZMod 3) h s + k • u)
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ A) (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hFself : aa w = 2) : ∀ v, aa v = Bform w v := by
  let U : Submodule (ZMod 3) V :=
    (Fintype.linearCombination (ZMod 3) h).range
  have hunitF : ∀ v ∈ U, aa v = Bform w v := by
    rintro v ⟨s, rfl⟩
    exact hRestr F w aa hF hFlin hFself s
  have hunitH : ∀ v ∈ U, bb v = Bform u v := fun v _ => hHfull v
  have hconjmem : H * F * H⁻¹ ∈ A :=
    mul_mem (mul_mem hH hF) (inv_mem hH)
  have hconjlin : ∀ v, ggLin (p := 3) ι (H * F * H⁻¹) v =
      v - (aa - aa u • bb) v • (w - bb w • u) := by
    intro v
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using
      e6_conj_reflection_action ι hH2 hHself hFlin hHlin v
  have hconjself := e6_conj_selfpair w u aa bb hFself hHself
  have hunitConj : ∀ v ∈ U, aa v - aa u * bb v =
      Bform (w - bb w • u) v := by
    rintro v ⟨s, rfl⟩
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using
      hRestr (H * F * H⁻¹) (w - bb w • u) (aa - aa u • bb)
        hconjmem hconjlin hconjself s
  have hne : ∃ v ∈ U, Bform u v ≠ 0 := by
    obtain ⟨s, hs⟩ := hBeta
    exact ⟨_, ⟨s, rfl⟩, hs⟩
  have hcross : aa u = bb w :=
    e6_unit_restriction_cross_eq U Bform hunitF hunitH hunitConj hne
  intro v
  obtain ⟨s, k, rfl⟩ := hspan v
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hRestr F w aa hF hFlin hFself s, hcross, hHfull w, hsymm u w]

theorem e6_all_actual_reflections_share_first_outside_form
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs)
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v, Bform (ggLin (p := 3) ι (φL i) u)
      (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (rootRefl : Fin 72 → MulAut ↥Bs)
    (hRootMem : ∀ m, rootRefl m ∈ ggAutomizer L Bs)
    (hRootAction : ∀ m v, ggLin (p := 3) ι (rootRefl m) v =
      v - Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) v •
        Fintype.linearCombination (ZMod 3) h (rootVec m))
    (hRootSelf : ∀ m, Bform (Fintype.linearCombination (ZMod 3) h (rootVec m))
      (Fintype.linearCombination (ZMod 3) h (rootVec m)) = 2)
    (lam : ZMod 3)
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r)
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3)) (c : Fin 6 → ZMod 3)
    (hchart : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (hform : Bform = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap)
    (hc : c ⬝ᵥ cartanE6KernelVec ≠ 0)
    (b : ZMod 3) (Bb : LinearMap.BilinForm (ZMod 3) V)
    (hBb : Bb = (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap)
    (H : MulAut ↥Bs) (u : V) (bb : Module.Dual (ZMod 3) V)
    (hHmem : H ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hH2 : H * H = 1)
    (hHlin : ∀ v, ggLin (p := 3) ι H v = v - bb v • u)
    (hHself : bb u = 2) (hHfull : ∀ v, bb v = Bb u v)
    (hOutside : chart u (Fin.last 6) ≠ 0)
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2) : ∀ v, aa v = Bb w v := by
  have hC : cartanE6ModThree.IsSymm := by
    ext i j
    exact (cartanE6ModThree_symm i j).symm
  have hsymm : ∀ v w, Bb v w = Bb w v := by
    intro v w
    rw [hBb]
    exact (B7_isSymm cartanE6ModThree c b hC).eq (chart v) (chart w)
  have hRestr : ∀ (Q : MulAut ↥Bs) (v : V) (ff : Module.Dual (ZMod 3) V),
      Q ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs →
      (∀ t, ggLin (p := 3) ι Q t = t - ff t • v) → ff v = 2 →
      ∀ s, ff (Fintype.linearCombination (ZMod 3) h s) =
        Bb v (Fintype.linearCombination (ZMod 3) h s) := by
    intro Q v ff hQ hQlin hQself s
    have hR := e6_actual_unit_restriction_all_from_original
      hH hx hLNoncyclic ι Bform h α φL hLI hpair hB hlin hgenB hinv hgenL hclosL
      rootRefl hRootMem hRootAction hRootSelf lam hxvec chart c hchart hform hc
      Q v ff hQ hQlin hQself
    rw [hR s, hform, hBb]
    exact e6_B7_H_second_eq_any_entry h chart hchart c 0 b v s
  let s : Fin 6 → ZMod 3 := fun i => chart u i.castSucc
  let k : ZMod 3 := chart u (Fin.last 6)
  have hcu : chart u = outsideCoords s k := eq_outsideCoords (chart u)
  have hbeta : (fun i => Bb (h i) u) ⬝ᵥ r ≠ 0 := by
    have heq : (fun i => Bb (h i) u) = cartanE6ModThree *ᵥ s + k • c := by
      funext i
      rw [hBb]
      change B7 cartanE6ModThree c b (chart (h i)) (chart u) = _
      rw [hchart i, hcu, (B7_isSymm cartanE6ModThree c b hC).eq,
        outside_B7_castSucc]
    rw [heq]
    have hCmul : Cmul s = cartanE6ModThree *ᵥ s := by
      rw [Cmul_eq_mulVec]
      congr 1
      ext i j
      rw [C_eq_mathlib]
      simp [cartanE6ModThree]
    rw [← hCmul]
    exact outside_coordinate_pair_ne_zero c s k hOutside hc
  have hBeta : ∃ t, Bb u (Fintype.linearCombination (ZMod 3) h t) ≠ 0 := by
    refine ⟨r, ?_⟩
    have heq : Bb u (Fintype.linearCombination (ZMod 3) h r) =
        (fun i => Bb (h i) u) ⬝ᵥ r := by
      rw [Fintype.linearCombination_apply, map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [hsymm u (h i), mul_comm]
    rw [heq]
    exact hbeta
  exact e6_full_form_of_universal_actual_restriction ι
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs) Bb h hsymm hRestr
    H u bb hHmem hH2 hHlin hHself hHfull hBeta
    (e6_six_span_and_outside_decomposition h chart hchart u hOutside)
    F w aa hF hFlin hself

end CFSG.StandardType.E6Seven
end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open CFSG.StandardType.E7F3
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_raw_all_added_unit_same_witness_independent_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFix : GGTBFixInput)
    (hcard : Nat.card Bs = 3 ^ 7)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ) (hS : S.card = 2)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (hΛa1 : 1 ≤ Nat.card Λa) (hΛa2 : Nat.card Λa ≤ 3)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Λ)
    (hML' : ML = CoxeterMatrix.E₆.reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (hV : Λ ⊕ Λa → V)
    (αV : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - αV o w • hV o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hpair : ∀ i j : Λ,
      αV (Sum.inl i) (hV (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      αV (o.map Subtype.val id) (hV (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hselII : LinearIndependent (ZMod 3) (fun i : Λ => hV (Sum.inl i)))
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hconn : GGDeletedConnectedS ML S)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)))
    (a : Λa)
    (ha_out : hV (Sum.inr a) ∉ Submodule.span (ZMod 3)
      (Set.range fun i : Λ => hV (Sum.inl i))) :
    ∃ (z : V) (c : Fin 6 → ZMod 3) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
      (b : ZMod 3) (Bb : LinearMap.BilinForm (ZMod 3) V)
      (chi : V ≃ₗ[ZMod 3] V7)
      (Bform0 : LinearMap.BilinForm (ZMod 3) V)
      (rootRefl : Fin 72 → MulAut ↥Bs) (lam : ZMod 3),
      Bb = (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap ∧
      (∀ i : Fin 6, chart (hV (Sum.inl (e i))) = Pi.single i.castSucc 1) ∧
      chart z = Pi.single (Fin.last 6) 1 ∧
      c ⬝ᵥ cartanE6KernelVec ≠ 0 ∧
      chart (hV (Sum.inr a)) (Fin.last 6) ≠ 0 ∧
      (∀ i : Fin 6, Bb (hV (Sum.inl (e i))) = αV (Sum.inl (e i))) ∧
      (∀ i j : Fin 6,
        Bb (hV (Sum.inl (e i))) (hV (Sum.inl (e j))) = cartanE6ModThree i j) ∧
      (∀ v, αV (Sum.inr a) v = Bb (hV (Sum.inr a)) v) ∧
      (∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v =
        v - Bb (hV (Sum.inr a)) v • hV (Sum.inr a)) ∧
      Bb (hV (Sum.inr a)) (hV (Sum.inr a)) = 2 ∧
      (∀ u v, Bb (ggLin (p := 3) ι (φ (Sum.inr a)) u)
        (ggLin (p := 3) ι (φ (Sum.inr a)) v) = Bb u v) ∧
      Bb z z = b ∧
      (∀ i : Fin 6, chi (hV (Sum.inl (e i))) = Pi.single i.castSucc 1) ∧
      chi (Fintype.linearCombination (ZMod 3)
        (fun i : Fin 6 => hV (Sum.inl (e i))) cartanE6KernelVec) = rvec ∧
      (∀ u v, Bb u v = pair (chi u) (chi v)) ∧
      CFSG.StandardType.E7F3.norm (chi (hV (Sum.inr a))) = 2 ∧
      chi (hV (Sum.inr a)) (Fin.last 6) ≠ 0 ∧
      (∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v =
        v - pair (chi (hV (Sum.inr a))) (chi v) • hV (Sum.inr a)) ∧
      (∀ (v : V7) (hn : CFSG.StandardType.E7F3.norm v = 2), v 6 = 0 →
        reflPerm v hn ∈
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (chartConjHom chi ι) →
        reflPerm v hn ∈ CFSG.StandardType.E7F3.L) ∧
      Bform0 = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap ∧
      (∀ i : Fin 6, Bform0 (hV (Sum.inl (e i))) = αV (Sum.inl (e i))) ∧
      (∀ i j : Fin 6,
        Bform0 (hV (Sum.inl (e i))) (hV (Sum.inl (e j))) = cartanE6ModThree i j) ∧
      (∀ i : Fin 6, Bform0 (hV (Sum.inl (e i))) z = αV (Sum.inl (e i)) z) ∧
      Bform0 z z = 0 ∧
      rootRefl = (fun m => e6RootRefl
        (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m)) ∧
      (∀ m, rootRefl m ∈ ggAutomizer L Bs) ∧
      (∀ m v, ggLin (p := 3) ι (rootRefl m) v =
        v - Bform0 (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) v •
          Fintype.linearCombination (ZMod 3)
            (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) ∧
      (∀ m, Bform0 (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m))
        (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) = 2) ∧
      ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) =
        lam • Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) r ∧
      (∀ i u v,
        Bform0 (ggLin (p := 3) ι ((fun j : Fin 6 => φ (Sum.inl (e j))) i) u)
          (ggLin (p := 3) ι ((fun j : Fin 6 => φ (Sum.inl (e j))) i) v) =
        Bform0 u v) ∧
      (∀ b' : Λa,
        (∀ v, αV (Sum.inr b') v = Bb (hV (Sum.inr b')) v) ∧
        CFSG.StandardType.E7F3.norm (chi (hV (Sum.inr b'))) = 2 ∧
        (∀ v, ggLin (p := 3) ι (φ (Sum.inr b')) v =
          v - pair (chi (hV (Sum.inr b'))) (chi v) • hV (Sum.inr b'))) := by
  classical
  obtain ⟨z, c, chart, b, Bb, chi, Bform0, rootRefl, lam, hBb, hchart_h, hchart_z, hc, hk,
    hB, hpairB, hfull_a, haction_a, hww2, hiso, hzz, hchi, hchi_r, hform_Bb, hnorm_a,
    hlast_a, haction_norm_a, hInside, hBform0, hform_h0, hform_hh0, hform_hz0, hform_zz0,
    hRootEq, hRootMem, hRootAction0, hRootSelf0, hxvec, hgenB0⟩ :=
    e6_raw_outside_unit_form_with_chart_basis_actual_inside_witnesslinks_independent_L
      hH hFix hcard S hS hΛa1 hΛa2 hML hCL hMK hCK e hML' ι φ hV αV hlin hrefl hpair hpairK
      hselII hfL hfK hclosL hclosK hconn hclosJ a ha_out
  let h' : Fin 6 → V := fun i => hV (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => αV (Sum.inl (e i))
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  have hLI : LinearIndependent (ZMod 3) h' := hselII.comp e e.injective
  have hpair' : ∀ i j, α' i (h' j) = cartanE6ModThree i j := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML']
    simp [cartanE6ModThree]
  have hlinL : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α' i v • h' i := by
    intro i v
    exact hlin (Sum.inl (e i)) v
  have hclosL' : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
  have hgenL : ∀ i, φL i ∈ ggAutomizer L Bs := by
    intro i
    rw [hclosL']
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hinv : ∀ i, φL i * φL i = 1 := by
    intro i
    have := (hrefl (Sum.inl (e i))).1
    simpa [φL, pow_two] using this
  obtain ⟨fK, hfK'⟩ := hfK
  have hFK_all : ∀ b' : Λa,
      (fK (MK.simple (Sum.inr b')) : MulAut ↥Bs) = φ (Sum.inr b') := by
    intro b'
    simpa using hfK' (Sum.inr b')
  have hmem_all : ∀ b' : Λa,
      φ (Sum.inr b') ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro b'
    apply Subgroup.mem_sup_right
    rw [← hFK_all b']
    exact (fK (MK.simple (Sum.inr b'))).2
  have hself_all : ∀ b' : Λa,
      αV (Sum.inr b') (hV (Sum.inr b')) = 2 := by
    intro b'
    have hp : αV (Sum.inr b') (hV (Sum.inr b')) =
        (CK (Sum.inr b') (Sum.inr b') : ZMod 3) := by
      simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr b') (Sum.inr b')
    rw [hp, hCK.1 (Sum.inr b')]
    rfl
  have hH2 : φ (Sum.inr a) * φ (Sum.inr a) = 1 := by
    have := (hrefl (Sum.inr a)).1
    simpa [pow_two] using this
  have hLNoncyclic : GGLNoncyclicInput := ggLNoncyclicInput_holds
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hAll : ∀ b' : Λa,
      (∀ v, αV (Sum.inr b') v = Bb (hV (Sum.inr b')) v) ∧
      CFSG.StandardType.E7F3.norm (chi (hV (Sum.inr b'))) = 2 ∧
      (∀ v, ggLin (p := 3) ι (φ (Sum.inr b')) v =
        v - pair (chi (hV (Sum.inr b'))) (chi v) • hV (Sum.inr b')) := by
    intro b'
    have hfull_b : ∀ v, αV (Sum.inr b') v = Bb (hV (Sum.inr b')) v :=
      e6_all_actual_reflections_share_first_outside_form hH hx hLNoncyclic ι Bform0 h' α' φL
        hLI hpair' hform_h0 hlinL hgenB0 hinv hgenL hclosL' rootRefl hRootMem
        hRootAction0 hRootSelf0 lam hxvec chart c hchart_h hBform0 hc b Bb hBb
        (φ (Sum.inr a)) (hV (Sum.inr a)) (αV (Sum.inr a)) (hmem_all a) hH2
        (hlin (Sum.inr a)) (hself_all a) hfull_a hk
        (φ (Sum.inr b')) (hV (Sum.inr b')) (αV (Sum.inr b')) (hmem_all b')
        (hlin (Sum.inr b')) (hself_all b')
    refine ⟨hfull_b, ?_, ?_⟩
    · rw [CFSG.StandardType.E7F3.norm,
        ← hform_Bb (hV (Sum.inr b')) (hV (Sum.inr b'))]
      rw [← hfull_b (hV (Sum.inr b'))]
      exact hself_all b'
    · intro v
      rw [hlin (Sum.inr b') v, hfull_b v, hform_Bb (hV (Sum.inr b')) v]
  refine ⟨z, c, chart, b, Bb, chi, Bform0, rootRefl, lam, ?_⟩
  exact ⟨hBb, hchart_h, hchart_z, hc, hk, hB, hpairB, hfull_a, haction_a, hww2, hiso,
    hzz, hchi, hchi_r, hform_Bb, hnorm_a, hlast_a, haction_norm_a, hInside,
    hBform0, hform_h0, hform_hh0, hform_hz0, hform_zz0, hRootEq, hRootMem,
    hRootAction0, hRootSelf0, hxvec, hgenB0, hAll⟩

end CFSG.StandardType

end

public section
namespace CFSG.StandardType

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open CFSG.StandardType.E7F3
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_actual_raw_seven_join_all_added_independent_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFix : GGTBFixInput)
    (hcard : Nat.card Bs = 3 ^ 7)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ) (hS : S.card = 2)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (hΛa1 : 1 ≤ Nat.card Λa) (hΛa2 : Nat.card Λa ≤ 3)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Λ)
    (hML' : ML = CoxeterMatrix.E₆.reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (hV : Λ ⊕ Λa → V)
    (αV : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - αV o w • hV o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hpair : ∀ i j : Λ,
      αV (Sum.inl i) (hV (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      αV (o.map Subtype.val id) (hV (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hselII : LinearIndependent (ZMod 3) (fun i : Λ => hV (Sum.inl i)))
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hconn : GGDeletedConnectedS ML S)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)))
    (a0 : Λa)
    (ha_out : hV (Sum.inr a0) ∉ Submodule.span (ZMod 3)
      (Set.range fun i : Λ => hV (Sum.inl i))) :
    CFSG.StandardType.GGWeylReflectionGroup 3
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨z, c, chart, b, Bb, chi, Bform0, rootRefl, lam,
    _hBb, _hchart_h, _hchart_z, _hc, _hk, hB, hpairB, _hfull_a, _haction_a,
    _hww2, _hiso, _hzz, hchi, _hchi_r, hform_Bb, _hnorm_a, _hlast_a,
    _haction_norm_a, hInside, _hBform0, _hform_h0, _hform_hh0, _hform_hz0,
    _hform_zz0, _hRootEq, _hRootMem, _hRootAction0, _hRootSelf0, _hxvec,
    _hgenB0, hAll⟩ :=
    e6_raw_all_added_unit_same_witness_independent_L hH hFix hcard S hS hΛa1 hΛa2 hML hCL hMK hCK
      e hML' ι φ hV αV hlin hrefl hpair hpairK hselII hfL hfK hclosL hclosK
      hconn hclosJ a0 ha_out
  have hspan_eq : Submodule.span (ZMod 3)
      (Set.range fun i : Fin 6 => hV (Sum.inl (e i))) =
      Submodule.span (ZMod 3) (Set.range fun i : Λ => hV (Sum.inl i)) := by
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  have ha_out6 : hV (Sum.inr a0) ∉ Submodule.span (ZMod 3)
      (Set.range fun i : Fin 6 => hV (Sum.inl (e i))) := by
    intro hmem
    exact ha_out (by rwa [hspan_eq] at hmem)
  have hSadd : ∀ a : Λa, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι (φ (Sum.inr a)) = reflPerm v hn := by
    intro a
    exact ⟨chi (hV (Sum.inr a)), (hAll a).2.1,
      witnessChart_conj_eq_reflPerm chi ι (φ (Sum.inr a)) (hV (Sum.inr a))
        (hAll a).2.2 (hAll a).2.1⟩
  have haction0 : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a0)) v =
      v - pair (chi (hV (Sum.inr a0))) (chi v) • hV (Sum.inr a0) :=
    (hAll a0).2.2
  exact e6_actual_seven_join_of_witness_chart chi ι S e φ hV αV hlin hclosL hclosK
    Bb hB hform_Bb (by simpa [CFSG.StandardType.E7F3.e] using hchi)
    a0 ha_out6 haction0 (hAll a0).2.1 hInside hSadd

end CFSG.StandardType
end

