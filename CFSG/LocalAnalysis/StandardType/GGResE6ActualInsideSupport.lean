module

public import CFSG.LocalAnalysis.StandardType.GGResE6ActualSevenRootSupport
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGResE6Coordinates
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.Blueprint.Chevalley
public import CFSG.Assembly.E6FourCentMask
public import CFSG.Mathlib.Decide.Bounded
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
public import CFSG.LocalAnalysis.StandardType.GGResE6ActualSevenRootSupport
public import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import Mathlib.LinearAlgebra.Reflection
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CFSG.LocalAnalysis.StandardType.GGE6DepKNoTv
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan


public section

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open CFSG.StandardType.E6InsideSpanNormalizer
open CFSG.StandardType.E6Seven
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}

@[expose] def Hcomb {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (u : Fin 6 → ZMod 3) : V :=
  Fintype.linearCombination (ZMod 3) h u

theorem e6_actual_insideU_membership_of_literal_axis
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {φL : Fin 6 → MulAut ↥Bs}
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    {F : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    (hFjoin : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hselfF : aa ha = 2)
    (hroot : ∃ m : Fin 72, Hcomb h (rootVec m) = ha) :
    F ∈ ggAutomizer L Bs := by
  classical
  obtain ⟨m, hm⟩ := hroot
  let R : MulAut ↥Bs := e6RootRefl φL 0 (rootPath m)
  have hRmem : R ∈ ggAutomizer L Bs := e6RootRefl_mem hgenL 0 (rootPath m)
  have hB0 : Bform (h 0) (h 0) = 2 := by
    rw [hB 0, hpair 0 0]
    decide +kernel
  have hUnit : ∀ i : Fin 6, Hcomb h (unitRoot i) = h i := by
    intro i
    rw [Hcomb, unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hBroot : ∀ m : Fin 72,
      Bform (Hcomb h (rootVec m)) (Hcomb h (rootVec m)) = 2 := by
    intro m
    have hg0 : ggLin (p := 3) ι (e6WordAut φL (rootPath m)) (h 0) =
        Hcomb h (rootVec m) := by
      rw [← hUnit 0]
      change ggLin (p := 3) ι (e6WordAut φL (rootPath m))
          (Fintype.linearCombination (ZMod 3) h (unitRoot 0)) =
        Hcomb h (rootVec m)
      rw [e6WordAut_act_linearCombination (h := h) (α := α)
        (hpair := hpair) (hlin := hlin) (φL := φL) (w := rootPath m)
        (u := unitRoot 0), rootVec_applyWord m]
      rw [Hcomb]
    rw [← hg0]
    rw [e6WordAut_isometry Bform φL ι hgenB]
    exact hB0
  have hRlin0 : ∀ v, ggLin (p := 3) ι R v =
      v - Bform (Hcomb h (rootVec m)) v • Hcomb h (rootVec m) := by
    intro v
    exact e6RootRefl_apply_full Bform h α hpair hB hlin hgenB hinv 0
      (rootPath m) (rootVec m) (rootVec_applyWord m) v
  have hRlin : ∀ v, ggLin (p := 3) ι R v = v - (Bform ha) v • ha := by
    intro v
    rw [hRlin0 v, ← hm]
  have hselfR : (Bform ha) ha = 2 := by
    rw [← hm]
    exact hBroot m
  exact e6_actual_insideU_membership_of_same_coroot hH ι hFjoin hRmem hFlin hRlin
    hselfF hselfR

theorem e6_actual_literal_axis_of_finite_test
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {φL : Fin 6 → MulAut ↥Bs}
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    {F : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    {w : Fin 6 → ZMod 3}
    (hha : ha = Hcomb h w)
    (hnorm : norm w ≠ 0)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hselfF : aa ha = 2)
    (hFrestrict : ∀ u : Fin 6 → ZMod 3,
      ggLin (p := 3) ι F (Hcomb h u) = Hcomb h (refl w u))
    (hconj : ∀ i j : Fin 6, ∃ m : Fin 72,
      ggLin (p := 3) ι (F * φL i * F⁻¹) (Hcomb h (unitRoot j)) =
        Hcomb h (rootVec m)) :
    ∃ m : Fin 72, Hcomb h (rootVec m) = ha := by
  classical
  have hUnit : ∀ i : Fin 6, Hcomb h (unitRoot i) = h i := by
    intro i
    rw [Hcomb, unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hC : C = cartanE6ModThree := by
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  have hUnit' : ∀ i : Fin 6,
      Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i := by
    intro i
    simpa [Hcomb] using hUnit i
  have hH_s : ∀ (i : Fin 6) (u : Fin 6 → ZMod 3),
      Hcomb h (s i u) = Hcomb h u - (cartanE6ModThree *ᵥ u) i • h i := by
    intro i u
    change Fintype.linearCombination (ZMod 3) h (s i u) =
      Fintype.linearCombination (ZMod 3) h u -
        (cartanE6ModThree *ᵥ u) i • h i
    rw [s, map_sub, map_smul, hUnit' i]
    simp only [Cmul_eq_mulVec, hC]
  have hφH : ∀ (i : Fin 6) (u : Fin 6 → ZMod 3),
      ggLin (p := 3) ι (φL i) (Hcomb h u) = Hcomb h (s i u) := by
    intro i u
    change ggLin (p := 3) ι (φL i) (Fintype.linearCombination (ZMod 3) h u) =
      Fintype.linearCombination (ZMod 3) h (s i u)
    rw [hlin i (Fintype.linearCombination (ZMod 3) h u),
      apply_linearCombination_eq_cartanE6ModThree (h := h) (α := α) hpair i u]
    exact (hH_s i u).symm
  have hF2 : ∀ v, ggLin (p := 3) ι F (ggLin (p := 3) ι F v) = v := by
    intro v
    rw [hFlin (ggLin (p := 3) ι F v), hFlin v, map_sub, map_smul, hselfF]
    module
  have hFinv : F⁻¹ = F := by
    apply inv_eq_of_mul_eq_one_right
    apply ggLin_injective (p := 3) ι
    ext v
    rw [map_mul, LinearEquiv.mul_apply, hF2]
    have hone : ggLin (p := 3) ι (1 : MulAut ↥Bs) = 1 := map_one _
    rw [hone]
    rw [show (1 : V ≃ₗ[ZMod 3] V) = LinearEquiv.refl (ZMod 3) V from rfl]
    rfl
  have hconj_apply : ∀ (i : Fin 6) (u : Fin 6 → ZMod 3),
      ggLin (p := 3) ι (F * φL i * F⁻¹) (Hcomb h u) =
        Hcomb h (refl w (s i (refl w u))) := by
    intro i u
    calc
      ggLin (p := 3) ι (F * φL i * F⁻¹) (Hcomb h u)
          = ggLin (p := 3) ι F (ggLin (p := 3) ι (φL i)
              (ggLin (p := 3) ι F⁻¹ (Hcomb h u))) := by
              simp only [map_mul, LinearEquiv.mul_apply]
      _ = ggLin (p := 3) ι F (ggLin (p := 3) ι (φL i)
              (Hcomb h (refl w u))) := by rw [hFinv, hFrestrict u]
      _ = ggLin (p := 3) ι F (Hcomb h (s i (refl w u))) := by
              rw [hφH i (refl w u)]
      _ = Hcomb h (refl w (s i (refl w u))) := by
              rw [hFrestrict (s i (refl w u))]
  have hpoint : ∀ i j : Fin 6,
      ∃ m : Fin 72, rootVec m = refl w (s i (refl w (unitRoot j))) := by
    intro i j
    obtain ⟨m, hm⟩ := hconj i j
    refine ⟨m, ?_⟩
    apply hLI.fintypeLinearCombination_injective
    rw [hconj_apply i (unitRoot j)] at hm
    exact hm.symm
  obtain ⟨m, hm⟩ := (refl_test_iff w hnorm).mp hpoint
  refine ⟨m, ?_⟩
  rw [hm]
  exact hha.symm

theorem e6_actual_insideU_membership_of_finite_test
    (hH : GGResHyp 3 B Bs x L D J y K)
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
    {F : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    (hFjoin : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hselfF : aa ha = 2)
    {w : Fin 6 → ZMod 3}
    (hha : ha = Hcomb h w)
    (hnorm : norm w ≠ 0)
    (hFrestrict : ∀ u : Fin 6 → ZMod 3,
      ggLin (p := 3) ι F (Hcomb h u) = Hcomb h (refl w u))
    (hconj : ∀ i j : Fin 6, ∃ m : Fin 72,
      ggLin (p := 3) ι (F * φL i * F⁻¹) (Hcomb h (unitRoot j)) =
        Hcomb h (rootVec m)) :
    F ∈ ggAutomizer L Bs := by
  obtain ⟨m, hm⟩ := e6_actual_literal_axis_of_finite_test hLI hpair hlin hha hnorm
    hFlin hselfF hFrestrict hconj
  exact e6_actual_insideU_membership_of_literal_axis hH hpair hB hlin hgenB hinv hgenL
    hFjoin hFlin hselfF ⟨m, hm⟩

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open CFSG.StandardType.E6InsideSpanNormalizer
open CFSG.StandardType.E6Seven
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}

theorem s_rootVec_mem : ∀ (i : Fin 6) (m : Fin 72),
    ∃ m' : Fin 72, s i (rootVec m) = rootVec m' := by
  decide +kernel

theorem unitRoot_mem_rootVec : ∀ j : Fin 6,
    ∃ m : Fin 72, rootVec m = unitRoot j := by
  decide +kernel

theorem e6_AL_preserves_rootVec
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {φL : Fin 6 → MulAut ↥Bs}
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hinv : ∀ i, φL i * φL i = 1)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer L Bs) (m : Fin 72) :
    ∃ m' : Fin 72,
      ggLin (p := 3) ι ψ (Fintype.linearCombination (ZMod 3) h (rootVec m)) =
        Fintype.linearCombination (ZMod 3) h (rootVec m') := by
  classical
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  have hC : C = cartanE6ModThree := by
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  have hUnit : ∀ i : Fin 6, H (unitRoot i) = h i := by
    intro i
    change Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i
    rw [unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hUnit' : ∀ i : Fin 6,
      Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i := by
    intro i
    simpa [H] using hUnit i
  have hH_s : ∀ (i : Fin 6) (u : Fin 6 → ZMod 3),
      H (s i u) = H u - (cartanE6ModThree *ᵥ u) i • h i := by
    intro i u
    change Fintype.linearCombination (ZMod 3) h (s i u) =
      Fintype.linearCombination (ZMod 3) h u -
        (cartanE6ModThree *ᵥ u) i • h i
    rw [s, map_sub, map_smul, hUnit' i]
    simp only [Cmul_eq_mulVec, hC]
  have hφH : ∀ (i : Fin 6) (u : Fin 6 → ZMod 3),
      ggLin (p := 3) ι (φL i) (H u) = H (s i u) := by
    intro i u
    change ggLin (p := 3) ι (φL i) (Fintype.linearCombination (ZMod 3) h u) =
      Fintype.linearCombination (ZMod 3) h (s i u)
    rw [hlin i (Fintype.linearCombination (ZMod 3) h u),
      apply_linearCombination_eq_cartanE6ModThree (h := h) (α := α) hpair i u]
    exact (hH_s i u).symm
  let Good : MulAut ↥Bs → Prop := fun ψ =>
    (∀ m : Fin 72, ∃ m' : Fin 72, ggLin (p := 3) ι ψ (H (rootVec m)) = H (rootVec m')) ∧
    (∀ m : Fin 72, ∃ m' : Fin 72, ggLin (p := 3) ι ψ⁻¹ (H (rootVec m)) = H (rootVec m'))
  have hgenGood : ∀ i : Fin 6, Good (φL i) := by
    intro i
    constructor
    · intro m
      obtain ⟨m', hm'⟩ := s_rootVec_mem i m
      refine ⟨m', ?_⟩
      rw [hφH i (rootVec m), hm']
    · intro m
      have hi : (φL i)⁻¹ = φL i := inv_eq_of_mul_eq_one_right (hinv i)
      obtain ⟨m', hm'⟩ := s_rootVec_mem i m
      refine ⟨m', ?_⟩
      rw [hi, hφH i (rootVec m), hm']
  have hclosureGood : ∀ ψ ∈ Subgroup.closure (Set.range φL), Good ψ := by
    intro ψ hψ
    refine Subgroup.closure_induction
      (p := fun ψ _ => Good ψ) ?_ ?_ ?_ ?_ hψ
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      exact hgenGood i
    · constructor
      · intro m
        exact ⟨m, by simp⟩
      · intro m
        exact ⟨m, by simp⟩
    · intro ψ₁ ψ₂ h₁ h₂ hg₁ hg₂
      constructor
      · intro m
        obtain ⟨m₁, hm₁⟩ := hg₂.1 m
        obtain ⟨m₂, hm₂⟩ := hg₁.1 m₁
        exact ⟨m₂, by rw [map_mul, LinearEquiv.mul_apply, hm₁, hm₂]⟩
      · intro m
        obtain ⟨m₁, hm₁⟩ := hg₁.2 m
        obtain ⟨m₂, hm₂⟩ := hg₂.2 m₁
        exact ⟨m₂, by rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply, hm₁, hm₂]⟩
    · intro ψ hψ hg
      exact ⟨hg.2, hg.1⟩
  have hψclosure : ψ ∈ Subgroup.closure (Set.range φL) := by
    rwa [← hclosL]
  exact (hclosureGood ψ hψclosure).1 m

end CFSG.StandardType

end

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open CFSG.StandardType.E6InsideSpanNormalizer
open CFSG.StandardType.E6Seven

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}

theorem e6_hFrestrict_of_restriction
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {h : Fin 6 → V} {F : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    {s : Fin 6 → ZMod 3} {mu : ZMod 3}
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hha : ha = Fintype.linearCombination (ZMod 3) h s)
    (hselfF : aa ha = 2)
    (hres : ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) = mu * e6dot (Cmul s) u) :
    ∀ u : Fin 6 → ZMod 3,
      ggLin (p := 3) ι F (Fintype.linearCombination (ZMod 3) h u) =
        Fintype.linearCombination (ZMod 3) h (refl s u) := by
  classical
  have hself_mu : mu * norm s = 2 := by
    have h := hselfF
    rw [hha, hres s, e6dot_Cmul_self] at h
    exact h
  have hnorm : norm s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hself_mu
    exact (by decide : (2 : ZMod 3) ≠ 0) hself_mu.symm
  have hmu : mu = (2 : ZMod 3) * (norm s)⁻¹ := by
    calc
      mu = mu * norm s * (norm s)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hnorm, mul_one]
      _ = (2 : ZMod 3) * (norm s)⁻¹ := by rw [hself_mu]
  intro u
  rw [hFlin (Fintype.linearCombination (ZMod 3) h u)]
  change Fintype.linearCombination (ZMod 3) h u - aa (Fintype.linearCombination (ZMod 3) h u) • ha =
    Fintype.linearCombination (ZMod 3) h (refl s u)
  rw [hres u, hha, hmu]
  rw [refl_apply]
  change Fintype.linearCombination (ZMod 3) h u -
      (((2 : ZMod 3) * (norm s)⁻¹) * e6dot (Cmul s) u) •
        Fintype.linearCombination (ZMod 3) h s =
    Fintype.linearCombination (ZMod 3) h
      (u - ((((2 : ZMod 3) * (norm s)⁻¹) * (∑ i, Cmul s i * u i)) • s))
  rw [map_sub, map_smul]
  congr 1

theorem e6_actual_normalizes_L_of_fix_x
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {F : MulAut ↥Bs} (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFx : F ⟨x, hx⟩ = ⟨x, hx⟩) :
    F ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := by
  have htop : F ∈ ggAutomizer ⊤ Bs :=
    (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)) hF
  apply ggAutomizer_mem_normalizer_of_zpowers hLNoncyclic hH.1.1 hx htop
  rw [hFx]
  exact Subgroup.mem_zpowers _

theorem e6_actual_normalizes_L_of_restriction
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Fin 6 → V)
    {F : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (s : Fin 6 → ZMod 3) (mu lam : ZMod 3)
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r)
    (hres : ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) = mu * e6dot (Cmul s) u) :
    F ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := by
  have hax : aa (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
    rw [hxvec, map_smul, hres r, e6dot_Cmul_swap s r, Cmul_r]
    simp [e6dot]
  apply e6_actual_normalizes_L_of_fix_x hH hx hLNoncyclic hF
  apply (ggLin_fix_iff (p := 3) ι F ⟨x, hx⟩).mpr
  rw [hlin, hax, zero_smul, sub_zero]

public theorem e6_actual_insideU_membership_original
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
    {F : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    (hFjoin : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hselfF : aa ha = 2)
    {s : Fin 6 → ZMod 3} {mu lam : ZMod 3}
    (hha : ha = Fintype.linearCombination (ZMod 3) h s)
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r)
    (hres : ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) = mu * e6dot (Cmul s) u) :
    F ∈ ggAutomizer L Bs := by
  classical
  have hself_mu : mu * norm s = 2 := by
    have h := hselfF
    rw [hha, hres s, e6dot_Cmul_self] at h
    exact h
  have hnorm : norm s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hself_mu
    exact (by decide : (2 : ZMod 3) ≠ 0) hself_mu.symm
  have hFrestrict : ∀ u : Fin 6 → ZMod 3,
      ggLin (p := 3) ι F (Fintype.linearCombination (ZMod 3) h u) =
        Fintype.linearCombination (ZMod 3) h (refl s u) :=
    e6_hFrestrict_of_restriction hFlin hha hselfF hres
  have hNorm : F ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    e6_actual_normalizes_L_of_restriction hH hx hLNoncyclic ι h hFjoin hFlin s mu lam hxvec hres
  have hconj : ∀ i j : Fin 6, ∃ m : Fin 72,
      ggLin (p := 3) ι (F * φL i * F⁻¹)
        (Fintype.linearCombination (ZMod 3) h (unitRoot j)) =
        Fintype.linearCombination (ZMod 3) h (rootVec m) := by
    intro i j
    have hmem : F * φL i * F⁻¹ ∈ ggAutomizer L Bs :=
      (Subgroup.mem_normalizer_iff.mp hNorm (φL i)).mp (hgenL i)
    obtain ⟨m0, hm0⟩ := unitRoot_mem_rootVec j
    obtain ⟨m1, hm1⟩ := e6_AL_preserves_rootVec hpair hlin hinv hclosL hmem m0
    refine ⟨m1, ?_⟩
    rw [← hm0]
    exact hm1
  exact e6_actual_insideU_membership_of_finite_test hH hLI hpair hB hlin hgenB hinv hgenL
    hFjoin hFlin hselfF hha hnorm hFrestrict hconj

end CFSG.StandardType

public section
namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit CFSG.StandardType
open scoped Matrix


theorem e6_actualL_isometry_of_generator_isometry
    {G : Type} [Group G] {Bs L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (Bform : LinearMap.BilinForm (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs)
    (hgenB : ∀ i u v, Bform (ggLin (p := 3) ι (φL i) u)
      (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    {F : MulAut ↥Bs} (hF : F ∈ ggAutomizer L Bs) :
    ∀ u v, Bform (ggLin (p := 3) ι F u) (ggLin (p := 3) ι F v) = Bform u v := by
  rw [hclosL] at hF
  refine Subgroup.closure_induction
    (p := fun F _ => ∀ u v, Bform (ggLin (p := 3) ι F u)
      (ggLin (p := 3) ι F v) = Bform u v) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨i, rfl⟩
    exact hgenB i
  · intro u v
    simp
  · intro F H hF hH hFi hHi u v
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFi, hHi]
  · intro F hF hi u v
    have hh := hi (ggLin (p := 3) ι F⁻¹ u) (ggLin (p := 3) ι F⁻¹ v)
    have hu : ggLin (p := 3) ι F (ggLin (p := 3) ι F⁻¹ u) = u := by
      rw [map_inv]
      exact (ggLin (p := 3) ι F).apply_symm_apply u
    have hv : ggLin (p := 3) ι F (ggLin (p := 3) ι F⁻¹ v) = v := by
      rw [map_inv]
      exact (ggLin (p := 3) ι F).apply_symm_apply v
    rw [hu, hv] at hh
    exact hh.symm

theorem e6_actual_inside_unit_functional_from_original
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
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2)
    (s : Fin 6 → ZMod 3) (hws : w = Fintype.linearCombination (ZMod 3) h s) :
    F ∈ ggAutomizer L Bs ∧ Bform w w = 2 ∧ ∀ v, aa v = Bform w v := by
  obtain ⟨mu, hresB⟩ := e6_restriction_proportional_sameWitness hH ι h α Bform
    rootRefl hRootMem hRootAction hRootSelf F w aa hF hFlin hself
  have hres : ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) = mu * e6dot (Cmul s) u := by
    intro u
    rw [hresB u, hws, e6_Bform_H_H_eq_e6dot hpair hB u s]
  have hself_mu : mu * norm s = 2 := by
    have hh := hself
    rw [hws, hres s, e6dot_Cmul_self] at hh
    exact hh
  have hnorm : norm s ≠ 0 := by
    intro heq
    rw [heq, mul_zero] at hself_mu
    exact (by decide : (2 : ZMod 3) ≠ 0) hself_mu.symm
  have hFrestrict := e6_hFrestrict_of_restriction hFlin hws hself hres
  have hNorm := e6_actual_normalizes_L_of_restriction hH hx hLNoncyclic ι h
    hF hFlin s mu lam hxvec hres
  have hconj : ∀ i j : Fin 6, ∃ m : Fin 72,
      ggLin (p := 3) ι (F * φL i * F⁻¹)
        (Fintype.linearCombination (ZMod 3) h (unitRoot j)) =
        Fintype.linearCombination (ZMod 3) h (rootVec m) := by
    intro i j
    have hmem : F * φL i * F⁻¹ ∈ ggAutomizer L Bs :=
      (Subgroup.mem_normalizer_iff.mp hNorm (φL i)).mp (hgenL i)
    obtain ⟨m0, hm0⟩ := unitRoot_mem_rootVec j
    obtain ⟨m1, hm1⟩ := e6_AL_preserves_rootVec hpair hlin hinv hclosL hmem m0
    exact ⟨m1, by rw [← hm0]; exact hm1⟩
  obtain ⟨m, hm⟩ := e6_actual_literal_axis_of_finite_test hLI hpair hlin
    hws hnorm hFlin hself hFrestrict hconj
  have hww : Bform w w = 2 := by
    rw [← hm]
    exact hRootSelf m
  have hFL : F ∈ ggAutomizer L Bs :=
    e6_actual_insideU_membership_original hH hx hLNoncyclic hLI hpair hB hlin
      hgenB hinv hgenL hclosL hF hFlin hself hws hxvec hres
  have hiso := e6_actualL_isometry_of_generator_isometry ι Bform φL hgenB hclosL hFL
  refine ⟨hFL, hww, fun v => ?_⟩
  have hh := hiso w v
  rw [hFlin w, hFlin v, hself] at hh
  have hneg : w - (2 : ZMod 3) • w = -w := by module
  rw [hneg] at hh
  simp only [map_neg, map_sub, map_smul, LinearMap.neg_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hh
  rw [hww] at hh
  have heq : aa v * (2 : ZMod 3) = Bform w v * 2 := by linear_combination hh
  exact mul_right_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) heq

end CFSG.StandardType.E6Seven
end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}
theorem e6_actual_originalL_six_independent_join
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K (fun l _ => l) ggTypLE6)
    (hcard : Nat.card Bs = 3 ^ 6) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hMLweyl, hCL, hMKweyl, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hE6 : GGIsTypeE6 ML := htyp
  obtain ⟨e, hML⟩ := hE6
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  have hgenL : ∀ i, φL i ∈ ggAutomizer L Bs := by
    intro i
    rw [hclosL]
    exact Subgroup.subset_closure ⟨e i, rfl⟩
  have hinv : ∀ i, φL i * φL i = 1 := by
    intro i
    simpa [pow_two] using (hrefl (Sum.inl (e i))).1
  obtain ⟨c0, ec, hs, hex, heh, heact⟩ :=
    e6_actual_independent_six_chart hH hlin hpair hCL hclosL e hML hsel hcard
  have hact : ∀ i v, ec (ggLin (p := 3) ι (φL i) v) = s i (ec v) := by
    intro i v
    rw [heact i v, e6ChartSum i (ec v)]
    rfl
  have hadd : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer L Bs := by
    intro a
    have hφa : φ (Sum.inr a) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
      apply Subgroup.mem_sup_right
      rw [hclosK]
      exact Subgroup.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)
    have hlinA : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v =
        v - α (Sum.inr a) v • h (Sum.inr a) := hlin (Sum.inr a)
    have hselfa : α (Sum.inr a) (h (Sum.inr a)) = 2 := by
      have h' : α (Sum.inr a) (h (Sum.inr a)) =
          (CK (Sum.inr a) (Sum.inr a) : ZMod 3) := by
        simpa using hpairK (Sum.inr a) (Sum.inr a)
      rw [h', hCK.1]
      norm_num
    exact e6_added_mem_of_chart hH hgenL hinv ec hact hφa hlinA hselfa
  have hKL : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    rw [hclosK]
    rw [Subgroup.closure_le]
    rintro ψ (⟨j, rfl⟩ | ⟨a, rfl⟩)
    · rw [hclosL]
      exact Subgroup.subset_closure ⟨j.1, rfl⟩
    · exact hadd a
  have hjoin : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizer L Bs :=
    sup_eq_left.mpr hKL
  have hW : GGWeylReflectionGroup 3 (ggAutomizer L Bs) := by
    refine ⟨Λ, ML, hMLweyl, fL, ?_⟩
    intro i
    rw [hfL i]
    exact hrefl (Sum.inl i)
  rw [hjoin]
  exact hW

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open CFSG.StandardType.E6InsideSpanNormalizer
open CFSG.StandardType.E6Seven
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}

theorem e6_all_added_inside_join
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
    {ΛJ : Type} [Fintype ΛJ]
    {φJ : ΛJ → MulAut ↥Bs} (hJmem : ∀ j, φJ j ∈ ggAutomizer L Bs)
    {Λa : Type} [Fintype Λa]
    {φK : Λa → MulAut ↥Bs}
    (hKgen : ggAutomizer K Bs = Subgroup.closure (Set.range φJ ∪ Set.range φK))
    (hadd : ∀ a : Λa,
      ∃ (ha : V) (aa : Module.Dual (ZMod 3) V) (s : Fin 6 → ZMod 3) (mu : ZMod 3),
        ha = Fintype.linearCombination (ZMod 3) h s ∧
        (∀ v, ggLin (p := 3) ι (φK a) v = v - aa v • ha) ∧
        aa ha = 2 ∧
        (∀ u : Fin 6 → ZMod 3,
          aa (Fintype.linearCombination (ZMod 3) h u) = mu * e6dot (Cmul s) u))
    {lam : ZMod 3}
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r)
    (hWeylL : GGWeylReflectionGroup 3 (ggAutomizer L Bs)) :
    ggAutomizer K Bs ≤ ggAutomizer L Bs ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizer L Bs ∧
      GGWeylReflectionGroup 3
        (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hAddedMem : ∀ a : Λa, φK a ∈ ggAutomizer L Bs := by
    intro a
    obtain ⟨ha, aa, s, mu, hha, hFlin, hself, hres⟩ := hadd a
    have hFjoin : φK a ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
      apply Subgroup.mem_sup_right
      rw [hKgen]
      exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
    exact e6_actual_insideU_membership_original hH hx hLNoncyclic hLI hpair hB hlin
      hgenB hinv hgenL hclosL hFjoin hFlin hself hha hxvec hres
  have hKleL : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    rw [hKgen]
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rcases hx with ⟨j, rfl⟩
      exact hJmem j
    · rcases hx with ⟨a, rfl⟩
      exact hAddedMem a
  have hjoin : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizer L Bs :=
    sup_eq_left.mpr hKleL
  exact ⟨hKleL, hjoin, by simpa [hjoin] using hWeylL⟩

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent



theorem e6_raw_all_added_inside_join
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
    (htyp : GGIsTypeE6 ML)
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
    (hsel : LinearIndependent (ZMod 3) (fun i : Λ => hV (Sum.inl i)))
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
    (hallinside : ∀ a : Λa,
      hV (Sum.inr a) ∈ Submodule.span (ZMod 3)
        (Set.range fun i : Λ => hV (Sum.inl i))) :
    ggAutomizer K Bs ≤ ggAutomizer L Bs ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizer L Bs ∧
      GGWeylReflectionGroup 3
        (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨e, hML'⟩ := htyp
  let h' : Fin 6 → V := fun i => hV (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => αV (Sum.inl (e i))
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLI : LinearIndependent (ZMod 3) h' := hsel.comp e e.injective
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
  obtain ⟨z, c, chart, Bform, hchart_h, hchart_z, hform_h, hform_hh, hform_hz, hform_zz,
    hBform, hRootMem, hRootAction, hRootSelf⟩ :=
    e6_raw_chart_root_actions hML hCL ι φ hV αV hlin hsel hpair hrefl hclosL e hML' hcard
  have hsymm : (gram7 cartanE6ModThree c 0).IsSymm := by
    apply gram7_symm
    apply Matrix.IsSymm.ext
    intro i j
    exact (cartanE6ModThree_symm i j).symm
  have hdiag : ∀ i : Fin 6, gram7 cartanE6ModThree c 0 i.castSucc i.castSucc = 2 := by
    intro i
    rw [gram7_castSucc_castSucc]
    fin_cases i <;> rfl
  have hgenB : ∀ i u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v := by
    intro i u v
    rw [hBform]
    exact chart_generator_invariant h' α' φL ι hlinL chart c 0 hchart_h
      (by intro j; rw [← hBform]; exact hform_h j) hsymm hdiag i u v
  obtain ⟨lam, hxvec⟩ :=
    e6_raw_radical_alignment hFix hH hcard hML hCL ι φ hV αV hlin hsel hpair hclosL e hML'
      hΛa1
  obtain ⟨fL, hfL⟩ := hfL
  have hWeylL : GGWeylReflectionGroup 3 (ggAutomizer L Bs) := by
    refine ⟨Λ, ML, hML, fL, ?_⟩
    intro i
    rw [hfL i]
    exact hrefl (Sum.inl i)
  have hJmem : ∀ j : {j : Λ // j ∉ S}, φ (Sum.inl j.val) ∈ ggAutomizer L Bs := by
    intro j
    rw [hclosL]
    exact Subgroup.subset_closure ⟨j.val, rfl⟩
  have hKgen : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j.val)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)) := by
    simpa using hclosK
  have hadd : ∀ a : Λa,
      ∃ (ha : V) (aa : Module.Dual (ZMod 3) V) (s : Fin 6 → ZMod 3) (mu : ZMod 3),
        ha = Fintype.linearCombination (ZMod 3) h' s ∧
        (∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v = v - aa v • ha) ∧
        aa ha = 2 ∧
        (∀ u : Fin 6 → ZMod 3,
          aa (Fintype.linearCombination (ZMod 3) h' u) = mu * e6dot (Cmul s) u) := by
    intro a
    have hspan := hallinside a
    rw [Submodule.mem_span_range_iff_exists_fun] at hspan
    obtain ⟨s, hs⟩ := hspan
    let s' : Fin 6 → ZMod 3 := fun i => s (e i)
    let ha : V := hV (Sum.inr a)
    let aa : Module.Dual (ZMod 3) V := αV (Sum.inr a)
    have hsum : Fintype.linearCombination (ZMod 3) h' s' = hV (Sum.inr a) := by
      rw [Fintype.linearCombination_apply]
      rw [Fintype.sum_equiv e (fun i : Fin 6 => s (e i) • h' i)
        (fun j : Λ => s j • hV (Sum.inl j)) (by intro i; rfl)]
      exact hs
    have hha : ha = Fintype.linearCombination (ZMod 3) h' s' := by
      dsimp [ha]
      exact hsum.symm
    have hFlin : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v = v - aa v • ha := by
      intro v
      exact hlin (Sum.inr a) v
    have hself : aa ha = 2 := by
      dsimp [aa, ha]
      have hp : αV (Sum.inr a) (hV (Sum.inr a)) =
          (CK (Sum.inr a) (Sum.inr a) : ZMod 3) := by
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a) (Sum.inr a)
      rw [hp, hCK.1 (Sum.inr a)]
      rfl
    have hFjoin : φ (Sum.inr a) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
      apply Subgroup.mem_sup_right
      rw [hKgen]
      exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
    obtain ⟨mu, hresB⟩ := e6_restriction_proportional_sameWitness hH ι h' α' Bform
      (fun m => e6RootRefl φL 0 (rootPath m)) hRootMem hRootAction hRootSelf
      (φ (Sum.inr a)) ha aa hFjoin hFlin hself
    refine ⟨ha, aa, s', mu, hha, hFlin, hself, ?_⟩
    intro u
    rw [hresB u, hha, e6_Bform_H_H_eq_e6dot hpair' hform_h u s']
  have hLNoncyclic : GGLNoncyclicInput := ggLNoncyclicInput_holds
  exact e6_all_added_inside_join hH hx hLNoncyclic hLI hpair' hform_h hlinL hgenB hinv
    hgenL hclosL' hJmem hKgen hadd hxvec hWeylL

end CFSG.StandardType

end

