module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBranch
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSpinor
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthALRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.StandardType

namespace NSJoin

open CFSG CFSG.Assembly
open CFSG.StandardType.OrthF3
open TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem nsOrth_refl_class {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (ι : Additive ↥Bs ≃+ V)
    {Q : QuadraticForm (ZMod 3) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : Subgroup (MulAut ↥Bs)}
    (hAO : ∀ g : V ≃ₗ[ZMod 3] V, (∃ a ∈ A, ggLin (p := 3) ι a = g) ↔ ∀ v, Q (g v) = Q v)
    {a : MulAut ↥Bs} (haA : a ∈ A) (ha : GGIsReflection 3 a) :
    ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c (ggLin (p := 3) ι a) := by
  haveI : FiniteDimensional (ZMod 3) V := Module.Finite.of_finite
  have hgO : ggLin (p := 3) ι a ∈ QuadraticMap.orthogonalGroup Q :=
    (QuadraticMap.mem_orthogonalGroup_iff).mpr ((hAO (ggLin (p := 3) ι a)).mp ⟨a, haA, rfl⟩)
  have hgr : GGLinRefl (ggLin (p := 3) ι a) :=
    (ggIsReflection_iff_ggLinRefl (p := 3) (by decide) ι a).mp ha
  exact (linRefl_iff_orthRefl (Q := Q) hQ hgO).mp hgr

theorem nsOrth_refl_class_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {c c' : ZMod 3} {g : V ≃ₗ[ZMod 3] V}
    (h : OrthReflOfNorm Q c g) (h' : OrthReflOfNorm Q c' g) : c = c' :=
  orthReflOfNorm_unique h h'

theorem nsOrth_weyl_generated {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylReflectionGroup p A) :
    A = Subgroup.closure {a | a ∈ A ∧ GGIsReflection p a} := by
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  apply le_antisymm
  · have hgen : Subgroup.closure (Set.range M.simple) = ⊤ :=
      M.toCoxeterSystem.subgroup_closure_range_simple
    let C : Subgroup ↥A :=
      (Subgroup.closure {a : MulAut ↥Bs | a ∈ A ∧ GGIsReflection p a}).comap A.subtype
    have hfac : Subgroup.comap (f : M.Group →* ↥A) C = ⊤ := by
      have hle : Subgroup.closure (Set.range M.simple) ≤
          Subgroup.comap (f : M.Group →* ↥A) C := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨i, rfl⟩
        exact (Subgroup.mem_comap).mpr ((Subgroup.mem_comap).mpr
          (Subgroup.subset_closure ⟨(f (M.simple i)).2, hf i⟩))
      rw [hgen] at hle
      exact le_antisymm le_top hle
    intro a ha
    have hx : (⟨a, ha⟩ : ↥A) ∈ C := by
      have hy : f.symm (⟨a, ha⟩ : ↥A) ∈ Subgroup.comap (f : M.Group →* ↥A) C := by
        rw [hfac]; exact Subgroup.mem_top _
      simpa using hy
    exact hx
  · exact (Subgroup.closure_le A).mpr (fun x hx => hx.1)

theorem nsOrth_automizer_le_induced {G : Type} [Group G] {L Bs : Subgroup G} :
    ggAutomizer L Bs ≤ ggInduced ⊤ Bs := by
  intro φ hφ
  rw [ggAutomizer_eq] at hφ
  change φ ∈ ggInduced L Bs at hφ
  obtain ⟨g, hgL, hgN, hgφ⟩ := hφ
  exact ⟨g, trivial, hgN, hgφ⟩

theorem nsOrth_reflConj_of_base
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦)
    {ιW : Type} (M : CoxeterMatrix ιW) (hM : GGIsWeylMatrix M)
    (hle : ∀ i j : ιW, i ≠ j → M.M i j ≤ 3)
    (f : M.Group ≃* ↥(ggAutomizer L Bs))
    (hf : ∀ i : ιW,
      GGIsReflection 3 ((f (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) :
    ggAutomizer L Bs = Subgroup.closure {a | a ∈ ggAutomizer L Bs ∧ GGIsReflection 3 a} ∧
      ∀ a ∈ ggAutomizer L Bs, ∀ b ∈ ggAutomizer L Bs, GGIsReflection 3 a →
        GGIsReflection 3 b → ∃ g ∈ ggAutomizer L Bs, b = g * a * g⁻¹ := by
  classical
  have hAind : ggAutomizer L Bs ≤ ggInduced ⊤ Bs := nsOrth_automizer_le_induced
  have hstar : GGBstar 3 B Bs := hcfg.1.1.2.1
  have hEl : IsElemAbelian 3 Bs := hstar.2.1
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  have hG2 : ¬ ∃ e : Fin 2 ≃ ιW, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, rfl⟩
    have hne : e 0 ≠ e 1 := by
      intro hh
      have hv := congrArg Fin.val (e.injective hh)
      norm_num at hv
    have h := hle (e 0) (e 1) hne
    have hlab : ((CoxeterMatrix.G₂).reindex e).M (e 0) (e 1) = 6 := by
      rw [CoxeterMatrix.reindex_apply]
      simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
    rw [hlab] at h
    omega
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  constructor
  · apply le_antisymm
    · have hgen : Subgroup.closure (Set.range M.simple) = ⊤ :=
        M.toCoxeterSystem.subgroup_closure_range_simple
      let C : Subgroup ↥A :=
        (Subgroup.closure {a : MulAut ↥Bs | a ∈ A ∧ GGIsReflection 3 a}).comap A.subtype
      have hfac : Subgroup.comap (f : M.Group →* ↥A) C = ⊤ := by
        have hle' : Subgroup.closure (Set.range M.simple) ≤
            Subgroup.comap (f : M.Group →* ↥A) C := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro _ ⟨i, rfl⟩
          exact (Subgroup.mem_comap).mpr ((Subgroup.mem_comap).mpr
            (Subgroup.subset_closure ⟨(f (M.simple i)).2, hf i⟩))
        rw [hgen] at hle'
        exact le_antisymm le_top hle'
      intro a ha
      have hx : (⟨a, ha⟩ : ↥A) ∈ C := by
        have hy : f.symm (⟨a, ha⟩ : ↥A) ∈ Subgroup.comap (f : M.Group →* ↥A) C := by
          rw [hfac]; exact Subgroup.mem_top _
        simpa using hy
      exact hx
    · exact (Subgroup.closure_le A).mpr (fun x hx => hx.1)
  · rintro a haA b hbA haR hbR
    have hroot : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G), p.Prime →
        p ≠ 2 → IsElemAbelian p Bs → GGNoTransvection p Bs →
        ∀ (A : Subgroup (MulAut ↥Bs)), A ≤ ggInduced ⊤ Bs →
        ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
        (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
        ∀ f : M.Group ≃* ↥A,
          (∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) →
        ∀ a : ↥A, GGIsReflection p (a : MulAut ↥Bs) →
          ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹) :=
      CFSG.StandardType.SecFiveRootRefl.ggSecFiveRootReflInput_holds
    obtain ⟨i, g, hai⟩ :=
      hroot G 3 Bs hp3 hp32 hEl hNT A hAind ιW M hM hG2 f hf ⟨a, haA⟩ haR
    obtain ⟨j, h, hbj⟩ :=
      hroot G 3 Bs hp3 hp32 hEl hNT A hAind ιW M hM hG2 f hf ⟨b, hbA⟩ hbR
    obtain ⟨w, hw⟩ := ggOrth_simple_conj M hM hle i j
    let uA : ↥A := f (h * w * g⁻¹)
    refine ⟨(uA : MulAut ↥Bs), uA.2, ?_⟩
    have hEq : (⟨b, hbA⟩ : ↥A) = uA * ⟨a, haA⟩ * uA⁻¹ := by
      rw [hbj, hai, hw]
      simp only [uA, map_mul, map_inv]
      group
    have := congrArg (Subtype.val) hEq
    simpa [uA] using this

theorem nsOrth_class_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3} {g : V ≃ₗ[ZMod 3] V}
    (h : OrthReflOfNorm Q c g) (e : V ≃ₗ[ZMod 3] V)
    (he : e ∈ QuadraticMap.orthogonalGroup Q) :
    OrthReflOfNorm Q c (e * g * e⁻¹) :=
  OrthReflOfNorm.conj h e he

end NSJoin

end CFSG.StandardType

end
