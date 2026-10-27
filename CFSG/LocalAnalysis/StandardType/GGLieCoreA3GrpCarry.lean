module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.LocalAnalysis.StandardType.GGKGOrthPairs
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped commutatorElement

private theorem ggLieGC_e6_symmetrizer (i : Fin (langTag .E6).rank) :
    (langTag .E6).symmetrizer i i = 1 := by
  simp only [langTag, Tag.symmetrizer]
  exact Matrix.one_apply_eq i

private theorem ggLieGC_e6_neighbor (j : Fin (langTag .E6).rank) :
    ∃ i, (langTag .E6).cartan j i = -1 := by
  simp only [langTag]
  fin_cases j <;> decide

private theorem ggLieGC_exists_orthogonal_minus_one
    {γ : Fin (langTag .E6).rank → ℤ}
    (hγ : IsRoot (langTag .E6) γ) :
    ∃ ε', IsRoot (langTag .E6) ε' ∧ iform γ ε' = -1 := by
  induction hγ with
  | basis j =>
    obtain ⟨i, hi⟩ := ggLieGC_e6_neighbor j
    refine ⟨Pi.single i 1, isRoot_single (langTag .E6) i, ?_⟩
    rw [CFSG.LieType.Steinberg.Adjoint.iform_single_left, ggLieGC_e6_symmetrizer j, one_mul,
      Finset.sum_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]
    exact hi
  | @reflect i v hv ih =>
    obtain ⟨ε', hε', hif⟩ := ih
    refine ⟨reflect (langTag .E6) i ε', IsRoot.reflect i hε', ?_⟩
    rw [CFSG.LieType.Steinberg.Adjoint.iform_reflect]
    exact hif

private theorem ggLieGC_root_pair
    {γ : Fin (langTag .E6).rank → ℤ} (hγ : IsRoot (langTag .E6) γ) :
    ∃ δ ε : Fin (langTag .E6).rank → ℤ,
      IsRoot (langTag .E6) δ ∧ IsRoot (langTag .E6) ε ∧ δ ≠ ε ∧ δ + ε = γ ∧
        iform δ ε = -1 := by
  obtain ⟨ε', hε', hif⟩ := ggLieGC_exists_orthogonal_minus_one hγ
  have hτ : ∀ i : Fin (langTag .E6).rank, (langTag .E6).symmetrizer i i = 1 :=
    ggLieGC_e6_symmetrizer
  have hne : γ ≠ -ε' := by
    intro he
    have h2 : iform γ ε' = -2 := by
      rw [he, CFSG.LieType.Chevalley.SimplyLacedCover.iform_neg_left,
        CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hε']
    omega
  have hδ : IsRoot (langTag .E6) (γ + ε') :=
    isRoot_add_of_iform_neg hγ hε' hne (by omega)
  refine ⟨γ + ε', -ε', hδ, IsRoot.neg hε', ?_, ?_, ?_⟩
  · intro hde
    have hg : γ = (-2 : ℤ) • ε' := by
      have h : γ + ε' + ε' = 0 := by rw [hde, neg_add_cancel]
      have h' : γ + 2 • ε' = 0 := by simpa [two_smul, add_assoc] using h
      have h'' : γ = -(2 • ε') := eq_neg_of_add_eq_zero_left h'
      rw [h'']
      simp
    have h8 : iform γ γ = 8 := by
      rw [hg, CFSG.LieType.Steinberg.Adjoint.iform_smul_left,
        CFSG.LieType.Steinberg.Adjoint.iform_smul_right,
        CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hε']
      norm_num
    have h2 : iform γ γ = 2 :=
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hγ
    omega
  · abel
  · rw [CFSG.LieType.Steinberg.Adjoint.iform_add_left,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_neg_right,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_neg_right, hif,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hε']
    norm_num

private theorem ggLieGC_pinnedX_mem_ratPoints
    {γ : Fin (langTag .E6).rank → ℤ} (hγ : IsRoot (langTag .E6) γ) :
    pinnedX (langTag .E6) GGL γ 1 ∈ ratPoints (ggPhi .E6 1) := by
  rw [ratPoints]
  refine Subgroup.mem_inf.2 ⟨pinnedX_mem_adjointGroup γ 1, ?_⟩
  refine MonoidHom.mem_eqLocusM.2 ?_
  rw [ggPhi_pinnedX_untw (t := .E6) (Or.inr (Or.inl rfl)) 1 hγ 1]
  norm_num

private theorem ggLieGC_commutator_langTag
    {K : Type} [Field K] [CharP K 2] {δ ε : Fin (langTag .E6).rank → ℤ}
    (hδ : IsRoot (langTag .E6) δ) (hε : IsRoot (langTag .E6) ε) (hne : δ ≠ ε)
    (hr : IsRoot (langTag .E6) (δ + ε)) (c d : K) :
    ⁅pinnedX (langTag .E6) K δ c, pinnedX (langTag .E6) K ε d⁆ =
      pinnedX (langTag .E6) K (δ + ε) (c * d) := by
  have hne' : δ ≠ -ε := fun e => hr.ne_zero (by rw [e, neg_add_cancel])
  obtain ⟨hs, hcomm⟩ := (simply_laced_root_commutator_unit.{0} (langTag .E6)
    (Or.inr (Or.inl rfl)) hδ hε hne hne').1 hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs1 : (commConst (langTag .E6) δ ε (1, 1) : K) = 1 := by
    rcases hs with h | h
    · rw [h, Int.cast_one]
    · rw [h, Int.cast_neg, Int.cast_one]
      linear_combination -h2
  rw [hcomm K c d, hs1, one_mul]

private theorem ggLieGC_pinnedX_one_mem_commutator
    {γ : Fin (langTag .E6).rank → ℤ} (hγ : IsRoot (langTag .E6) γ) :
    pinnedX (langTag .E6) GGL γ 1 ∈
      ⁅ratPoints (ggPhi .E6 1), ratPoints (ggPhi .E6 1)⁆ := by
  obtain ⟨δ, ε, hδ, hε, hne, hsum, -⟩ := ggLieGC_root_pair hγ
  have hr : IsRoot (langTag .E6) (δ + ε) := by rw [hsum]; exact hγ
  have hcomm := ggLieGC_commutator_langTag hδ hε hne hr (1 : GGL) (1 : GGL)
  rw [mul_one] at hcomm
  rw [← hsum]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (ggLieGC_pinnedX_mem_ratPoints hδ)
    (ggLieGC_pinnedX_mem_ratPoints hε)

private theorem ggLieGC_weylElt_mem_commutator
    (i : Fin (langTag .E6).rank) :
    weylElt (langTag .E6) GGL i 1 ∈
      ⁅ratPoints (ggPhi .E6 1), ratPoints (ggPhi .E6 1)⁆ := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  have harg : (-(((1 : GGLˣ)⁻¹ : GGLˣ) : GGL)) = (1 : GGL) := by
    rw [inv_one, Units.val_one, CharTwo.neg_eq]
  rw [harg]
  simp only [Units.val_one]
  rw [← pinnedX_single (τ := langTag .E6) (R := GGL) i 1,
    ← pinnedX_neg_single (τ := langTag .E6) (R := GGL) i 1]
  exact mul_mem (mul_mem (ggLieGC_pinnedX_one_mem_commutator (isRoot_single _ i))
    (ggLieGC_pinnedX_one_mem_commutator (IsRoot.neg (isRoot_single _ i))))
    (ggLieGC_pinnedX_one_mem_commutator (isRoot_single _ i))

private theorem ggLieGC_canonicalRep_mem_commutator
    (w : WeylGroup (langTag .E6)) :
    canonicalRep (coxeterSystem (langTag .E6)) GGL w ∈
      ⁅ratPoints (ggPhi .E6 1), ratPoints (ggPhi .E6 1)⁆ := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem (langTag .E6)).exists_isReduced w
  rw [canonicalRep_wordProd (cs := coxeterSystem (langTag .E6)) (R := GGL) hω]
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ggLieGC_weylElt_mem_commutator i

theorem ggLie_weyl_carry
    {β₀ β₁ ψ₀ ψ₁ : Fin (langTag .E6).rank → ℤ} (hβ₀ : IsRoot (langTag .E6) β₀)
    (hβ₁ : IsRoot (langTag .E6) β₁) (hψ₀ : IsRoot (langTag .E6) ψ₀)
    (hψ₁ : IsRoot (langTag .E6) ψ₁) (hβ : iform β₀ β₁ = 0) (hψ : iform ψ₀ ψ₁ = 0) :
    ∃ n ∈ ⁅ratPoints (ggPhi .E6 1), ratPoints (ggPhi .E6 1)⁆,
      n * (pinnedX (langTag .E6) GGL β₀ 1 * pinnedX (langTag .E6) GGL (-β₀) 1) * n⁻¹ =
        pinnedX (langTag .E6) GGL ψ₀ 1 * pinnedX (langTag .E6) GGL (-ψ₀) 1 ∧
      n * (pinnedX (langTag .E6) GGL β₁ 1 * pinnedX (langTag .E6) GGL (-β₁) 1) * n⁻¹ =
        pinnedX (langTag .E6) GGL ψ₁ 1 * pinnedX (langTag .E6) GGL (-ψ₁) 1 := by
  obtain ⟨u₁, hu₁θ, hu₁α⟩ :=
    CFSG.StandardType.KGL.exists_weyl_smul_orthPair hβ₀ hβ₁ hβ
  obtain ⟨u₂, hu₂θ, hu₂α⟩ :=
    CFSG.StandardType.KGL.exists_weyl_smul_orthPair hψ₀ hψ₁ hψ
  let hθ : Fin (langTag .E6).rank → ℤ := CFSG.SeitzReduction.highRoot Tag.E6
  let hα : Fin (langTag .E6).rank → ℤ := (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)
  let w₁ : WeylGroup (langTag .E6) := u₁
  let w₂ : WeylGroup (langTag .E6) := u₂
  have hw₁θ : w₁ • hθ = β₀ := hu₁θ
  have hw₁α : w₁ • hα = β₁ := hu₁α
  have hw₂θ : w₂ • hθ = ψ₀ := hu₂θ
  have hw₂α : w₂ • hα = ψ₁ := hu₂α
  let w₃ : WeylGroup (langTag .E6) := w₂ * w₁⁻¹
  have hwβ₀ : w₃ • β₀ = ψ₀ := by
    dsimp only [w₃]
    rw [mul_smul, ← hw₁θ, inv_smul_smul, hw₂θ]
  have hwβ₁ : w₃ • β₁ = ψ₁ := by
    dsimp only [w₃]
    rw [mul_smul, ← hw₁α, inv_smul_smul, hw₂α]
  refine ⟨canonicalRep (coxeterSystem (langTag .E6)) GGL w₃,
    ggLieGC_canonicalRep_mem_commutator w₃, ?_, ?_⟩
  · have h2 : (2 : GGL) = 0 := by
      haveI : CharP GGL 2 := inferInstance
      exact_mod_cast CharP.cast_eq_zero GGL 2
    have hc₀ := canonicalRep_mul_pinnedX_mul_inv_of_two (τ := langTag .E6) (K := GGL) h2 w₃
      hβ₀ 1
    have hc₀' := canonicalRep_mul_pinnedX_mul_inv_of_two (τ := langTag .E6) (K := GGL) h2 w₃
      (IsRoot.neg hβ₀) 1
    rw [hwβ₀] at hc₀
    have hm₀ : w₃ • (-β₀) = -ψ₀ := by rw [smul_neg, hwβ₀]
    rw [hm₀] at hc₀'
    calc canonicalRep (coxeterSystem (langTag .E6)) GGL w₃ *
          (pinnedX (langTag .E6) GGL β₀ 1 * pinnedX (langTag .E6) GGL (-β₀) 1) *
          (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃)⁻¹
        = (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃ * pinnedX (langTag .E6) GGL β₀ 1 *
            (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃)⁻¹) *
          (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃ *
            pinnedX (langTag .E6) GGL (-β₀) 1 *
            (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃)⁻¹) := by group
      _ = pinnedX (langTag .E6) GGL ψ₀ 1 * pinnedX (langTag .E6) GGL (-ψ₀) 1 := by
        rw [hc₀, hc₀']
  · have h2 : (2 : GGL) = 0 := by
      haveI : CharP GGL 2 := inferInstance
      exact_mod_cast CharP.cast_eq_zero GGL 2
    have hc₁ := canonicalRep_mul_pinnedX_mul_inv_of_two (τ := langTag .E6) (K := GGL) h2 w₃
      hβ₁ 1
    have hc₁' := canonicalRep_mul_pinnedX_mul_inv_of_two (τ := langTag .E6) (K := GGL) h2 w₃
      (IsRoot.neg hβ₁) 1
    rw [hwβ₁] at hc₁
    have hm₁ : w₃ • (-β₁) = -ψ₁ := by rw [smul_neg, hwβ₁]
    rw [hm₁] at hc₁'
    calc canonicalRep (coxeterSystem (langTag .E6)) GGL w₃ *
          (pinnedX (langTag .E6) GGL β₁ 1 * pinnedX (langTag .E6) GGL (-β₁) 1) *
          (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃)⁻¹
        = (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃ * pinnedX (langTag .E6) GGL β₁ 1 *
            (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃)⁻¹) *
          (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃ *
            pinnedX (langTag .E6) GGL (-β₁) 1 *
            (canonicalRep (coxeterSystem (langTag .E6)) GGL w₃)⁻¹) := by group
      _ = pinnedX (langTag .E6) GGL ψ₁ 1 * pinnedX (langTag .E6) GGL (-ψ₁) 1 := by
        rw [hc₁, hc₁']

end CFSG.StandardType.LieCore
