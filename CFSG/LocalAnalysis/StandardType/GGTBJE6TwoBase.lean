module

public import CFSG.LocalAnalysis.StandardType.GGLangRootSL2Rational
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair

public section

namespace CFSG.StandardType.E6Two

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped MatrixGroups commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem WSL_eq_uvu {L : Type} [Field L] [CharP L 2] :
    (WSL : SL(2, L)) = uSL 1 * vSL 1 * uSL 1 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, one_add_one_eq_two,
      CharTwo.two_eq_zero]

private theorem WSL_eq_vuv {L : Type} [Field L] [CharP L 2] :
    (WSL : SL(2, L)) = vSL 1 * uSL 1 * vSL 1 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, one_add_one_eq_two,
      CharTwo.two_eq_zero]


theorem map_fix_le_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {X : Type*} [Group X] (ψ : X →* ModGL τ L)
    (hψS : ∀ y, ψ y ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i))
    (hψA : ∀ y, ψ y ∈ adjointGroup τ L) (F' : X →* X)
    (hψF : ∀ y, S.D.step (ψ y) = ψ (F' y)) (K : Subgroup X) (hK : ∀ y ∈ K, F' y = y)
    (hKperf : ⁅K, K⁆ = K) :
    ∀ y ∈ K, ψ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  intro y hy
  set P : Subgroup (ModGL τ L) := K.map ψ with hP
  have hPmodel : P ≤ S.D.model := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hψA u, ?_⟩
    change S.D.step (ψ u) = ψ u
    rw [hψF, hK u hu]
  have hPspan : P ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rintro _ ⟨u, -, rfl⟩
    exact hψS u
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hKperf]
  have hPΓ : P ≤ S.Γ := by
    rw [← hPperf]
    exact Subgroup.commutator_mono hPmodel hPmodel
  have hPrat : P ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    fun g hg => ⟨hPspan hg, hPΓ hg⟩
  have hcomm : ⁅P, P⁆ ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mono hPrat hPrat
  rw [hPperf] at hcomm
  exact hcomm ⟨y, hy, rfl⟩

theorem step_rootSL2_of_charTwo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (X : SL(2, L)) :
    S.D.step (rootSL2 τ L α X) =
      rootSL2 τ L (S.ρ α) (Matrix.SpecialLinearGroup.map Fr X) := by
  have h : S.D.step.comp (rootSL2 τ L α) =
      (rootSL2 τ L (S.ρ α)).comp (Matrix.SpecialLinearGroup.map Fr) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change S.D.step (rootSL2 τ L α (uSL c)) =
          rootSL2 τ L (S.ρ α) (Matrix.SpecialLinearGroup.map Fr (uSL c))
        rw [rootSL2_uSL_of_charTwo hα, LangRat.step_pinnedX_of_charTwo S hα, map_uSL,
          rootSL2_uSL_of_charTwo ((S.frob.isRoot_iff α).2 hα), hFr]
      · change S.D.step (rootSL2 τ L α (vSL c)) =
          rootSL2 τ L (S.ρ α) (Matrix.SpecialLinearGroup.map Fr (vSL c))
        rw [rootSL2_vSL_of_charTwo hα, LangRat.step_pinnedX_of_charTwo S (IsRoot.neg hα),
          S.frob.neg_eq, map_vSL, rootSL2_vSL_of_charTwo ((S.frob.isRoot_iff α).2 hα), hFr]
  exact DFunLike.congr_fun h X

theorem rootSL2_neg_WSL_of_charTwo
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootSL2 τ L (-β) WSL = rootSL2 τ L β WSL := by
  have h1 : rootSL2 τ L (-β) WSL =
      pinnedX τ L (-β) 1 * pinnedX τ L β 1 * pinnedX τ L (-β) 1 := by
    rw [WSL_eq_uvu (L := L), map_mul, map_mul, rootSL2_uSL_of_charTwo (IsRoot.neg hβ),
      rootSL2_vSL_of_charTwo (IsRoot.neg hβ), neg_neg]
  have h2 : rootSL2 τ L β WSL =
      pinnedX τ L (-β) 1 * pinnedX τ L β 1 * pinnedX τ L (-β) 1 := by
    rw [WSL_eq_vuv (L := L), map_mul, map_mul, rootSL2_uSL_of_charTwo hβ,
      rootSL2_vSL_of_charTwo hβ]
  rw [h1, h2]

end CFSG.StandardType.E6Two

end
