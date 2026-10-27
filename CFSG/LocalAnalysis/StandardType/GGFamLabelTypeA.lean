module

public import CFSG.LocalAnalysis.StandardType.GGFamTypeAField
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelKind
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)
open CFSG.StandardType.TablePThreeKG (compRank_frameRoots_eq twistInner_of_splitFrame
  not_twistInner_of_unitaryFrame)
open scoped MatrixGroups commutatorElement

theorem fam_label_rankOne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hr1 : compRank (componentRoots χ i) = 1)
    (hn : (componentRoots χ i).ncard = 2)
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i)) :
    FamLabelAt S χ i := by
  classical
  obtain ⟨K, hKfield, hKfin, f, hf1, hKcard, hfield, _hchrK, hK4, g, hgsurj, hgker⟩ :=
    fam_exists_slCover_rankOne S hρ i hr1 hn hq
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hchr : ringChar L = 2 := ringChar.eq L 2
  have hK2 : Nat.card K = 2 ^ f := by rw [hKcard, hchr]
  have hfield' : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) := by
    rw [← hchr]; exact hfield
  have hf2 : 2 ≤ f := by
    rw [hK2] at hK4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at hK4
  have hN : (componentRoots χ i).ncard =
      compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) := by
    rw [hn, hr1]
  have hkind : twistKindOf S.ρ (componentRoots χ i) = .inner :=
    twistKindOf_eq_inner_of_compRank_eq_one S.ρ (componentRoots χ i) hr1
  have hlab : componentLabel (compRank (componentRoots χ i)) (componentRoots χ i).ncard
      (twistKindOf S.ρ (componentRoots χ i)) f = (⟨.A, 1, f⟩ : LargeEvenLabel) := by
    rw [hkind, componentLabel_inner_A f hN, hr1]
  have hmodel : LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
      Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i)) .PSL 2 2 f :=
    lieModel_of_slCover (ν := 2) hf1 hK2 (by norm_num) (by intro _; omega) g hgsurj hgker
  refine ⟨f, hfield', ?_⟩
  rw [hlab]
  exact ggCompLabelAt_A 1 f (by norm_num) hf1 (fun _ => hf2) hmodel

theorem fam_label_splitFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ x y) = σ (π x) (π y))
    (hA : 1 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) + 1))
    (hsl : ∀ γ ∈ componentRoots χ i, iform γ γ = 2) :
    FamLabelAt S χ i := by
  classical
  obtain ⟨K, hKfield, hKfin, f, hf1, hKcard, hfield, _hchrK, g, hgsurj, hgker⟩ :=
    fam_exists_slCover_splitFrame S hρ i hν hψ hΨ π hπ
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hchr : ringChar L = 2 := ringChar.eq L 2
  have hK2 : Nat.card K = 2 ^ f := by rw [hKcard, hchr]
  have hfield' : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) := by
    rw [← hchr]; exact hfield
  have hκ : (1 : ℤ) ≠ 0 := one_ne_zero
  have hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * (1 : ℤ) := by
    intro x y hxy
    have hroot : σ x y ∈ componentRoots χ i := by rw [hΨ]; exact ⟨x, y, hxy, rfl⟩
    rw [hsl _ hroot]; norm_num
  have hcr : compRank (componentRoots χ i) = ν - 1 :=
    compRank_frameRoots_eq hψ hκ hnorm hΨ hA.2 hν
  have hmodel : LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
      Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i)) .PSL ν 2 f :=
    lieModel_of_slCover (ν := ν) hf1 hK2 (le_trans (by norm_num) hν) (by intro h; omega)
      g hgsurj hgker
  have hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]) :=
    hΨ.symm ▸ twistInner_of_splitFrame hψ hκ hnorm
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]) π hπ
  have hkind : twistKindOf S.ρ (componentRoots χ i) = .inner :=
    twistKindOf_eq_inner_of_twistInner S.ρ (componentRoots χ i) hinner
  have hlab : componentLabel (compRank (componentRoots χ i)) (componentRoots χ i).ncard
      (twistKindOf S.ρ (componentRoots χ i)) f =
      (⟨.A, compRank (componentRoots χ i), f⟩ : LargeEvenLabel) := by
    rw [hkind, componentLabel_inner_A f hA.2]
  refine ⟨f, hfield', ?_⟩
  rw [hlab]
  refine ggCompLabelAt_A (compRank (componentRoots χ i)) f hA.1 hf1 (fun h => by omega) ?_
  have hνeq : compRank (componentRoots χ i) + 1 = ν := by omega
  rw [hνeq]
  exact hmodel

theorem fam_label_unitaryFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ x y) = σ (π y) (π x))
    (hA : 1 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) + 1))
    (hsl : ∀ γ ∈ componentRoots χ i, iform γ γ = 2)
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i)) :
    FamLabelAt S χ i := by
  classical
  have hchr : ringChar L = 2 := ringChar.eq L 2
  have hcover := fam_exists_suCover_unitaryFrame S hρ i hν hψ hΨ π hπ hq
  rw [hchr] at hcover
  obtain ⟨K, hKfield, hKfin, f, hf1, hKcard, hfield, _hchrK, h32, g, hgsurj, hgker⟩ := hcover
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hK2 : Nat.card K = (2 ^ f) ^ 2 := hKcard
  have hfield' : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) := hfield
  have hκ : (1 : ℤ) ≠ 0 := one_ne_zero
  have hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * (1 : ℤ) := by
    intro x y hxy
    have hroot : σ x y ∈ componentRoots χ i := by rw [hΨ]; exact ⟨x, y, hxy, rfl⟩
    rw [hsl _ hroot]; norm_num
  have hcr : compRank (componentRoots χ i) = ν - 1 :=
    compRank_frameRoots_eq hψ hκ hnorm hΨ hA.2 hν
  have hmodel : LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
      Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i)) .PSU ν 2 f :=
    lieModel_of_suCover (ν := ν) hf1 hK2 hν h32 g hgsurj hgker
  have hni : ¬ twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]) :=
    hΨ.symm ▸ not_twistInner_of_unitaryFrame hν hψ hκ hnorm
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]) π hπ
  have h2c : 2 ≤ compRank (componentRoots χ i) := by omega
  have hkind : twistKindOf S.ρ (componentRoots χ i) = .suN :=
    twistKindOf_eq_suN S.ρ (componentRoots χ i) hni h2c hA.2
  have hlab : componentLabel (compRank (componentRoots χ i)) (componentRoots χ i).ncard
      (twistKindOf S.ρ (componentRoots χ i)) f =
      (⟨.twA, compRank (componentRoots χ i), f⟩ : LargeEvenLabel) := by
    rw [hkind, componentLabel_suN]
  refine ⟨f, hfield', ?_⟩
  rw [hlab]
  refine ggCompLabelAt_twA (compRank (componentRoots χ i)) f h2c hf1 ?_ ?_
  · intro hc2
    have hν3 : ν = 3 := by omega
    have hf_ne1 : f ≠ 1 := by
      intro hf1'
      apply h32
      rw [hν3, hf1']
      norm_num
    omega
  · have hνeq : compRank (componentRoots χ i) + 1 = ν := by omega
    rw [hνeq]
    exact hmodel

theorem langFamRatLabel_typeA
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    FamLabelAt S (famCharHom a) i := by
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hslt : SimplyLacedTag τ := by rcases hτ with rfl | rfl | rfl <;> simp [SimplyLacedTag]
  have hsl : ∀ γ ∈ componentRoots (famCharHom a) i, iform γ γ = 2 := fun γ hγ =>
    CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two hslt
      ((isRootComponent_componentRoots (χ := famCharHom a) i).isRoot γ hγ)
  rcases fam_typeA_frame_cases hτ S hp hT hap h1 i hA with
      ⟨hr1, hn⟩ | ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ | ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩
  · exact fam_label_rankOne S hρ i hr1 hn hq
  · exact fam_label_splitFrame S hρ i hν hψ hΨ π hπ hA hsl
  · exact fam_label_unitaryFrame S hρ i hν hψ hΨ π hπ hA hsl hq

end CFSG.StandardType.TableCRes

end
