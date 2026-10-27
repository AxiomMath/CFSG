module

public import CFSG.LocalAnalysis.StandardType.GGSelectedRootPair
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaPlusRoot
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaMinusRoot
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLongField
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin
public import CFSG.LocalAnalysis.StandardType.GGRankOneTagsA
import CFSG.LieType.Universal.Spin.Twisted.Extras
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Generation.Datum
import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LieType.HighestRoot.RootInvolution
import CFSG.LieType.Universal.SpinOmega.Kernel
import CFSG.LargeExtraspecial.A2ModFrBLevi

public section

namespace CFSG.StandardType.SiegelPair

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.ModelFacts CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

section Generic

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem isLongestRoot_of_ggLongRoot (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {β : Fin D.rank → ℤ} (h : GGLongRoot D β) : IsLongestRoot D β := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := h
  have hH := CFSG.LieType.HighestRoot.isHighestRoot_of_forall_ht_le hirr hdiv hγ₀ hmax
  have hL : IsLongestRoot D γ₀ := ⟨hH.mem_roots, hH.longest⟩
  exact IsLongest.map_weylAction hL w

private theorem map_conj_mul (H : Subgroup K) (a b : K) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem map_conj_map {K' : Type*} [Group K'] (ι : K' →* K) (H : Subgroup K') (g : K') :
    (H.map (MulAut.conj g).toMonoidHom).map ι = (H.map ι).map (MulAut.conj (ι g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem exists_rootPair_eq_of_images {K' V : Type*} [Group K'] [Group V]
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅) (ι : K' →* K) (σ : K →* V)
    (hσ : Function.Injective σ) {β : Fin D.rank → ℤ} (u₁ : K) {β₀ α' : Fin D'.rank → ℤ}
    (hβ₀ : IsLongestRoot D' β₀) (hα' : IsLongestRoot D' α')
    (h₁ : ((D'.rootGroup β₀).map ι).map σ =
      ((D.rootGroup β).map (MulAut.conj u₁).toMonoidHom).map σ)
    (h₂ : ((D'.rootGroup (-β₀)).map ι).map σ =
      ((D.rootGroup (-β)).map (MulAut.conj u₁).toMonoidHom).map σ) :
    ∃ u : K, (D'.rootGroup α').map ι = (D.rootGroup β).map (MulAut.conj u).toMonoidHom ∧
      (D'.rootGroup (-α')).map ι = (D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom := by
  have e₁ := Subgroup.map_injective hσ h₁
  have e₂ := Subgroup.map_injective hσ h₂
  obtain ⟨g', hg'₁, hg'₂⟩ := exists_map_conj_rankOne_of_isLongest hct' hirr'
    (fun i hi => by rw [hdiv'] at hi; exact absurd hi (Set.notMem_empty i)) hα' hβ₀
  refine ⟨(ι g')⁻¹ * u₁, ?_, ?_⟩
  · symm
    rw [map_conj_mul, ← e₁, ← hg'₁, map_conj_map, ← map_conj_mul, inv_mul_cancel, map_one]
    exact Subgroup.map_id _
  · symm
    rw [map_conj_mul, ← e₂, ← hg'₂, map_conj_map, ← map_conj_mul, inv_mul_cancel, map_one]
    exact Subgroup.map_id _

end Generic

section Spin

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_rootPair_eq_siegel_POmegaPlus {n : ℕ} (hn : 3 ≤ n) {K' : Type*} [Group K']
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅)
    (ι : K' →* ↥(spinGroup (Spin.quadPlus n F)))
    {β₀ : Fin D'.rank → ℤ} (hlong : GGLongRoot D' β₀) {α' : Fin D'.rank → ℤ}
    (hα' : IsLongestRoot D' α') (a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F)
    (hQ : (Spin.quadPlus n F) a₁ = 0 ∧ (Spin.quadPlus n F) a₂ = 0 ∧ (Spin.quadPlus n F) b₁ = 0 ∧
      (Spin.quadPlus n F) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadPlus n F) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadPlus n F) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadPlus n F) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map (Spin.spinAction (Spin.quadPlus n F)) =
      siegelGroup (Spin.quadPlus n F) a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map (Spin.spinAction (Spin.quadPlus n F)) =
      siegelGroup (Spin.quadPlus n F) b₁ b₂) :
    ∃ β, IsLongestRoot (Spin.plusDatum n F hn) β ∧ ∃ u : ↥(spinGroup (Spin.quadPlus n F)),
      (D'.rootGroup α').map ι =
          ((Spin.plusDatum n F hn).rootGroup β).map (MulAut.conj u).toMonoidHom ∧
        (D'.rootGroup (-α')).map ι =
          ((Spin.plusDatum n F hn).rootGroup (-β)).map (MulAut.conj u).toMonoidHom := by
  obtain ⟨β, -, hlβ, u₁, hu₁, hu₁'⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus n F hn a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  have hβ : IsLongestRoot (Spin.plusDatum n F hn) β :=
    isLongestRoot_of_ggLongRoot (isIrreducible_cartanD hn) rfl hlβ
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hσ : Function.Injective (Spin.spinAction (Spin.quadPlus n F)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Spin.ker_spinMatrix]
    exact Spin.ker_spinMatrix_quadPlus_eq_bot h2
  obtain ⟨u, hu⟩ := exists_rootPair_eq_of_images hct' hirr' hdiv' ι _ hσ u₁
    (isLongestRoot_of_ggLongRoot hirr' hdiv' hlong) hα' (hX.trans hu₁.symm) (hX'.trans hu₁'.symm)
  exact ⟨β, hβ, u, hu⟩

theorem exists_rootPair_eq_siegel_POmegaMinus {n : ℕ} (hn : 4 ≤ n) {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) {K' : Type*} [Group K']
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅)
    (ι : K' →* ↥(spinGroup (Spin.quadMinus n F bq cq)))
    {β₀ : Fin D'.rank → ℤ} (hlong : GGLongRoot D' β₀) {α' : Fin D'.rank → ℤ}
    (hα' : IsLongestRoot D' α') (a₁ a₂ b₁ b₂ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)
    (hQ : (Spin.quadMinus n F bq cq) a₁ = 0 ∧ (Spin.quadMinus n F bq cq) a₂ = 0 ∧
      (Spin.quadMinus n F bq cq) b₁ = 0 ∧ (Spin.quadMinus n F bq cq) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadMinus n F bq cq) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadMinus n F bq cq) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadMinus n F bq cq) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n F bq cq) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n F bq cq) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n F bq cq) a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map (Spin.spinAction (Spin.quadMinus n F bq cq)) =
      siegelGroup (Spin.quadMinus n F bq cq) a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map (Spin.spinAction (Spin.quadMinus n F bq cq)) =
      siegelGroup (Spin.quadMinus n F bq cq) b₁ b₂) :
    ∃ β, IsLongestRoot (Spin.Twisted.minusDatum n hirr) β ∧
      ∃ u : ↥(spinGroup (Spin.quadMinus n F bq cq)),
        (D'.rootGroup α').map ι =
            ((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom ∧
          (D'.rootGroup (-α')).map ι =
            ((Spin.Twisted.minusDatum n hirr).rootGroup (-β)).map (MulAut.conj u).toMonoidHom := by
  obtain ⟨β, -, hlβ, u₁, hu₁, hu₁'⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaMinus n hirr hn a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  have hβ : IsLongestRoot (Spin.Twisted.minusDatum n hirr) β :=
    isLongestRoot_of_ggLongRoot (isIrreducible_cartanB (by omega)) rfl hlβ
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hσ := CFSG.LargeExtraspecial.A2Mod.FrB.spinAction_injective n hirr h2
  obtain ⟨u, hu⟩ := exists_rootPair_eq_of_images hct' hirr' hdiv' ι _ hσ u₁
    (isLongestRoot_of_ggLongRoot hirr' hdiv' hlong) hα' (hX.trans hu₁.symm) (hX'.trans hu₁'.symm)
  exact ⟨β, hβ, u, hu⟩

end Spin

section SpinPsi

variable {G : Type} [Group G]

theorem exists_ggRootSub_eq_siegel_POmegaPlus {k f : ℕ}
    (ψ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G) {K' : Type*} [Group K']
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅)
    (ι : K' →* ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
    {β₀ : Fin D'.rank → ℤ} (hlong : GGLongRoot D' β₀) {α' : Fin D'.rank → ℤ}
    (hα' : IsLongestRoot D' α') (a₁ a₂ b₁ b₂ : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f)
    (hQ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂) :
    ∃ β, IsLongestRoot (Spin.plusDatum (k + 3) (GaloisField 2 f) (Nat.le_add_left 3 k)) β ∧
      ∃ u : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))),
        (D'.rootGroup α').map (ψ.comp ι) =
            ggRootSub (Spin.plusDatum (k + 3) (GaloisField 2 f) (Nat.le_add_left 3 k)) ψ β u ∧
          (D'.rootGroup (-α')).map (ψ.comp ι) =
            ggRootSub (Spin.plusDatum (k + 3) (GaloisField 2 f) (Nat.le_add_left 3 k)) ψ (-β)
              u := by
  obtain ⟨β, hβ, u, hu₁, hu₂⟩ := exists_rootPair_eq_siegel_POmegaPlus (Nat.le_add_left 3 k) hct'
    hirr' hdiv' ι hlong hα' a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'
  refine ⟨β, hβ, u, ?_, ?_⟩
  · exact (Subgroup.map_map _ _ _).symm.trans (congrArg (Subgroup.map ψ) hu₁)
  · exact (Subgroup.map_map _ _ _).symm.trans (congrArg (Subgroup.map ψ) hu₂)

end SpinPsi

section Packages

variable {G : Type} [Group G]

theorem presentedSelectedSL2At_ggRootSub_of_longModel {t : StatedLieTag} {n f : ℕ}
    (ψ : (ggU t n f).K →* G) {nn : Fin (ggU t n f).D.rank → (ggU t n f).K}
    {H : Fin (ggU t n f).D.rank → Subgroup (ggU t n f).K}
    (hct : IsCTGroupDatum (coxeterMatrix (ggU t n f).D.isFiniteType).toCoxeterSystem
      (weylAction (ggU t n f).D.isFiniteType) (ggU t n f).D.roots (ggU t n f).D.rootGroup nn H)
    (hirr : IsIrreducible (ggU t n f).D.cartan) (hdiv : (ggU t n f).D.divisible = ∅)
    {k : Type} [Field k] [Finite k] [CharP k 2] {α : Fin (ggU t n f).D.rank → ℤ}
    (hα : IsLongestRoot (ggU t n f).D α) (model : SelectedRoot.SelectedSL2Model (ggU t n f).D k α)
    (hmodel : model.phi.range = ggRootLevi (ggU t n f).D α) {β : Fin (ggU t n f).D.rank → ℤ}
    (hβ : IsLongestRoot (ggU t n f).D β) (u : (ggU t n f).K) :
    PresentedSelectedSL2At ψ
      (ggRootSub (ggU t n f).D ψ β u ⊔ ggRootSub (ggU t n f).D ψ (-β) u) := by
  obtain ⟨g, hg₁, hg₂⟩ := exists_map_conj_rankOne_of_isLongest hct hirr
    (fun i hi => by rw [hdiv] at hi; exact absurd hi (Set.notMem_empty i)) hα hβ
  refine ⟨k, inferInstance, inferInstance, inferInstance, α, model, u * g, ?_⟩
  rw [MonoidHom.range_comp, hmodel, ← Subgroup.map_map, ggRootLevi, Subgroup.map_sup,
    map_conj_mul, map_conj_mul, hg₁, hg₂, Subgroup.map_sup]
  rfl

theorem exists_ggRootSub_eq_siegel_POmegaMinus {n f : ℕ} (hn : 4 ≤ n)
    (ψ : (ggU .POmegaMinus n f).K →* G) {K' : Type*} [Group K']
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅)
    (ι : K' →* (ggU .POmegaMinus n f).K)
    {β₀ : Fin D'.rank → ℤ} (hlong : GGLongRoot D' β₀) {α' : Fin D'.rank → ℤ}
    (hα' : IsLongestRoot D' α')
    (a₁ a₂ b₁ b₂ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f)
    (hQ : (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₂ = 0)
    (h₁ : QuadraticMap.polar
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        b₁ b₂) :
    ∃ β, IsLongestRoot (ggU .POmegaMinus n f).D β ∧ ∃ u : (ggU .POmegaMinus n f).K,
      (D'.rootGroup α').map (ψ.comp ι) = ggRootSub (ggU .POmegaMinus n f).D ψ β u ∧
        (D'.rootGroup (-α')).map (ψ.comp ι) = ggRootSub (ggU .POmegaMinus n f).D ψ (-β) u := by
  obtain ⟨β, hβ, u, hu₁, hu₂⟩ := exists_rootPair_eq_siegel_POmegaMinus hn (minusCoeffs_irr 2 f)
    hct' hirr' hdiv' ι hlong hα' a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'
  refine ⟨β, hβ, u, ?_, ?_⟩
  · exact (Subgroup.map_map _ _ _).symm.trans (congrArg (Subgroup.map ψ) hu₁)
  · exact (Subgroup.map_map _ _ _).symm.trans (congrArg (Subgroup.map ψ) hu₂)

theorem presentedSelectedSL2At_of_siegel_POmegaPlus {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* G) {K' : Type} [Group K']
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅)
    (ι : K' →* ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
    {β₀ : Fin D'.rank → ℤ} (hlong : GGLongRoot D' β₀) {δ : Fin D'.rank → ℤ}
    (hδ : IsLongestRoot D' δ) (model' : SelectedRoot.SelectedSL2Model D' (GaloisField 2 f) δ)
    (hmodel' : model'.phi.range = ggRootLevi D' δ)
    (a₁ a₂ b₁ b₂ : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f)
    (hQ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂) :
    PresentedSelectedSL2At ψ
      ((((show ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G from ψ).comp ι).comp
        model'.phi).range) := by
  let ψ₀ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G := ψ
  obtain ⟨β, hβ, u, hu₁, hu₂⟩ := exists_ggRootSub_eq_siegel_POmegaPlus ψ₀ hct' hirr' hdiv' ι hlong
    hδ a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'
  have hadm : StatedLieAdmissible .POmegaPlus (k + 3) 2 f := ⟨Nat.prime_two, hf, by omega⟩
  have hrank : 3 ≤ bnRank .POmegaPlus (k + 3) := by simp only [bnRank]; omega
  have hS : ((ψ₀.comp ι).comp model'.phi).range =
      ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u ⊔
        ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u := by
    rw [MonoidHom.range_comp, hmodel', ggRootLevi, Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) hu₁ hu₂
  exact (congrArg (PresentedSelectedSL2At ψ) hS).mpr
    (presentedSelectedSL2At_ggRootSub ψ (ggTagFacts_POmegaPlus hadm hrank).2.1
      (ggRankOneModel_POmegaPlus hadm hrank) rfl hβ.1 u)

theorem presentedSelectedSL2At_of_siegel_POmegaMinus {n f : ℕ} (hn : 4 ≤ n)
    (ψ : (ggU .POmegaMinus n f).K →* G) {K' : Type} [Group K']
    {D' : UniversalRootDatum K'} {nn' : Fin D'.rank → K'} {H' : Fin D'.rank → Subgroup K'}
    (hct' : IsCTGroupDatum (coxeterMatrix D'.isFiniteType).toCoxeterSystem
      (weylAction D'.isFiniteType) D'.roots D'.rootGroup nn' H')
    (hirr' : IsIrreducible D'.cartan) (hdiv' : D'.divisible = ∅)
    (ι : K' →* (ggU .POmegaMinus n f).K)
    {β₀ : Fin D'.rank → ℤ} (hlong : GGLongRoot D' β₀) {δ : Fin D'.rank → ℤ}
    (hδ : IsLongestRoot D' δ) (model' : SelectedRoot.SelectedSL2Model D' (GaloisField 2 f) δ)
    (hmodel' : model'.phi.range = ggRootLevi D' δ)
    (a₁ a₂ b₁ b₂ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f)
    (hQ : (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₂ = 0)
    (h₁ : QuadraticMap.polar
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        b₁ b₂) :
    PresentedSelectedSL2At ψ (((ψ.comp ι).comp model'.phi).range) := by
  obtain ⟨β, hβ, u, hu₁, hu₂⟩ := exists_ggRootSub_eq_siegel_POmegaMinus hn ψ hct' hirr' hdiv' ι
    hlong hδ a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'
  obtain ⟨δ₀, -, hlδ₀, model₀, hmodel₀, -⟩ :=
    SelectedRoot.exists_selectedSL2Model_POmegaMinus_long_range (f := f) hn
  have hirr : IsIrreducible (ggU .POmegaMinus n f).D.cartan := isIrreducible_cartanB (by omega)
  have hS : ((ψ.comp ι).comp model'.phi).range =
      ggRootSub (ggU .POmegaMinus n f).D ψ β u ⊔ ggRootSub (ggU .POmegaMinus n f).D ψ (-β) u := by
    rw [MonoidHom.range_comp, hmodel', ggRootLevi, Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) hu₁ hu₂
  rw [hS]
  exact presentedSelectedSL2At_ggRootSub_of_longModel ψ
    (Spin.Twisted.minusDatum_isCTGroupDatum n (minusCoeffs_irr 2 f) hn) hirr rfl
    (isLongestRoot_of_ggLongRoot hirr rfl hlδ₀) model₀ hmodel₀ hβ u

theorem exists_memberKit_orthogonal {t' : StatedLieTag} {m f : ℕ}
    (ht' : t' = .POmegaPlus ∨ t' = .POmegaMinus) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ∃ (nn' : Fin (ggU t' m f).D.rank → (ggU t' m f).K)
      (H' : Fin (ggU t' m f).D.rank → Subgroup (ggU t' m f).K),
      IsCTGroupDatum (coxeterMatrix (ggU t' m f).D.isFiniteType).toCoxeterSystem
        (weylAction (ggU t' m f).D.isFiniteType) (ggU t' m f).D.roots (ggU t' m f).D.rootGroup
        nn' H' ∧
      IsIrreducible (ggU t' m f).D.cartan ∧ (ggU t' m f).D.divisible = ∅ ∧
      ∃ (δ : Fin (ggU t' m f).D.rank → ℤ)
        (model' : SelectedRoot.SelectedSL2Model (ggU t' m f).D (GaloisField 2 f) δ),
        IsLongestRoot (ggU t' m f).D δ ∧ model'.phi.range = ggRootLevi (ggU t' m f).D δ := by
  rcases ht' with rfl | rfl
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    have hn : 3 ≤ j + 3 := by omega
    have hadm : StatedLieAdmissible .POmegaPlus (j + 3) 2 f := ⟨Nat.prime_two, hf, by omega⟩
    have hrank : 3 ≤ bnRank .POmegaPlus (j + 3) := by simp only [bnRank]; omega
    obtain ⟨model', hmodel'⟩ := SelectedRoot.exists_model_of_rankOneModel
      (ggRankOneModel_POmegaPlus hadm hrank) (⟨0, by omega⟩ : Fin (j + 3))
    exact ⟨_, _, Spin.plusDatum_isCTGroupDatum hn (Spin.plusDatum_iSup_eq_top (j + 3) _ hn),
      isIrreducible_cartanD hn, rfl, _, model',
      isLongest_single_cartanD hn rfl _ _, hmodel'⟩
  · have hirr' : IsIrreducible (ggU .POmegaMinus m f).D.cartan := isIrreducible_cartanB (by omega)
    obtain ⟨δ, -, hlδ, model', hmodel', -⟩ :=
      SelectedRoot.exists_selectedSL2Model_POmegaMinus_long_range (f := f) hm
    exact ⟨_, _, Spin.Twisted.minusDatum_isCTGroupDatum m (minusCoeffs_irr 2 f) hm, hirr', rfl,
      δ, model', isLongestRoot_of_ggLongRoot hirr' rfl hlδ, hmodel'⟩

theorem exists_presented_of_siegelBlock_POmegaPlus {k f m : ℕ} {t' : StatedLieTag}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (ht' : t' = .POmegaPlus ∨ t' = .POmegaMinus) (hm : 4 ≤ m)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* G)
    (ι : (ggU t' m f).K →* ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
    {β₀ : Fin (ggU t' m f).D.rank → ℤ} (hlong : GGLongRoot (ggU t' m f).D β₀)
    (a₁ a₂ b₁ b₂ : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f)
    (hQ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₁ = 0)
    (hX : (((ggU t' m f).D.rootGroup β₀).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂)
    (hX' : (((ggU t' m f).D.rootGroup (-β₀)).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂) :
    ∃ (δ : Fin (ggU t' m f).D.rank → ℤ)
      (model' : SelectedRoot.SelectedSL2Model (ggU t' m f).D (GaloisField 2 f) δ),
      model'.phi.range = ggRootLevi (ggU t' m f).D δ ∧
        PresentedSelectedSL2At ψ
          ((((show ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G from ψ).comp
            ι).comp model'.phi).range) := by
  obtain ⟨nn', H', hct', hirr', hdiv', δ, model', hδ, hmodel'⟩ :=
    exists_memberKit_orthogonal ht' hm hf
  exact ⟨δ, model', hmodel', presentedSelectedSL2At_of_siegel_POmegaPlus hk hf ψ hct' hirr' hdiv'
    ι hlong hδ model' hmodel' a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'⟩

theorem exists_presented_of_siegelBlock_POmegaMinus {n f m : ℕ} {t' : StatedLieTag}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (ht' : t' = .POmegaPlus ∨ t' = .POmegaMinus) (hm : 4 ≤ m)
    (ψ : (ggU .POmegaMinus n f).K →* G) (ι : (ggU t' m f).K →* (ggU .POmegaMinus n f).K)
    {β₀ : Fin (ggU t' m f).D.rank → ℤ} (hlong : GGLongRoot (ggU t' m f).D β₀)
    (a₁ a₂ b₁ b₂ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f)
    (hQ : (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₂ = 0)
    (h₁ : QuadraticMap.polar
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₂ = 0 ∧
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₁ = 0)
    (hX : (((ggU t' m f).D.rootGroup β₀).map ι).map (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        a₁ a₂)
    (hX' : (((ggU t' m f).D.rootGroup (-β₀)).map ι).map (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        b₁ b₂) :
    ∃ (δ : Fin (ggU t' m f).D.rank → ℤ)
      (model' : SelectedRoot.SelectedSL2Model (ggU t' m f).D (GaloisField 2 f) δ),
      model'.phi.range = ggRootLevi (ggU t' m f).D δ ∧
        PresentedSelectedSL2At ψ (((ψ.comp ι).comp model'.phi).range) := by
  obtain ⟨nn', H', hct', hirr', hdiv', δ, model', hδ, hmodel'⟩ :=
    exists_memberKit_orthogonal ht' hm hf
  exact ⟨δ, model', hmodel', presentedSelectedSL2At_of_siegel_POmegaMinus hn ψ hct' hirr' hdiv'
    ι hlong hδ model' hmodel' a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'⟩

end Packages

end CFSG.StandardType.SiegelPair

end
