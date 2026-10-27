module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreStruct
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
public import Certificates.Certificate13659
import CFSG.HardMathSupport.Timmesfeld.LangTorus.UntwistOuter
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.LieType.AlgebraicGroups.ConnectedToralLang

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

private theorem mapsTo_kernelRoots_jointChar
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {a₁ a₂ : Fin τ.rank → Lˣ}
    (h₁ : rootDiagUnit τ a₁ ∈ D.torus) (h₂ : rootDiagUnit τ a₂ ∈ D.torus) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
      (kernelRoots (jointChar a₁ a₂)) (kernelRoots (jointChar a₁ a₂)) := by
  rintro γ ⟨hγ, hχ⟩
  have hχ' : (rootChar a₁ γ, rootChar a₂ γ) = 1 := hχ
  have h1 : rootChar a₁ γ = 1 := congrArg Prod.fst hχ'
  have h2 : rootChar a₂ γ = 1 := congrArg Prod.snd hχ'
  refine ⟨(hρ.isRoot_iff γ).2 hγ, ?_⟩
  change (rootChar a₁ (ρ γ), rootChar a₂ (ρ γ)) = 1
  rw [hρ.rootChar_eq a₁ h₁ γ hγ, hρ.rootChar_eq a₂ h₂ γ hγ, h1, h2]
  simp

theorem iterate_mem_kernelRoots_jointChar
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {a₁ a₂ : Fin τ.rank → Lˣ}
    (h₁ : rootDiagUnit τ a₁ ∈ D.torus) (h₂ : rootDiagUnit τ a₂ ∈ D.torus) (n : ℕ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots (jointChar a₁ a₂)) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[n] γ ∈ kernelRoots (jointChar a₁ a₂) := by
  exact (mapsTo_kernelRoots_jointChar hρ h₁ h₂).iterate n hγ

theorem exists_langSetup_of_datum
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ) (hfin : Finite D.model) {f : ℕ}
    (hf : 1 ≤ f) (hq : D.q = 2 ^ f) :
    ∃ S : LangSetup τ L 5, S.D = D ∧ S.ρ = ρ :=
  ⟨D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl)
    ⟨hq ▸ Nat.prime_two.isPrimePow.pow (by omega), by
      rw [hq]
      exact (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 (by omega))⟩
    (by
      rw [hq]
      intro h
      have := Nat.prime_five.dvd_of_dvd_pow h
      omega) hfin, rfl, rfl⟩

private lemma not_hasDiagramSymmetryType_of_smallRank {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hsh : (compRank Ψ = 1 ∧ Ψ.ncard = 2) ∨
      (compRank Ψ = 2 ∧ Ψ.ncard = 8) ∨ (compRank Ψ = 2 ∧ Ψ.ncard = 12)) :
    ¬ HasDiagramSymmetryType Ψ := by
  rintro (⟨h2, hc⟩ | ⟨h4, hc⟩ | ⟨h6, hc⟩) <;>
    rcases hsh with ⟨h1, hc1⟩ | ⟨h1, hc1⟩ | ⟨h1, hc1⟩
  · rw [h1] at h2 hc
    norm_num at hc
    omega
  · rw [h1] at h2 hc
    norm_num at hc
    omega
  · rw [h1] at h2 hc
    norm_num at hc
    omega
  · rw [h1] at h4
    omega
  · rw [h1] at h4
    omega
  · rw [h1] at h4
    omega
  · rw [h1] at h6
    omega
  · rw [h1] at h6
    omega
  · rw [h1] at h6
    omega

theorem twistInner_of_small_inner
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {φ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (hφ : φ '' componentRoots χ i = componentRoots χ i)
    (hinj : Function.Injective φ) (hform : ∀ γ δ, iform (φ γ) (φ δ) = iform γ δ)
    (hneg : ∀ γ, φ (-γ) = -φ γ)
    (hsh : (compRank (componentRoots χ i) = 1 ∧ (componentRoots χ i).ncard = 2) ∨
      (compRank (componentRoots χ i) = 2 ∧ (componentRoots χ i).ncard = 8) ∨
      (compRank (componentRoots χ i) = 2 ∧ (componentRoots χ i).ncard = 12)) :
    twistInner (componentRoots χ i) φ := by
  have hW : RootAutIsWeyl := CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hnsym : ¬ HasDiagramSymmetryType (componentRoots χ i) :=
    not_hasDiagramSymmetryType_of_smallRank hsh
  have hbij : Set.BijOn φ (componentRoots χ i) (componentRoots χ i) :=
    ⟨fun x hx => by
        rw [← hφ]
        exact Set.mem_image_of_mem φ hx,
      hinj.injOn,
      fun y hy => by
        rw [← hφ] at hy
        exact hy⟩
  exact hW τ (componentRoots χ i) hΨ hnsym φ hbij (fun γ _ δ _ => hform γ δ)
    (fun γ _ => hneg γ)

end CFSG.StandardType.LieCore
