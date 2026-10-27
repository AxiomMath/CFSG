module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def UFieldInputSmall
    (τ : Tag) :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ p : ℕ) (S : LangSetup τ L p₀),
    p.Prime → p ≠ 2 → ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
      ∀ K : Subgroup (ModGL τ L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) →
        ∃ i : KernelComponent (famCharHom a),
          K ≤ rootSpan τ L (famOrbit S.ρ a i) ∧
          (GGCompFieldAt (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) K ∨
            (S.D.q = 2 ∧ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 ∧
              Nat.card K = 360 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360))

theorem two_le_of_fieldExt_small
    {X Y : Type} [Group X] [Group Y] {J : Subgroup X} {J' : Subgroup Y}
    (hJ : CFSG.Open.IsQuasisimple ↥J)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* (↥J' ⧸ Subgroup.center ↥J'))
    {f k : ℕ}
    (hfield : GGCompFieldAt (2 ^ (f * k)) J' ∨
      (2 ^ f = 2 ∧ k = 1 ∧ Nat.card ↥J' = 360 ∧ Nat.card (↥J' ⧸ Subgroup.center ↥J') = 360))
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') : 2 ≤ k := by
  rcases hfield with hfield | ⟨-, -, -, hsmall⟩
  · exact two_le_of_fieldExt hJ e hfield hF
  · exfalso
    obtain ⟨_, _, _, -, hmod⟩ := hF
    refine ClNonsplit.evenLieOrder_ne_three_sixty_of_admissible
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hmod) ?_
    rw [← CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hmod, Nat.card_congr e.toEquiv]
    exact hsmall

theorem uframe_conclude_small
    {τ : Tag} (hField : UFieldInputSmall τ)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S₁ : LangSetup τ (AlgebraicClosure K) 5)
    (hq : S₁.D.q = 2 ^ f) (fr₁ : GGTCUFrame S₁.Γ G₀ B) (hBT : fr₁.BLang ≤ S₁.D.torus)
    (hBel : IsElemAbelian p B) (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') :
    ∃ (Ψ : Set (Fin τ.rank → ℤ)),
      IsRootComponent Ψ ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (S₁.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ τ.rank := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.toLang_injective).toEquiv
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hpar : ∀ u : fr₁.DLang D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hBT (hD₁B u.2)).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hBT (hD₁B u.2)
  have hrange : (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u)) =
      ((fr₁.DLang D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DLang D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u))) := by
    rw [hrange]
    exact fr₁.isComponentOf_JLang hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DLang D) a haT hap (fr₁.JLang J) hcomp
  rw [hq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt_small hJ.2.2 (fr₁.nonempty_equiv_JLang hJG hJ.2.2).some hfield hF
  have hC := fr₁.le_DLang_of_commute hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BLang (fr₁.DLang D) (fr₁.JLang J) hBT hBel₁.2 hD₁B a i
    hspan hC
  refine ⟨componentRoots (famCharHom a) i, isRootComponent_componentRoots i, ?_, ?_,
    two_mul_finrank_le_of_orbit S₁ a haT i h2⟩
  · obtain ⟨j, hj⟩ := exists_image_component_of_stable (famCharHom a)
      (fun γ hγ => rho_mem_kernelRoots_famChar S₁ a haT hγ) S₁.frob.iform_eq i
    have hij : i ≠ j := by
      rintro rfl
      exact image_ne_of_two_le_componentOrbitLength h2 hj
    intro γ hγ δ hδ
    rw [hj] at hδ
    refine ⟨iform_eq_zero_of_mem_componentRoots' hij hγ hδ, ?_⟩
    obtain ⟨hγk, hγi⟩ := hγ
    obtain ⟨hδk, hδi⟩ := hδ
    have := not_isRoot_of_mk_ne (χ := famCharHom a) (α := ⟨γ, hγk⟩) (β := ⟨δ, hδk⟩)
      (by rw [hγi, hδi]; exact hij) one_pos one_pos
    simpa using this
  · calc Nat.card B = Nat.card fr₁.BLang := fr₁.card_BLang.symm
      _ ≤ Nat.card (fr₁.DLang D) *
          p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
      _ = p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) := by
        rw [fr₁.card_DLang hDB, hDcard, pow_add]

theorem uframe_main_small
    {τ : Tag} (hField : UFieldInputSmall τ)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt τ p (Nat.card B)) :
    ∃ (Ψ : Set (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ)),
      IsRootComponent Ψ ∧ (∀ γ, IsRoot τ (ρ γ) ↔ IsRoot τ γ) ∧
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ τ.rank := by
  obtain ⟨K, instF, instFin, instChar, S, hq, ⟨fr⟩⟩ :=
    exists_uframe hτ hp hp2 hmod hBN hin hfaith hBel hDB hDcard
  obtain ⟨S₁, hq₁, fr₁, hBT⟩ := exists_torus_uframe hτ hp hp2 S fr hBel htor
  obtain ⟨Ψ, hΨ, horth, hcard, h2r⟩ :=
    uframe_conclude_small hField hp hp2 S₁ (hq₁.trans hq) fr₁ hBT hBel hDB hDcard hJG hJ hcent hF
  exact ⟨Ψ, S₁.ρ, hΨ, S₁.frob.isRoot_iff, S₁.frob.iform_eq, horth, hcard, h2r⟩

end CFSG.StandardType.TableCRes
