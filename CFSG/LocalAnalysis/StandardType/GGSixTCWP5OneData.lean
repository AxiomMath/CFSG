module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UData
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5UFrame

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType

theorem uframe_data_twE6
    (hField : UFieldInput Tag.E6)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* twistedE6RootGroup K σ)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt Tag.E6 p (Nat.card B)) :
    ∃ (S₁ : LangSetup Tag.E6 (AlgebraicClosure K) 5) (fr₁ : GGTCUFrame S₁.Γ G₀ B),
      S₁.D.q = 2 ^ f ∧ fr₁.BLang ≤ S₁.D.torus ∧
      ∃ (a : ↥(fr₁.DLang D) → Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
        (i : KernelComponent (famCharHom a)),
        (∀ u : ↥(fr₁.DLang D),
          (u : ModGL Tag.E6 (AlgebraicClosure K)) = rootDiagUnit Tag.E6 (a u)) ∧
        (∀ u j, a u j ^ p = 1) ∧
        fr₁.JLang J ≤ rootSpan Tag.E6 (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
        2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) ∧
        IsRootComponent (componentRoots (famCharHom a) i) ∧
        (∀ γ ∈ componentRoots (famCharHom a) i,
          ∀ δ ∈ (S₁.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
              componentRoots (famCharHom a) i,
            iform γ δ = 0 ∧ ¬ IsRoot Tag.E6 (γ + δ)) ∧
        Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ
          (componentRoots (famCharHom a) i))) ∧
        2 * Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) ≤
          Tag.E6.rank := by
  classical
  have : CharP K 2 :=
    charP_two_of_finite_field_card_two_pow (f := f * 2) (by rw [hK, pow_mul])
  obtain ⟨S, hq, ⟨fr⟩⟩ :=
    exists_uframe_twE6 hf hp hp2 hK σ hσ θ hBN hin hfaith hBel hDB hDcard
  obtain ⟨S₁, hq₁, fr₁, hBT⟩ :=
    exists_torus_uframe (τ := Tag.E6) (Or.inr (Or.inl rfl)) hp hp2 S fr hBel htor
  have hqq : S₁.D.q = 2 ^ f := hq₁.trans hq
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.toLang_injective).toEquiv
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hpar : ∀ u : fr₁.DLang D, ∃ c : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL Tag.E6 (AlgebraicClosure K)) = rootDiagUnit Tag.E6 c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hBT (hD₁B u.2)).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit Tag.E6 (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hBT (hD₁B u.2)
  have hrange : (Set.range fun u : fr₁.DLang D => rootDiagUnit Tag.E6 (a u)) =
      ((fr₁.DLang D : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :
        Set (ModGL Tag.E6 (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit Tag.E6 (a u) ∈ (fr₁.DLang D : Set (ModGL Tag.E6 (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DLang D => rootDiagUnit Tag.E6 (a u))) := by
    rw [hrange]
    exact fr₁.isComponentOf_JLang hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DLang D) a haT hap (fr₁.JLang J) hcomp
  rw [hqq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JLang hJG hJ.2.2).some hfield hF
  have hC := fr₁.le_DLang_of_commute hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BLang (fr₁.DLang D) (fr₁.JLang J) hBT hBel₁.2 hD₁B a i
    hspan hC
  have horth : ∀ γ ∈ componentRoots (famCharHom a) i,
      ∀ δ ∈ (S₁.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
          componentRoots (famCharHom a) i,
        iform γ δ = 0 ∧ ¬ IsRoot Tag.E6 (γ + δ) := by
    obtain ⟨j, hj⟩ := exists_image_component_of_stable (famCharHom a)
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
  refine ⟨S₁, fr₁, hqq, hBT, a, i, ha, hap, hspan, h2,
    isRootComponent_componentRoots i, horth, ?_, two_mul_finrank_le_of_orbit S₁ a haT i h2⟩
  calc Nat.card B = Nat.card fr₁.BLang := fr₁.card_BLang.symm
    _ ≤ Nat.card (fr₁.DLang D) *
        p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
    _ = p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) := by
      rw [fr₁.card_DLang hDB, hDcard, pow_add]

end CFSG.StandardType.TableCRes

end
