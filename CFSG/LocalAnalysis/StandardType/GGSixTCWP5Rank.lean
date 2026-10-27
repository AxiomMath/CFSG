module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint CFSG.StandardType CFSG.Open CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)
open CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Rank

private theorem w7K_bridge {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : Ψ.Finite) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ := by
  let g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun v i => (v i : ℚ)
  let f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℚ) :=
    { toFun := g
      map_add' := by intro a b; funext i; simp [g]
      map_smul' := by intro a b; funext i; simp [g] }
  have hfinj : Function.Injective f := by
    intro a b h
    funext i
    have h' := congrFun h i
    exact Int.cast_injective h'
  have : Module.Finite ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Module.Finite.span_of_finite ℤ (hΨ.image f)
  have hmap : (Submodule.span ℤ Ψ).map f = Submodule.span ℤ (f '' Ψ) := by
    rw [Submodule.map_span]
  have heq : Module.finrank ℤ (Submodule.span ℤ Ψ) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) := by
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfinj (Submodule.span ℤ Ψ))
  have hM : Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Submodule.finrank_span_eq_finrank_span ℤ ℚ (f '' Ψ)
  have hcomp : compRank Ψ = Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) := by
    rw [compRank]
    rfl
  rw [hcomp, hM]
  exact heq

private theorem w7K_finite
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) : Ψ.Finite :=
  (CFSG.Blueprint.Chevalley.finite_setOf_isRoot (τ := τ)).subset
    (fun α hα => hΨ.isRoot α hα)

private theorem w7K_lab_eq {lab' : CFSG.Assembly.LargeEvenLabel}
    (htag : markTag lab' = .PSL) (hrank : markRank lab' = 2)
    (hchar : markChar lab' = 2) (hdeg : markDeg lab' = 3) :
    lab' = ⟨CFSG.Assembly.LargeEvenLieTag.A, 1, 3⟩ := by
  obtain ⟨t, rr, nn⟩ := lab'
  cases t <;>
    simp only [markTag, markRank, markChar, markDeg,
      CFSG.Assembly.LargeEvenLabel.mk.injEq] at htag hrank hchar hdeg ⊢ <;>
    (try split_ifs at htag hrank hchar hdeg) <;> simp_all
  omega

private theorem w7K_rank_eq_one
    {G : Type} [Group G] (hcen : Subgroup.center G = ⊥)
    {r N n : ℕ} {k : TwistKind}
    (hmod : LieModel G .PSL 2 2 3)
    (hΛ : CFSG.Assembly.LargeEvenInLambda2 (componentLabel r N k n))
    (hhas : GGHasLabel (componentLabel r N k n) G) : r = 1 := by
  obtain ⟨lab', hlab', htag, hrank, hchar, hdeg, hraw'⟩ :=
    exists_label_rawDatum_of_lieModel hcen hmod
  have hhas' : GGHasLabel lab' G := hraw'
  have hiso : GGLabelIso (componentLabel r N k n) lab' :=
    ggLabelRigidInput_holds (componentLabel r N k n) lab' G hΛ hlab' hhas hhas'
  have hlab'_eq : lab' = ⟨CFSG.Assembly.LargeEvenLieTag.A, 1, 3⟩ :=
    w7K_lab_eq htag hrank hchar hdeg
  rw [hlab'_eq] at hiso
  have hcl : componentLabel r N k n = ⟨CFSG.Assembly.LargeEvenLieTag.A, 1, 3⟩ := by
    rcases hiso with h | h | h | h | h | h | h | h
    · exact h
    · rcases h.2.1 with h2 | h2 <;> nomatch h2
    · obtain ⟨-, h2⟩ := h
      simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at h2
      omega
    · obtain ⟨-, h2⟩ := h
      simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at h2
      omega
    · obtain ⟨-, h2⟩ := h
      simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at h2
      omega
    · obtain ⟨-, h2⟩ := h
      simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at h2
      omega
    · obtain ⟨-, h2⟩ := h
      simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at h2
      omega
    · obtain ⟨h1, -⟩ := h
      simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at h1
      omega
  cases k <;> simp only [componentLabel] at hcl
  · split_ifs at hcl
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      exact hcl.2.1
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      nomatch hcl.1
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      nomatch hcl.1
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      nomatch hcl.1
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      nomatch hcl.1
  · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
    nomatch hcl.1
  · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
    nomatch hcl.1
  · split_ifs at hcl
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      nomatch hcl.1
    · simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hcl
      nomatch hcl.1

theorem uframeO_conclude_psl28
    (hField : UFieldInput Tag.E6) (hL : LangFamilyCompLabel)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S₁ : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    (fr₁ : GGTCUFrameO G₀ B (ModGL Tag.E6 (AlgebraicClosure K))) (hΘ : fr₁.Θ.range = S₁.Γ)
    (hBT : fr₁.BimgO ≤ S₁.D.torus) (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hBel : IsElemAbelian p B) (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hJ28 : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3) : Nat.card B ≤ p ^ 3 := by
  classical
  have hBel₁ : IsElemAbelian p fr₁.BimgO := fr₁.isElemAbelian_BimgO hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BimgO := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.νinj).toEquiv
  have hD₁B : fr₁.DimgO D ≤ fr₁.BimgO := fr₁.DimgO_le_BimgO
  have hpar : ∀ u : fr₁.DimgO D, ∃ c : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL Tag.E6 (AlgebraicClosure K)) = rootDiagUnit Tag.E6 c ∧ ∀ j, c j ^ p = 1 :=
    fun u => exists_param_of_torus (hBT (hD₁B u.2)).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit Tag.E6 (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hBT (hD₁B u.2)
  have hrange : (Set.range fun u : fr₁.DimgO D => rootDiagUnit Tag.E6 (a u)) =
      ((fr₁.DimgO D : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :
        Set (ModGL Tag.E6 (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit Tag.E6 (a u) ∈
        (fr₁.DimgO D : Set (ModGL Tag.E6 (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JimgO J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DimgO D => rootDiagUnit Tag.E6 (a u))) := by
    rw [hrange, ← hΘ]
    exact fr₁.isComponentOf_JimgO hBN hDB hJG hJ
  obtain ⟨i, hspan, -⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DimgO D) a haT hap (fr₁.JimgO J) hcomp
  obtain ⟨n, -, hlab⟩ :=
    hL Tag.E6 (AlgebraicClosure K) 5 p S₁ (Or.inl rfl) hp hp2 (fr₁.DimgO D) a haT hap
      (fr₁.JimgO J) hcomp i hspan
  obtain ⟨hΛ, -, hhas, -⟩ := hlab
  have hequiv := (fr₁.nonempty_equiv_JimgO hJG hJ.2.2).some
  have hhasJ : GGHasLabel
      (componentLabel (compRank (componentRoots (famCharHom a) i))
        (componentRoots (famCharHom a) i).ncard
        (twistKindOf S₁.ρ (componentRoots (famCharHom a) i)) n)
      (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv hequiv.symm hhas
  have hcen : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ :=
    center_quot_eq_bot_of_isQuasisimple hJ.2.2
  have hrank1 : compRank (componentRoots (famCharHom a) i) = 1 :=
    w7K_rank_eq_one hcen hJ28 hΛ hhasJ
  have hfin : (componentRoots (famCharHom a) i).Finite :=
    w7K_finite (isRootComponent_componentRoots (i := i))
  have hfr : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) = 1 := by
    rw [w7K_bridge _ hfin, hrank1]
  have hC := fr₁.le_DimgO_of_commute hBN hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BimgO (fr₁.DimgO D) (fr₁.JimgO J) hBT hBel₁.2 hD₁B
    a i hspan hC
  calc Nat.card B = Nat.card fr₁.BimgO := fr₁.card_BimgO.symm
    _ ≤ Nat.card (fr₁.DimgO D) *
        p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
    _ = p ^ 2 * p ^ 1 := by rw [fr₁.card_DimgO hDB, hDcard, hfr]
    _ = p ^ 3 := by ring

end Rank

end CFSG.StandardType.TableCRes

end
