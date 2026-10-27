module

public import CFSG.LieType.TwoRank.PGLMap
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart11
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart28
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicImplementersPart2

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.RankExclusion

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
      CFSG.LieType.AlgebraicGroups
  CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.StandardType.S2MathFi1035Pos
  CFSG.Open

open CFSG.StandardType.F4ExplicitPos.CyclicImplementers

open CFSG.StandardType.F4ExplicitPos.OrbitKernel

open CFSG.StandardType.F4ExplicitPos.CubicAction

open scoped Pointwise

theorem mem_normalizer_of_same_inner {G : Type*} [Group G] (H : Subgroup G) {y g : G}
    (hg : g ∈ H) (h : ∀ x ∈ H, y * x * y⁻¹ = g * x * g⁻¹) :
    y ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    show y * x * y⁻¹ ∈ H
    rw [h x hx]
    exact mul_mem (mul_mem hg hx) (inv_mem hg)
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * z * g, mul_mem (mul_mem (inv_mem hg) hz) hg, ?_⟩
    show y * (g⁻¹ * z * g) * y⁻¹ = z
    rw [h (g⁻¹ * z * g) (mul_mem (mul_mem (inv_mem hg) hz) hg)]
    group

section Gamma

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

variable {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}

variable {B : Type*} [Group B]

noncomputable def gammaOfTheta
    (i : KernelComponent χ) (Θ : B →* ModGL Tag.F4 Ω)
    (hΘZ : ∀ b : B, Θ b ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)) :
    B →* MulAut (rootSpan Tag.F4 Ω (componentRoots χ i)) :=
  (rootSpan Tag.F4 Ω (componentRoots χ i)).normalizerMonoidHom.comp
    (Θ.codRestrict _ fun b => by
      obtain ⟨g, hg, hgconj⟩ :=
        exists_mem_componentRootSpan_conj_eq_of_mem_Z_good (L := Ω) i (hΘZ b)
      exact mem_normalizer_of_same_inner (rootSpan Tag.F4 Ω (componentRoots χ i)) hg
        (fun x hx => hgconj x hx))

theorem gammaOfTheta_apply
    (i : KernelComponent χ) (Θ : B →* ModGL Tag.F4 Ω)
    (hΘZ : ∀ b : B, Θ b ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ))
    (b : B) (x : rootSpan Tag.F4 Ω (componentRoots χ i)) :
    ((gammaOfTheta i Θ hΘZ b x : rootSpan Tag.F4 Ω (componentRoots χ i)) : ModGL Tag.F4 Ω) =
      Θ b * (x : ModGL Tag.F4 Ω) * (Θ b)⁻¹ := by
  simp only [gammaOfTheta, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem gammaOfTheta_exists_conj
    (i : KernelComponent χ) (Θ : B →* ModGL Tag.F4 Ω)
    (hΘZ : ∀ b : B, Θ b ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)) :
    ∀ b : B, ∃ g : rootSpan Tag.F4 Ω (componentRoots χ i),
      MulAut.conj g = gammaOfTheta i Θ hΘZ b := by
  intro b
  refine (exists_hinner_of_mem_Z Ω i (gammaOfTheta i Θ hΘZ) ?_) b
  intro b
  exact ⟨Θ b, hΘZ b, fun x => gammaOfTheta_apply i Θ hΘZ b x⟩

end Gamma

section Kernel

theorem kappa_conjAction_eq
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {X : Type} [Group X] [Finite X] {G₀ B₁ K : Subgroup X}
    (Θ : B₁ →* ModGL Tag.F4 Ω) (η : G₀ →* ModGL Tag.F4 Ω)
    (hBG : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hKG : K ≤ G₀)
    (hBK : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hηact : ∀ (b : B₁) (y : G₀),
      η ((G₀.normalizerMonoidHom ⟨b, hBG b.2⟩) y) = Θ b * η y * (Θ b)⁻¹)
    (b : B₁) (k : K) :
    η (Subgroup.inclusion hKG (conjAction hBK b k)) =
      Θ b * η (Subgroup.inclusion hKG k) * (Θ b)⁻¹ := by
  have hι : Subgroup.inclusion hKG (conjAction hBK b k) =
      (G₀.normalizerMonoidHom ⟨b, hBG b.2⟩) (Subgroup.inclusion hKG k) := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion, conjAction_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  rw [hι]
  exact hηact b (Subgroup.inclusion hKG k)

theorem gamma_ker_le_conjAction_ker
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {X : Type} [Group X] [Finite X] {G₀ B₁ K : Subgroup X}
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (Θ : B₁ →* ModGL Tag.F4 Ω)
    (hΘZ : ∀ b : B₁, Θ b ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ))
    (η : G₀ →* ModGL Tag.F4 Ω)
    (hBG : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hKG : K ≤ G₀)
    (hBK : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hηinj : Function.Injective η)
    (hηact : ∀ (b : B₁) (y : G₀),
      η ((G₀.normalizerMonoidHom ⟨b, hBG b.2⟩) y) = Θ b * η y * (Θ b)⁻¹)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (D : LangDatum Tag.F4 Ω) (hρ : FrobRootMap D ρ)
    (hKorbit : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots χ i)))
    (hfix : ∀ b : B₁, D.step (Θ b) = Θ b) :
    (gammaOfTheta i Θ hΘZ).ker ≤ (conjAction hBK).ker := by
  intro b hb
  rw [MonoidHom.mem_ker] at hb ⊢
  have hcentralH : Θ b ∈ Subgroup.centralizer
      (rootSpan Tag.F4 Ω (componentRoots χ i) : Set (ModGL Tag.F4 Ω)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγ : gammaOfTheta i Θ hΘZ b ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hb]; rfl
    have hcoe := congrArg
      (fun z : rootSpan Tag.F4 Ω (componentRoots χ i) => (z : ModGL Tag.F4 Ω)) hγ
    rw [gammaOfTheta_apply i Θ hΘZ b ⟨x, hx⟩] at hcoe
    calc x * Θ b = (Θ b * x * (Θ b)⁻¹) * Θ b := by rw [hcoe]
      _ = Θ b * x := by group
  have hcentralK : Θ b ∈ Subgroup.centralizer
      ((η.comp (Subgroup.inclusion hKG)).range : Set (ModGL Tag.F4 Ω)) :=
    mem_centralizer_of_mem_centralizer_rootSpan D ρ hρ
      (fun γ hγ => isRoot_of_mem_componentRoots hγ) hKorbit (hfix b) hcentralH
  have hκinj : Function.Injective (η.comp (Subgroup.inclusion hKG)) :=
    hηinj.comp (Subgroup.inclusion_injective hKG)
  have hfixk : ∀ k : K, conjAction hBK b k = k := by
    intro k
    apply hκinj
    change η (Subgroup.inclusion hKG (conjAction hBK b k)) =
      η (Subgroup.inclusion hKG k)
    rw [kappa_conjAction_eq Θ η hBG hKG hBK hηact b k]
    have hcomm := Subgroup.mem_centralizer_iff.mp hcentralK
      (η (Subgroup.inclusion hKG k))
      (MonoidHom.mem_range.mpr ⟨k, rfl⟩)
    rw [← hcomm]
    group
  ext k
  simpa using hfixk k

end Kernel

section Projective

noncomputable def quotientCenterCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)

noncomputable def pglChange (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] :
    Matrix.ProjGenLinGroup n K ≃* (GL n K ⧸ CFSG.Open.StatedScalars n K) :=
  QuotientGroup.quotientMulEquivOfEq (CFSG.Open.StatedAPI.statedScalars_eq_center n K).symm

noncomputable def pslToProj {n : Type} [Fintype n] [DecidableEq n]
    {E Ω : Type} [Field E] [Field Ω] (f : E →+* Ω) :
    Matrix.ProjectiveSpecialLinearGroup n E →*
      (GL n Ω ⧸ CFSG.Open.StatedScalars n Ω) :=
  (pglChange n Ω).toMonoidHom.comp
    ((Matrix.ProjGenLinGroup.map (n := n) f).comp
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := n) (R := E)))

theorem pslToProj_injective {n : Type} [Fintype n] [DecidableEq n]
    {E Ω : Type} [Field E] [Field Ω] (f : E →+* Ω) (hf : Function.Injective f) :
    Function.Injective (pslToProj (n := n) f) :=
  (pglChange n Ω).injective.comp
    ((CFSG.LieType.TwoRank.projGenLinGroup_map_injective (n := n) f).comp
      (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := n) (R := E)))

theorem center_statedSp_eq_bot {n : ℕ} {E : Type} [Field E] [CharP E 2] :
    Subgroup.center (StatedSp n E) = ⊥ :=
  (CFSG.LieType.Universal.Symplectic.center_eq n E).trans
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n))

end Projective

section Beta

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]

variable {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}

variable (i : KernelComponent χ)

variable {X : Type} [Group X] [Finite X] {G₀ B₁ K : Subgroup X}

variable (Θ : B₁ →* ModGL Tag.F4 Ω)

theorem exists_betaOfGamma
    (hΘZ : ∀ b : B₁, Θ b ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ))
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) :
    ∃ k : ℕ, k ≠ 0 ∧ 4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k) ∧
      ∃ β : B₁ →*
          (CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω
              (TauCeti.frobeniusFixedSubfield Ω 2 k) (componentRoots χ i)) ⧸
          Subgroup.center (CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω
              (TauCeti.frobeniusFixedSubfield Ω 2 k) (componentRoots χ i)),
        β.ker = (gammaOfTheta i Θ hΘZ).ker := by
  have : Finite B₁ := Subtype.finite
  exact CFSG.StandardType.F4ExplicitPos.FiniteAction.exists_finiteSubfield_quotientAction Ω halg
    (gammaOfTheta i Θ hΘZ) (gammaOfTheta_exists_conj i Θ hΘZ)

end Beta

end CFSG.StandardType.F4ExplicitPos.RankExclusion
end

end
