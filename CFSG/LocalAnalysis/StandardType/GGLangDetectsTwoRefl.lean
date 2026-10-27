module

public import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped commutatorElement

private theorem j4rEqOne {L : Type} [Field L] [CharP L 2] {ε : L} (h : ε * ε = 1) : ε = 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hsq : (ε + 1) * (ε + 1) = 0 := by
    have : (ε + 1) * (ε + 1) = ε * ε + 2 * ε + 1 := by ring
    rw [this, h, h2, zero_mul, add_zero, ← two_mul, h2, zero_mul]
  have h1 : ε + 1 = 0 := mul_self_eq_zero.1 hsq
  rw [eq_neg_of_add_eq_zero_left h1, CharTwo.neg_eq]

private def j4rConj {τ : Tag}
    {L : Type} [Field L] (g : ModGL τ L) (w : WeylGroup τ) : Prop :=
  ∀ ξ, IsRoot τ ξ → ∃ μ : Lˣ, ∀ c : L,
    g * pinnedX τ L ξ c * g⁻¹ = pinnedX τ L (w • ξ) ((μ : L) * c)

private theorem j4rConj_one {τ : Tag}
    {L : Type} [Field L] : j4rConj (1 : ModGL τ L) (1 : WeylGroup τ) := by
  intro ξ _
  exact ⟨1, fun c => by simp⟩

private theorem j4rConj_mul {τ : Tag}
    {L : Type} [Field L] {g h : ModGL τ L} {x y : WeylGroup τ}
    (hg : j4rConj g x) (hh : j4rConj h y) : j4rConj (g * h) (x * y) := by
  intro ξ hξ
  obtain ⟨μ₂, hμ₂⟩ := hh ξ hξ
  obtain ⟨μ₁, hμ₁⟩ := hg (y • ξ) (IsRoot.smul hξ y)
  refine ⟨μ₁ * μ₂, fun c => ?_⟩
  calc g * h * pinnedX τ L ξ c * (g * h)⁻¹
      = g * (h * pinnedX τ L ξ c * h⁻¹) * g⁻¹ := by group
    _ = g * pinnedX τ L (y • ξ) ((μ₂ : L) * c) * g⁻¹ := by rw [hμ₂ c]
    _ = pinnedX τ L (x • y • ξ) ((μ₁ : L) * ((μ₂ : L) * c)) := hμ₁ _
    _ = pinnedX τ L ((x * y) • ξ) (((μ₁ * μ₂ : Lˣ) : L) * c) := by
        rw [mul_smul, Units.val_mul, mul_assoc]

private theorem j4rConj_inv {τ : Tag}
    {L : Type} [Field L] {g : ModGL τ L} {x : WeylGroup τ}
    (hg : j4rConj g x) : j4rConj g⁻¹ x⁻¹ := by
  intro ξ hξ
  obtain ⟨μ, hμ⟩ := hg (x⁻¹ • ξ) (IsRoot.smul hξ x⁻¹)
  refine ⟨μ⁻¹, fun c => ?_⟩
  have h1 := hμ (((μ⁻¹ : Lˣ) : L) * c)
  have e : (μ : L) * (((μ⁻¹ : Lˣ) : L) * c) = c := by
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [smul_inv_smul, e] at h1
  rw [inv_inv, ← h1]
  group

theorem langRatKills_of_reflection_commutator
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    {a : Fin τ.rank → Lˣ} (b : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a))
    {Ψs : Set (Fin τ.rank → ℤ)} (hΨ : Ψs ⊆ componentRoots (rootCharHom a) i)
    (hstab : ∀ δ ∈ Ψs, S.ρ δ = δ ∨ S.ρ δ = -δ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψs) {u : WeylGroup τ}
    (hu : u ∈ Subgroup.closure {s : WeylGroup τ | ∃ δ ∈ Ψs, s = rootReflection δ})
    (horth : iform (u • γ) γ = 0)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b}) :
    rootChar b γ = 1 := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  have hrootΨ : ∀ δ ∈ Ψs, IsRoot τ δ := fun δ hδ => isRoot_of_mem_componentRoots (hΨ hδ)
  have hγr : IsRoot τ γ := hrootΨ γ hγ
  have hmemR : ∀ δ ∈ Ψs, rootSL2 τ L δ WSL ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    intro δ hδ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact rootSL2_mem_rootSpan_of_mem_rationalRoots S i ⟨0, δ, hΨ hδ, rfl⟩ WSL
    · exact rootSL2_WSL_mem_Γ_of_rho S hτ hq hAlg (hrootΨ δ hδ) (hstab δ hδ)
  have key : ∀ w : WeylGroup τ,
      w ∈ Subgroup.closure {s : WeylGroup τ | ∃ δ ∈ Ψs, s = rootReflection δ} →
      ∃ g ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i, j4rConj g w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨δ, hδ, rfl⟩ := hx
      refine ⟨rootSL2 τ L δ WSL, hmemR δ hδ, fun ξ hξ => ?_⟩
      obtain ⟨μ, hμ⟩ :=
        CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_conj_pinnedX (K := L) (hrootΨ δ hδ) hξ
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c, rootReflection_smul (hrootΨ δ hδ)]
      rfl
    | one => exact ⟨1, one_mem _, j4rConj_one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg, hgx⟩ := hx
      obtain ⟨h, hh, hhy⟩ := hy
      exact ⟨g * h, mul_mem hg hh, j4rConj_mul hgx hhy⟩
    | inv x _ hx =>
      obtain ⟨g, hg, hgx⟩ := hx
      exact ⟨g⁻¹, inv_mem hg, j4rConj_inv hgx⟩
  obtain ⟨g₁, hg₁, hg₁act⟩ := key (rootReflection γ) (Subgroup.subset_closure ⟨γ, hγ, rfl⟩)
  obtain ⟨g, hg, hgact⟩ := key u hu
  have hperp : iform γ (u⁻¹ • γ) = 0 := by
    have h := iform_smul u⁻¹ (u • γ) γ
    rwa [inv_smul_smul, horth] at h
  have hw : (⁅rootReflection γ, u⁆ : WeylGroup τ) • γ = -γ := by
    rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, rootReflection_inv hγr,
      rootReflection_smul_of_iform_eq_zero hγr hperp, smul_inv_smul,
      rootReflection_smul_self hγr]
  obtain ⟨c', hc', μ, hμ⟩ : ∃ c' ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      ∃ μ : Lˣ, ∀ t : L, c' * pinnedX τ L γ t * c'⁻¹ = pinnedX τ L (-γ) ((μ : L) * t) := by
    refine ⟨⁅g₁, g⁆, Subgroup.commutator_mem_commutator hg₁ hg, ?_⟩
    have hcact : j4rConj ⁅g₁, g⁆ ⁅rootReflection γ, u⁆ := by
      simp only [commutatorElement_def]
      exact j4rConj_mul (j4rConj_mul (j4rConj_mul hg₁act hgact) (j4rConj_inv hg₁act))
        (j4rConj_inv hgact)
    obtain ⟨μ, hμ⟩ := hcact γ hγr
    exact ⟨μ, fun t => by rw [hμ t, hw]⟩
  have hd := hle hc'
  rw [Subgroup.mem_centralizer_singleton_iff] at hd
  set d := rootDiagUnit τ b with hdd
  have hcd : c' * d * c'⁻¹ = d := by rw [hd, mul_assoc, mul_inv_cancel, mul_one]
  have hcd' : c' * d⁻¹ * c'⁻¹ = d⁻¹ := by
    have h := congrArg (fun x => x⁻¹) hcd
    simpa [mul_assoc] using h
  have h1 : c' * (d * pinnedX τ L γ 1 * d⁻¹) * c'⁻¹ =
      pinnedX τ L (-γ) ((μ : L) * ((rootChar b γ : Lˣ) * 1)) := by
    rw [hdd, rootDiagUnit_conj_pinnedX b hγr 1, hμ]
  have h2 : c' * (d * pinnedX τ L γ 1 * d⁻¹) * c'⁻¹ =
      pinnedX τ L (-γ) ((rootChar b (-γ) : Lˣ) * ((μ : L) * 1)) := by
    calc c' * (d * pinnedX τ L γ 1 * d⁻¹) * c'⁻¹
        = (c' * d * c'⁻¹) * (c' * pinnedX τ L γ 1 * c'⁻¹) * (c' * d⁻¹ * c'⁻¹) := by group
      _ = d * (c' * pinnedX τ L γ 1 * c'⁻¹) * d⁻¹ := by rw [hcd, hcd']
      _ = d * pinnedX τ L (-γ) ((μ : L) * 1) * d⁻¹ := by rw [hμ 1]
      _ = pinnedX τ L (-γ) ((rootChar b (-γ) : Lˣ) * ((μ : L) * 1)) := by
          rw [hdd, rootDiagUnit_conj_pinnedX b (IsRoot.neg hγr) _]
  have h3 := pinnedX_injective τ L (-γ) (h1.symm.trans h2)
  rw [CFSG.ClassicalInvolution.ModelFacts.Levi.rootChar_neg' b γ] at h3
  have h4 : ((rootChar b γ : Lˣ) : L) * ((rootChar b γ : Lˣ) : L) = 1 := by
    have hμ0 : (μ : L) ≠ 0 := μ.ne_zero
    have h5 : (μ : L) * ((rootChar b γ : Lˣ) : L) = (μ : L) * (((rootChar b γ)⁻¹ : Lˣ) : L) :=
      calc (μ : L) * ((rootChar b γ : Lˣ) : L) = (μ : L) * (((rootChar b γ : Lˣ) : L) * 1) := by
            rw [mul_one]
        _ = (((rootChar b γ)⁻¹ : Lˣ) : L) * ((μ : L) * 1) := h3
        _ = (μ : L) * (((rootChar b γ)⁻¹ : Lˣ) : L) := by rw [mul_one, mul_comm]
    have h6 := mul_left_cancel₀ hμ0 h5
    calc ((rootChar b γ : Lˣ) : L) * ((rootChar b γ : Lˣ) : L)
        = ((rootChar b γ : Lˣ) : L) * (((rootChar b γ)⁻¹ : Lˣ) : L) := by rw [← h6]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Units.ext (j4rEqOne h4)

end CFSG.StandardType.LangRat

end
