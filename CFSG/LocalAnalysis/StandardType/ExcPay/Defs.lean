module

public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGActualQuadraticField
public import CFSG.LocalAnalysis.StandardType.GGResidualA2Pair
public import Certificates.Certificate13723
public import Certificates.Certificate13724

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

@[expose] def rootKerFam (τ : Tag) (p : ℕ) (k : Fin τ.rank) : Type :=
  {a : Fin τ.rank → GGLˣ // (∀ i, a i ^ p = 1) ∧ a k = 1}

theorem finite_rootKerFam (τ : Tag) {p : ℕ} (hp : 0 < p) (k : Fin τ.rank) :
    Finite (rootKerFam τ p k) := by
  have hne : NeZero p := ⟨hp.ne'⟩
  have hfin : Finite (rootsOfUnity p GGL) := inferInstance
  let f : rootKerFam τ p k → (Fin τ.rank → rootsOfUnity p GGL) :=
    fun a j => ⟨a.1 j, (mem_rootsOfUnity _ _).2 (a.2.1 j)⟩
  exact Finite.of_injective f fun a b h => Subtype.ext (funext fun j =>
    congrArg Subtype.val (congrFun h j))

section Square


structure ExcPaySquare {G : Type} [Group G] (t : StatedLieTag) (ht : GGExcFive t) (f p : ℕ)
    (Bs X : Subgroup G) where
  M : GGDatumModel t f p ht
  ψ : ↥M.D.Γ →* G
  ψ_inj : Function.Injective ψ
  ψ_range : ψ.range = X
  β : ↥Bs →* ModGL (langTag t) GGL
  pres : ∀ (b : ↥Bs) (y : ↥M.D.Γ), β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ
  compat : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
    ψ ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, pres b y⟩ = (b : G) * ψ y * (b : G)⁻¹
  torus : ∀ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) →
    rootDiagUnit (langTag t) a ∈ M.D.torus
  s : Fin (langTag t).rank → MulAut ↥Bs
  s_mem : ∀ k, s k ∈ ggAutomizer X Bs
  s_refl : ∀ k, GGIsReflection p (s k)
  fix : ∀ k (z : ModGL (langTag t) GGL),
    z ∈ Subgroup.closure
        (Set.range fun a : rootKerFam (langTag t) p k => rootDiagUnit (langTag t) a.1) ↔
      ∃ b : ↥Bs, s k b = b ∧ β b = z

end Square

section Pair


theorem pair_of_toral_a2_roots_original_member_actualField
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    (α₀ α₁ : Fin (langTag t).rank → ℤ)
    (hrootpair : CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair α₀ α₁)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin (langTag t).rank → GGLˣ)
    (a₁ : I₁ → Fin (langTag t).rank → GGLˣ)
    (htor₀ : ∀ i, rootDiagUnit (langTag t) (a₀ i) ∈ M.D.torus)
    (htor₁ : ∀ i, rootDiagUnit (langTag t) (a₁ i) ∈ M.D.torus)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) = {α₀, -α₀})
    (hk₁ : famKernel (Set.range a₁) = {α₁, -α₁})
    (ψ : ↥M.D.Γ →* G) (hψinj : Function.Injective ψ) (hX : ψ.range = X)
    (β : ↥Bs →* ModGL (langTag t) GGL)
    (hpres : ∀ (b : ↥Bs) (y : ↥M.D.Γ), β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ)
    (hcompat : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      ψ ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
        (b : G) * ψ y * (b : G)⁻¹)
    (r s : MulAut ↥Bs)
    (hH₀ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ↔
        ∃ b : ↥Bs, r b = b ∧ β b = z)
    (hH₁ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) ↔
        ∃ b : ↥Bs, s b = b ∧ β b = z) :
    ∃ θG : Su (actualQuadraticSubfield f) 2 f 3 →* G,
      Function.Injective θG ∧ θG.range ≤ X ∧
      (B12 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs r ∧
      (B23 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs s ∧
      UnitaryBlockStandardPair (actualQuadraticSubfield f) 2 f θG.range
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  have htag : langTag t = .F4 ∨ langTag t = .D4 ∨ langTag t = .E6 ∨
      langTag t = .E7 ∨ langTag t = .E8 := by
    rcases langTag_five t with h | h | h | h <;> simp [h]
  obtain ⟨j, σ, hpair, h01, h12, _⟩ :=
    CFSG.StandardType.LieCore.exists_a2Frame_of_a2Pair (L := GGL) htag hrootpair
  have hk₀' : famKernel (Set.range a₀) = {σ 0 1, -σ 0 1} := by
    simpa only [h01] using hk₀
  have hk₁' : famKernel (Set.range a₁) = {σ 1 2, -σ 1 2} := by
    simpa only [h12] using hk₁
  exact CFSG.StandardType.ResidualA2Pair.pair_of_matched_frame_original_member_toral_actualField
    M (n := 0) hp hp2 hplus j σ hpair a₀ a₁ htor₀ htor₁ ha₀ ha₁ hk₀' hk₁'
    ψ hψinj hX β hpres hcompat r s hH₀ hH₁

end Pair

end CFSG.StandardType.ExcPay
