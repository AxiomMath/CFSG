module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.TCX.F4.LayerClaims
public import CFSG.RankThree.PartOne.S11d.LayerDecomp

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.TCX.F4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def SingleLayerData (p : ℕ) {G : Type} [Group G] (α : MulAut G) (X : Subgroup G) :
    Prop :=
  ∃ D : Subgroup G, IsComponentOf X D ∧ (∀ g ∈ D, α g ∈ D) ∧
    (∀ D' : Subgroup G, IsComponentOf X D' → D' = D) ∧
    (∀ g ∈ X, α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ D) ∧ LayerClaimsF4 p α D

section Engine

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [CharP L 2]
  [Algebra.IsAlgebraic K L]

theorem singleLayerData_of_engine {p : ℕ} (hp : p.Prime) {σ : K ≃+* K} {Φ₀ Fr : L →+* L}
    (hΦ₀K : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c))
    (hFrc : ∀ c, Fr c = c ^ Nat.card K) {n₀ g₀ : ModGL τ L}
    (hn₀fix : Units.map (entrywiseHom Φ₀) n₀ = n₀) (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Units.map (entrywiseHom Φ₀) g₀ = g₀ * n₀)
    (hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u)
    (hperf : ∀ Y : Subgroup (ModGL τ L), Finite Y → Y ≤ adjointGroup τ L →
      (∀ y ∈ Y, Units.map (entrywiseHom Fr) y = y) → ⁅Y, Y⁆ = Y → Y ≤ (adjEmb τ K L).range)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf (n₀ ^ p) (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (P : Unit → Subgroup (ModGL τ L)) (hfam : IsSigmaFamily (n₀ ^ p) Fr S P)
    (hjoin : rootSpan τ L S ⊓ twistedFixedPoints (n₀ ^ p) (Units.map (entrywiseHom Fr)) ≤ P ())
    {x : adjointGroup τ K} (hxord : orderOf x = p) {c : adjointGroup τ K}
    (hcσ : entrywiseAdjointAut τ σ c = c)
    (hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
      (subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) S))
    (hker : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ → rootCharKernel a ⊆ S)
    (hmodel : ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D),
      Function.Injective ρ' ∧ ρ'.range = P () ∧
      (∀ d, n₀ * Units.map (entrywiseHom Φ₀) (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q) :
    SingleLayerData p (entrywiseAdjointAut τ σ) (Subgroup.centralizer ({x} : Set (adjointGroup τ K))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hg₀N : Units.map (entrywiseHom Fr) g₀ = g₀ * n₀ ^ p := by
    rw [hΦK, iterate_lang (Units.map (entrywiseHom Φ₀)) hn₀fix hg₀ p]
  have hjoin' : rootSpan τ L S ⊓ twistedFixedPoints (n₀ ^ p) (Units.map (entrywiseHom Fr)) ≤
      ⨆ i : Unit, P i := by
    rw [iSup_unique]
    exact hjoin
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hodd⟩ := layerData_structure hp Fr hFrc (n₀ ^ p) g₀
    hg₀C hg₀N hperf hstab hS hSn P hfam hjoin' (fun i j hij => absurd (Subsingleton.elim i j) hij)
    hxord c hc hker
  obtain ⟨D, _, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ := hmodel
  have hPrange' : ρ'.range ≤ (psiTilde τ K L g₀ c).range := by
    rw [hρ'range]
    exact hPrange ()
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push (psiTilde τ K L g₀ c)
    (psiTilde_injective g₀ c) ρ' hρ'inj hPrange'
  have hQ : φ.range = layerComp g₀ c P () := by
    rw [hφrange, hρ'range]
    rfl
  have hασ : ∀ d', entrywiseAdjointAut τ σ (φ d') = φ (τ' d') := fun d' => by
    apply psiTilde_injective g₀ c
    rw [← psiTilde_entrywise hΦ₀K hg₀ hcσ, hψφ, hρ'compat, ← hψφ]
  have hstabQ : ∀ g ∈ layerComp g₀ c P (), entrywiseAdjointAut τ σ g ∈ layerComp g₀ c P () := by
    intro g hg
    rw [← hQ] at hg ⊢
    obtain ⟨d, rfl⟩ := hg
    exact ⟨τ' d, (hασ d).symm⟩
  refine ⟨layerComp g₀ c P (), hcomp (), hstabQ, fun D' hD' => ?_, fun g hg hgσ hk => ?_,
    hclaims (entrywiseAdjointAut τ σ) φ hφinj hασ _ hQ⟩
  · obtain ⟨i, hi⟩ := isComponentOf_eq_of_decomposition (fun i : Unit => layerComp g₀ c P i)
      hcomp hsolv hD'
    rw [hi]
  · have h := mem_of_two_power_of_odd_index hnormal hodd hg hk
    rwa [iSup_unique] at h

end Engine

end CFSG.RankThree.PartOne.TCX
