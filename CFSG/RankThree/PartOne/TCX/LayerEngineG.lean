module

public import CFSG.RankThree.PartOne.KLCE.EngineG
public import CFSG.RankThree.PartOne.KE.E6TwFourFamily
public import CFSG.RankThree.PartOne.TCX.LayerEngine

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.TCX.F4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section EngineG

variable {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]

theorem singleLayerData_of_engineG (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (F₀ Φ : ModGL τ L →* ModGL τ L) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = F₀ (ι y)) {p : ℕ} (hp : p.Prime) (hιΦ : ∀ y, Φ (ι y) = ι y)
    (hodd : ∀ h ∈ torusGroup τ L, ∃ m : ℕ, Odd m ∧ h ^ m = 1)
    (n₀ N g₀ : ModGL τ L) (hg₀C : g₀ ∈ adjointGroup τ L) (hg₀F : F₀ g₀ = g₀ * n₀)
    (hg₀ : Φ g₀ = g₀ * N)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf N Φ →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (P : Unit → Subgroup (ModGL τ L)) (hfam : IsSigmaFamilyΦ N Φ S P)
    (hjoin : rootSpan τ L S ⊓ twistedFixedPoints N Φ ≤ P ())
    {x : C} (hx : orderOf x = p) (c : C) (hcα : α₀ c = c)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g₀ (subtorusSigma N Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ → rootCharKernel a ⊆ S)
    (hmodel : ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D),
      Function.Injective ρ' ∧ ρ'.range = P () ∧
      (∀ d, n₀ * F₀ (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hjoin' : rootSpan τ L S ⊓ twistedFixedPoints N Φ ≤ ⨆ i : Unit, P i := by
    rw [iSup_unique]
    exact hjoin
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hoddi⟩ := layerData_structure_gen ι hι hιC Φ hιΦ hodd hp
    N g₀ hg₀C hg₀ hperf hstab hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hjoin'
    (fun i j hij => absurd (Subsingleton.elim i j) hij) hx c hc hkerZ
  obtain ⟨D, hD, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ := hmodel
  have hPrange' : ρ'.range ≤ (psiG ι g₀ c).range := by
    rw [hρ'range]
    exact hPrange ()
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push (psiG ι g₀ c)
    (psiG_injective hι g₀ c) ρ' hρ'inj hPrange'
  have hQ : φ.range = layerCompG ι g₀ c P () := by
    rw [hφrange, hρ'range]
    rfl
  have hασ : ∀ d', α₀ (φ d') = φ (τ' d') := fun d' => by
    apply psiG_injective hι g₀ c
    rw [← psiG_intertwine F₀ α₀ hα₀ hg₀F hcα, hψφ, hρ'compat, ← hψφ]
  have hstabQ : ∀ g ∈ layerCompG ι g₀ c P (), α₀ g ∈ layerCompG ι g₀ c P () := by
    intro g hg
    rw [← hQ] at hg ⊢
    obtain ⟨d, rfl⟩ := hg
    exact ⟨τ' d, (hασ d).symm⟩
  refine ⟨layerCompG ι g₀ c P (), hcomp (), hstabQ, fun D' hD' => ?_, fun g hg hgσ hk => ?_,
    hclaims α₀ φ hφinj hασ _ hQ⟩
  · obtain ⟨i, hi⟩ := isComponentOf_eq_of_decomposition (fun i : Unit => layerCompG ι g₀ c P i)
      hcomp hsolv hD'
    rw [hi]
  · have h := mem_of_two_power_of_odd_index hnormal hoddi hg hk
    rwa [iSup_unique] at h

end EngineG

end CFSG.RankThree.PartOne.TCX
