module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFixA
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFixC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem not_forall_odd_mem_centralizer_V₀ (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ)
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3) :
    ¬ (∀ c : ↥(conjClosure V H), Odd (orderOf c) →
        φ c ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype →
        (c : G) ∈ centralizer (V₀ : Set G)) := by
  intro hcen
  have cfg : ExCfg M V₀ V U S H φ p := ⟨h1, h5, hS, h, hH, hV, hQ, hφ, hX, hp, hN, hNc⟩
  exact cfg.false_of_kernel (fun q hq => cfg.centralizer_closure_of_map_mem_center hcen hq)
    (fun q hqN hq => cfg.map_mem_center_of_mem_centralizer_closure hqN hq)

theorem IsMinFam16.exists_odd_not_mem_centralizer_V₀ (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ)
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3) :
    ∃ c : ↥(conjClosure V H), Odd (orderOf c) ∧
      φ c ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype ∧
        (c : G) ∉ centralizer (V₀ : Set G) := by
  by_contra hcon
  rw [not_exists] at hcon
  exact not_forall_odd_mem_centralizer_V₀ h1 h5 hS h hH hV hQ hφ hX hp hN hNc
    (fun c hodd hcenter => by
      by_contra hmem
      exact hcon c ⟨hodd, hcenter, hmem⟩)

end CFSG.LocalAnalysis.WeakClosure81

end
