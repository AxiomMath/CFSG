module

public import CFSG.LocalAnalysis.StandardType.GGSelectedPSUModel
public import CFSG.LocalAnalysis.StandardType.GGPSUFirstPlane
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux
import CFSG.LieType.Steinberg.CentralExt.SUThreeThree

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan Matrix

theorem exists_selectedModel_PSU_block {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n) :
    ∃ (β : SU (unitaryInvolution F 2 f) n ≃* Su F 2 f n)
      (γ : Fin (Unitary.rootDatum hF n).rank → ℤ)
      (model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f) γ),
      model.phi.range.map β.toMonoidHom =
        CFSG.StandardType.ggSuPairBlock F 2 f n ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  obtain ⟨β, hβ⟩ := exists_suBridge_firstPlane (K := F) (p := 2) (f := f) (n := n) hF (by omega)
  obtain ⟨γ, model, hsupp⟩ := exists_selectedModel_PSU hF hn
  refine ⟨β, γ, model, ?_⟩
  have hle : model.phi.range.map β.toMonoidHom ≤
      CFSG.StandardType.ggSuPairBlock F 2 f n ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hβ (model.phi A) (fun i j hij => hsupp A i j hij)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  obtain ⟨eSL⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUThreeThree.nonempty_sl2_mulEquiv_SUid_two
      (p := 2) (f := f) hF
  have hblock : (blockEmb F 2 f n 2 0 (by omega)).range =
      CFSG.StandardType.ggSuPairBlock F 2 f n ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    simpa using CFSG.StandardType.ggPhanNSAPairAux_range_blockEmb2 (K := F) (p := 2) (f := f)
      (n := n) (i := 0) (by omega : 0 + 2 ≤ n)
  have h1 : Nat.card (CFSG.StandardType.ggSuPairBlock F 2 f n ⟨0, by omega⟩ ⟨1, by omega⟩) =
      Nat.card (Su F 2 f 2) := by
    rw [← hblock]
    exact (Nat.card_congr (MonoidHom.ofInjective (blockEmb_injective (by omega))).toEquiv).symm
  have h2 : Nat.card model.phi.range = Nat.card (Su F 2 f 2) := by
    rw [Nat.card_congr (MonoidHom.ofInjective model.injective).toEquiv.symm]
    exact Nat.card_congr eSL.toEquiv
  have h3 : Nat.card (model.phi.range.map β.toMonoidHom) = Nat.card model.phi.range :=
    Subgroup.card_map_of_injective β.injective
  rw [h1, h3, h2]

end CFSG.StandardType.SelectedRoot

end
