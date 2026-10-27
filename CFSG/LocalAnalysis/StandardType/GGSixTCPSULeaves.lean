module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem PSULiftHyp.of_ggTCHyp
    {X : Type} [Group X] [Finite X] {n p : ℕ} {G₀ B D J L : Subgroup X} {x : X} {g : ℕ}
    {ψ : (ggU .PSU n (g + 1)).K →* X} (h : GGTCHyp .PSU n (g + 1) ψ p G₀ B D J L x) :
    PSULiftHyp n g ψ p B where
  adm := h.adm
  ker := h.ker
  prime := h.prime
  ne_two := h.ne_two
  norm := by
    change B ≤ Subgroup.normalizer (ψ.range : Set X)
    rw [h.range]
    exact h.b_norm
  diag := fun b hb => h.b_diag b hb
  elem := h.b_elem
  card4 := h.b_card
  faithful := by
    change B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥
    rw [h.range]
    exact h.b_faithful
  hN := fun hpdiv => h.b_HN (Or.inr ⟨rfl, hpdiv⟩)

end CFSG.StandardType.TableCRes
