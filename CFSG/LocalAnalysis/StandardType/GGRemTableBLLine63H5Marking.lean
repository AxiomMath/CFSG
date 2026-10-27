module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGUnitDvdLabelDefs

public section

namespace CFSG.StandardType.Line63.H5

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

theorem config_marking_data {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L) :
    commutator L = ⊤ ∧ ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ n) ^ 2 ∧ 1 ≤ n ∧ 3 ∣ 2 ^ n + 1 ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6),
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
          (LargeEvenGUSet (Fin 6) K (2 ^ n)),
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨hL, lab, hlab, hraw⟩ := hM
  refine ⟨hL, ?_⟩
  have h63 : GGUnitDvd63Label 3 lab := by
    obtain ⟨R, _, I, F, -, -, θ, h, -⟩ := largeEvenRawDatum_exists hraw
    exact h
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, -⟩ := h63
  dsimp only at ht hpn hl5
  subst ht hl5
  have hn : 1 ≤ n := hlab.1
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, i1, i2, hK, -, -, θ, -, -, hBN, hBI⟩ := hraw
  exact ⟨n, K, i1, i2, hK, hn, hpn, θ, hBN, hBI⟩

end CFSG.StandardType.Line63.H5

end
