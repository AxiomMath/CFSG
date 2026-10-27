module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.ClassicalInvolution.WeakCT.Spin
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

section PresD

variable {G : Type} [Group G] [Finite G]

theorem ggPresentsG0_typeD_of_system {n f : ℕ} (hn : 4 ≤ n) (hq : 4 ≤ 2 ^ f) {H : Subgroup G}
    {U : Fin n → Subgroup ↥H}
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : (ggU .POmegaPlus n f).K →* G,
      GGPresentsG0 H (ggU .POmegaPlus n f).D .POmegaPlus n f ψ := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0] at hq
    norm_num at hq
  have hn3 : 3 ≤ n := by omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq' : 4 ≤ Nat.card (GaloisField 2 f) := by rw [hK]; exact hq
  have hadm : StatedLieAdmissible .POmegaPlus n 2 f := ⟨Nat.prime_two, hf, hn⟩
  obtain ⟨Ψ₀, hsurj, hker, hqs, _hcenter, hmodel, _hlevi⟩ :=
    weakCT_spinPlus (F := GaloisField 2 f) (X := ↥H) hadm hn3 hK hq' U hgen hcomm hpair
  have hU : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  rw [hU]
  refine ⟨H.subtype.comp Ψ₀, ⟨⟨hadm, ?_⟩, ⟨?_, ?_⟩, ?_, hmodel⟩⟩
  · show 2 ≤ (Spin.plusDatum n (GaloisField 2 f) hn3).rank
    simp only [Spin.plusDatum]
    omega
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective Ψ₀ H.subtype (Subgroup.subtype_injective H)]
    exact hker
  · exact hqs.1.commutator_eq_top

end PresD

end CFSG.StandardType

end
