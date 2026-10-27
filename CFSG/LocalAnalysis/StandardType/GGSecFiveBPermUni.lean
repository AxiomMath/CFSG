module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggG0_eq_sup_of_uniCell (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {f : ℕ} {K : Subgroup G} {i0 : Fin n}
    (hSO : GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta f K i0 ∨
      GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta f K i0) :
    ggG0 p B x L D J = L ⊔ K := by
  have hK : K ∈ 𝒦 := hSO.elim (fun h => h.2.1) (fun h => h.2.1)
  have hKeta : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 :=
    hSO.elim (fun h => h.2.2.2) (fun h => h.2.2.2)
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hpres (by omega) hNbr hK ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
  rw [hJoin]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hAut, hKeta]
  exact aPermutationFull_sup_bCoordinateBlock p (by omega) i0

section Split


theorem ggSecFiveBPermOffSpUniInput_of_fields (hQ4 : GGSecFiveBPermUniQGeFourInput)
    (hQ2 : GGSecFiveBPermUniQTwoInput) : GGSecFiveBPermOffSpUniInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  have hU' : GGInnerDiagOnLabel (fun p lab => (GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n) ∨
      (GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1)) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨?_, h.2⟩) hU
    rcases le_or_gt 2 lab.n with h2 | h2
    · exact Or.inl ⟨h.1, h2⟩
    · exact Or.inr ⟨h.1, by omega⟩
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n)
      (T := fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) hU' with h4 | h2
  · exact hQ4 G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB h4
  · exact hQ2 G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB h2

theorem ggSecFiveData_of_uniCell (hS : GGSecFiveBPermUniSpChartInput)
    (hO : GGSecFiveBPermUniOmInput) (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hT : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {n : ℕ} (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hCell : ¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n),
      GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0)
    {f : ℕ} {K : Subgroup G} {i0 : Fin n} (hf : 2 ≤ f)
    (hSO : GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta f K i0 ∨
      GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta f K i0) :
    GGSecFiveData p B x L D J := by
  have hLK := ggG0_eq_sup_of_uniCell hJ hR e hpres (by omega) hJoin hAut hNbr hSO
  rcases hSO with hSp | hOm
  · obtain ⟨s, rfl, κ₁, κ₂, hκ₁, hκ₂, hsup, hagree, hlong, hcross₁, hcross₂⟩ :=
      hS G p B Bs x L D J 𝒦 hR hT _ e hpres hn eta hJoin hAut hNbr hG0 hCell f K i0 hf hSp
    exact ggSecFiveData_of_spSpCharts (by omega) hf κ₁ κ₂ hκ₁ hκ₂ hagree hlong hcross₁ hcross₂
      (hLK.trans hsup.symm)
  rcases hO G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell f K i0 hf hOm with
    ⟨ψ, hker, hrange⟩ | ⟨ψ, hker, hrange⟩
  · exact ggSecFiveData_of_psi_POmegaPlus ⟨Nat.prime_two, by omega, by omega⟩
      (by rw [bnRank]; omega) ψ hker (hrange.trans hLK.symm)
  · exact ggSecFiveData_of_psi_POmegaMinus ⟨Nat.prime_two, by omega, by omega⟩
      (by rw [bnRank]; omega) ψ hker (hrange.trans hLK.symm)

theorem ggSecFiveBPermUniQGeFourInput_of_rows (hN : GGSecFiveBPermUniNbrInput)
    (hS : GGSecFiveBPermUniSpChartInput) (hO : GGSecFiveBPermUniOmInput)
    (h4 : GGSecFiveBPermUniFourInput) (hJ : BMaxJoinInput) : GGSecFiveBPermUniQGeFourInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  obtain ⟨f, K, i, hf, hSO⟩ :=
    hN G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  rcases eq_or_lt_of_le hn with hn4 | hn5
  · exact h4 G p B Bs x L D J 𝒦 hR hT n e hpres hn4.symm eta hJoin hAut hNbr hG0 hCell hB f K i
      hf hSO (ggG0_eq_sup_of_uniCell hJ hR e hpres hn hJoin hAut hNbr hSO)
  exact ggSecFiveData_of_uniCell hS hO hJ hR hT e hpres hn5 eta hJoin hAut hNbr hG0 hCell hf hSO

theorem ggSecFiveBPermUniQTwoInput_of_rows
    (hN : GGSecFiveBPermUniQTwoNbrInput)
    (hS : GGSecFiveBPermUniQTwoSpInput) (hO : GGSecFiveBPermUniQTwoOmInput)
    (hX : GGSecFiveBPermUniQTwoExcInput) (hJ : BMaxJoinInput) : GGSecFiveBPermUniQTwoInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  have hn5 : 5 ≤ n := by
    by_contra h4
    obtain rfl : n = 4 := by omega
    exact not_ggInnerDiagOnLabel_unitary_four hR.1.1
      (hU.mono_label fun lab hl => ⟨Or.inl hl.1.1, hl.1.2.1, hl.1.2.2⟩)
  by_cases hz : Line63.H5.twoCenter L = ⊥
  swap
  · exact hX G p B Bs x L D J 𝒦 hR hT n e hpres hn5 eta hJoin hAut hNbr hG0 hCell hB hU hz
  obtain ⟨K, i0, hSO⟩ :=
    hN G p B Bs x L D J 𝒦 hR hT n e hpres hn5 eta hJoin hAut hNbr hG0 hCell hB hU hz
  have hLK := ggG0_eq_sup_of_uniCell hJ hR e hpres hn hJoin hAut hNbr hSO
  rcases hSO with hSp | hOm
  · exact hS G p B Bs x L D J 𝒦 hR hT n e hpres hn5 eta hJoin hAut hNbr hG0 hCell hz K i0 hSp hLK
  rcases hO G p B Bs x L D J 𝒦 hR hT n e hpres hn5 eta hJoin hAut hNbr hG0 hCell hz K i0 hOm with
    ⟨ψ, hker, hrange⟩ | ⟨ψ, hker, hrange⟩
  · exact ggSecFiveData_of_psi_POmegaPlus ⟨Nat.prime_two, le_rfl, by omega⟩
      (by rw [bnRank]; omega) ψ hker (hrange.trans hLK.symm)
  · exact ggSecFiveData_of_psi_POmegaMinus ⟨Nat.prime_two, le_rfl, by omega⟩
      (by rw [bnRank]; omega) ψ hker (hrange.trans hLK.symm)

theorem ggSecFiveBPermOffSpUniInput_of_rows (hN : GGSecFiveBPermUniNbrInput)
    (hS : GGSecFiveBPermUniSpChartInput) (hO : GGSecFiveBPermUniOmInput)
    (h4 : GGSecFiveBPermUniFourInput) (hQ2 : GGSecFiveBPermUniQTwoInput) (hJ : BMaxJoinInput) :
    GGSecFiveBPermOffSpUniInput :=
  ggSecFiveBPermOffSpUniInput_of_fields (ggSecFiveBPermUniQGeFourInput_of_rows hN hS hO h4 hJ) hQ2

end Split

end CFSG.StandardType

end
