module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCor123
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2n_reflCentre {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ)
    (hc : ¬ GGQ2CentreNotIn Bs D φ) : g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hHyp' : GGCorFiveTwentyHyp p B Bs x L D J := hHyp
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hc' : ∀ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∈ D := by
    intro b
    by_contra hb
    exact hc ⟨b, hb⟩
  have hconj : ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro d hd
    have hdBs : d ∈ Bs := hDBs hd
    have hphi : ((φ ⟨d, hdBs⟩ : ↥Bs) : G) = g * d * g⁻¹ := by
      simpa using hInd.2 ⟨d, hdBs⟩
    have hmem : d⁻¹ * (g * d * g⁻¹) ∈ D := by
      have h := hc' ⟨d, hdBs⟩
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, hphi] using h
    have hmm := D.mul_mem hd hmem
    rwa [mul_inv_cancel_left] at hmm
  have hmap_le : D.map (MulAut.conj g) ≤ D := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨d, hd, rfl⟩ := hz
    simpa [MulAut.conj_apply] using hconj d hd
  have hmap_eq : D.map (MulAut.conj g) = D := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hgD : g ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq
  exact ggQ2n_normalizer_inf_le hLB hP hHyp' hp hCav ⟨hInd.1, hgD⟩

end CFSG.StandardType

end
