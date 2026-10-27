module

public import CFSG.RankThree.PartOne.K159.BorelOrth
public import CFSG.RankThree.PartOne.K159.BorelSp
public import CFSG.RankThree.PartOne.S15K.LayerTypes

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.RankThree.PartOne.S15K CFSG.RankThree.Classical2

theorem _root_.CFSG.RankThree.PartOne.S15K.BlockModel.borelFactsGrp {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {J : Type} [Group J]
    (h : BlockModel p J) : BorelFactsGrp p J := by
  obtain ⟨g, E, _, _, _, hE, hg, hpg, hm⟩ := h
  have hpE : p ∣ Nat.card E - 1 := by
    rw [hE]
    exact hpg
  rcases hm with ⟨m, hm, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨W, _, _, _, R, hR, hd, hts, ⟨e⟩⟩
  · have : Finite J := Finite.of_equiv _ e.symm.toEquiv
    have hSL := borelFactsGrp_specialLinear (K := E) (m := m) hp hpE (by omega) (by omega)
    exact BorelFactsGrp.of_mulEquiv e.symm hSL
  · have : Finite J := Finite.of_equiv _ e.symm.toEquiv
    exact BorelFactsGrp.of_mulEquiv e.symm (borelFactsGrp_statedSp_two hp hpE hp3)
  · have : Finite W := Module.finite_of_finite E
    have : Finite (W ≃ₗ[E] W) :=
      Finite.of_injective (fun g : W ≃ₗ[E] W => (g : W → W)) DFunLike.coe_injective
    have : Finite J := Finite.of_equiv _ e.symm.toEquiv
    rcases hd with hd4 | hd6
    · have hts4 : ∀ U : Submodule E W, Module.finrank E U = 2 → ∃ u ∈ U, R u ≠ 0 := fun U hU =>
        hts U (by rw [hU, hd4])
      exact BorelFactsGrp.of_mulEquiv e.symm
        (borelFactsGrp_orthDerived_four R hR hd4 hts4 hp hpE hp3)
    · have hts6 : ∀ U : Submodule E W, Module.finrank E U = 3 → ∃ u ∈ U, R u ≠ 0 := fun U hU =>
        hts U (by rw [hU, hd6])
      exact BorelFactsGrp.of_mulEquiv e.symm
        (borelFactsGrp_orthDerived_six R hR hd6 hts6 hp hpE hp3)

theorem kf158BlocksBorel_two_three (hS13 : Sec13Avail) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hout : Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E))
    {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {Y : Subgroup G} (hYb : Y ∈ thetaComponentsAt p b)
    (hYI : Y ≤ lieGenerated p E) : BorelFacts p Y := by
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    rcases hout with ⟨-, -, -, -, -, hEA, -⟩ | ⟨-, -, -, -, -, hEA, -⟩ <;>
      rintro ⟨-, -, -, -, -, -, hne, -⟩ <;> exact hne hEA
  have h13 := hS13 G p A c L E h15.h12 hnot5
  have hL := layerModelData_two_three h15 h13 hout
  exact (hL.blockModel_of_mem_thetaComponentsAt h15.h12.prime hb hb1 hYb hYI).borelFactsGrp
    h15.h12.prime (by have := h15.h12.three_lt; omega)

end CFSG.RankThree.PartOne.K159
