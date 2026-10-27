module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.RankThree.PartOne.OutStructure

open CFSG.Assembly.LowTwoRank

theorem outPNice_PSL_two {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 m) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have e' : X ≃* CFSG.RankThree.PartOne.KCRootAxis.SL₂ K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (CFSG.RankThree.PartOne.KCRootAxis.slEquivPSL K).symm
  exact OutPNice.of_mulEquiv e'
    (outPNice_of_isCyclic_outer hp CFSG.RankThree.PartOne.KCRootAxis.out_sl2_isCyclic)

theorem outPNice_PSp_two {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSp 2 2 m) : OutPNice p X := by
  obtain ⟨⟨-, hm1, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm1 hK
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hm1 hFr hord
      hzp
  have : Finite (StatedProj (StatedSp 2 K)) := inferInstance
  exact OutPNice.of_mulEquiv e (outPNice_of_isCyclic_outer hp hcyc)

end CFSG.RankThree.PartOne.OutStructure
