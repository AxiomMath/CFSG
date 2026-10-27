module

public import CFSG.RankThree.PartOne.N143.Item613IdxDefs
public import CFSG.RankThree.PartOne.N143.Inspect613
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree.PartOne.Census3 TauCeti
open scoped commutatorElement

theorem item613Idx_item5 : Item613IdxFor Census3.ThmThreeItem5 := by
  rintro X _ _ - ⟨n, hn5, hn12, ⟨e⟩⟩ p hp hp7 E hE hcard -
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p E
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hcard)
  have hdvdE : p ^ 2 ∣ Nat.card E := by
    rw [hk]
    exact pow_dvd_pow p hk2
  have hdvd : p ^ 2 ∣ Nat.card X := hdvdE.trans (Subgroup.card_subgroup_dvd_card E)
  have hX : Nat.card X = Nat.factorial n / 2 := by
    have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  rw [hX] at hdvd
  have h2n : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  exact not_sq_dvd_factorial_of_le_twelve hp hp7 hn12 (hdvd.trans (Nat.div_dvd_of_dvd h2n))

theorem item613Idx_item1 : Item613IdxFor Census3.ThmThreeItem1 := by
  rintro X _ _ - ⟨q, hq2, -, hv, ⟨e⟩⟩ p hp hp7 E hE - ⟨S, hS1, hS2, hEN, hSE⟩
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.eq_two_or_odd'.resolve_left hq2, q.exponent_pos, hcard⟩
  let eP : X ≃* GorensteinWalter.PSL2 (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hd : GorensteinWalter.HasDihedralSylowTwo X :=
    CFSG.ComponentClassification.OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv eP
      (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hodd)
  have hEp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hcent := no_action_of_dihedral hd hp (by omega) hEp hS2 hEN
  have hcomm : ⁅E, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  apply hS1
  rw [← hSE, Subgroup.commutator_comm]
  exact hcomm

end CFSG.RankThree.PartOne.N143
