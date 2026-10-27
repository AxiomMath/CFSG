module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc.Assembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc (AmbLeaves)

theorem ambLeaves_of_central_quotient {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K)) (h : AmbLeaves (K ⧸ Subgroup.center K)) :
    AmbLeaves K := by
  refine ⟨fun E hE hc => iSup_centralizer_eq_top_of_central_quotient hK h3 h.1 hE hc, ?_⟩
  intro Z X hpos Q hdvd
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hpos' := pos_map_central_quotient h3 hpos
  have hinjX : ∀ x ∈ X, π x = 1 → x = 1 :=
    eq_one_of_mk_eq_one_of_card_center h3 hpos.2.2.2.2.2.1
  obtain ⟨eX, -⟩ := exists_mulEquiv_map π hinjX
  obtain ⟨Q'⟩ : Nonempty (Sylow 3 (X.map π)) := inferInstance
  have hXcard : Nat.card (X.map π) = Nat.card X := (Nat.card_congr eX.toEquiv).symm
  have hQ : Nat.card Q = 3 ^ (Nat.card X).factorization 3 := Sylow.card_eq_multiplicity Q
  have hQ' : Nat.card Q' = Nat.card Q := by
    rw [Sylow.card_eq_multiplicity Q', hXcard, hQ]
  refine h.2 _ _ hpos' Q' ?_
  have hcop : Nat.Coprime (9 * Nat.card Q) (Nat.card (Subgroup.center K)) := by
    have h3c : Nat.Coprime 3 (Nat.card (Subgroup.center K)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [hQ]
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9, ← pow_add]
    exact Nat.Coprime.pow_left _ h3c
  have hcard : Nat.card K = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [hcard] at hdvd
  rw [hQ']
  exact hcop.dvd_of_dvd_mul_right hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
