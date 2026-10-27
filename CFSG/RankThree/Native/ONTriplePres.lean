module

public import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.RankThree.Native.ONTriplePresInputs
public import Certificates.Certificate8144

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.CosetTable

abbrev FHat (e₁ e₂ e₃ : ℕ) : Type := PG 8 (coverRels e₁ e₂ e₃)

theorem card_coxeter_le :
    Finite (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ∧
    Nat.card (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ≤ 3753792 :=
  Certificates.certificate8144.1

theorem restrict_coverRels (e₁ e₂ e₃ : ℕ) :
    restrictWords (subsetOf 8 [0, 1, 2, 3, 4, 5]) (coverRels e₁ e₂ e₃) = C1 := rfl

theorem card_FHat_le_of_check {e₁ e₂ e₃ cap n : ℕ}
    (h : subsetCheckCC (coverRels e₁ e₂ e₃) [0, 1, 2, 3, 4, 5] cap n = true) :
    Finite (FHat e₁ e₂ e₃) ∧ Nat.card (FHat e₁ e₂ e₃) ≤ n * 3753792 := by
  have hfin := card_coxeter_le.1
  rw [← restrict_coverRels e₁ e₂ e₃] at hfin
  obtain ⟨hf, hc⟩ := card_le_of_subsetCheckCC (coverRels e₁ e₂ e₃) [0, 1, 2, 3, 4, 5] h
  refine ⟨hf, hc.trans (Nat.mul_le_mul_left _ ?_)⟩
  rw [restrict_coverRels]
  exact card_coxeter_le.2

theorem card_FHat_one_le :
    Finite (FHat 1 1 1) ∧ Nat.card (FHat 1 1 1) ≤ 1382446517760 :=
  Certificates.certificate8144.2.1

theorem card_FHat_zero_le :
    Finite (FHat 0 0 0) ∧ Nat.card (FHat 0 0 0) ≤ 1382446517760 :=
  Certificates.certificate8144.2.2.1

theorem index_FHat_one_le :
    (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
      (subsetOf 8 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
      (subsetOf 8 [0, 1, 2, 3, 4, 5])).index ≤ 368280 :=
  Certificates.certificate8144.2.2.2

end CFSG.RankThree.Native.ONTriple
