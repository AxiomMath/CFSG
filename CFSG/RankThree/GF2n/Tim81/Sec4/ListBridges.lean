module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Inputs
public import CFSG.RankThree.PartOne.S15K.SL2Model
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.RankThree.GF2n.Tim81

open scoped MatrixGroups

theorem IsL2OrSzGroup.of_psl2_model {X : Type} [Group X] {s : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSL 2 2 s) : IsL2OrSzGroup X := by
  obtain ⟨hs2, F, hF, hFin, hChar, hcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.S15K.exists_mulEquiv_sl2_of_model h
  letI := hF
  letI : Fintype F := Fintype.ofFinite F
  letI := hChar
  refine Or.inl ⟨F, hF, Fintype.ofFinite F, hChar, ?_, ⟨e⟩⟩
  rw [← Nat.card_eq_fintype_card, hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs2

theorem IsL2OrSzGroup.of_sz_lieModel {X : Type} [Group X] {s : ℕ}
    (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 s) : IsL2OrSzGroup X := by
  obtain ⟨-, a, ha, K, hK, hKfin, hf, hcard, ⟨e⟩⟩ :=
    (CFSG.Blueprint.LieModel.twistedB2_iff.mp h).2
  letI := hK
  letI : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := s)
      (by rwa [← Nat.card_eq_fintype_card])
  refine Or.inr ⟨a, K, hK, Fintype.ofFinite K, hchar, ha, ?_, ⟨e⟩⟩
  rw [← Nat.card_eq_fintype_card, hcard, hf]

theorem nonempty_mulEquiv_alternating_eight_of_psl4_model {X : Type} [Group X]
    (h : CFSG.Open.StatedClassicalModel X .PSL 4 2 1) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) :=
  CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
    (Or.inl ⟨by decide, h⟩)

end CFSG.RankThree.GF2n.Tim81
