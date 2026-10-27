module

public import CFSG.RankThree.PartOne.CTP.SeitzL2
public import CFSG.RankThree.PartOne.CTP.SeitzThree

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.GorensteinWalter CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

section Odd

variable {F : Type} [Field F] [Finite F]

theorem isCoatom_fixed_psl2FieldAut {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hodd : ringChar F ≠ 2) {τ : F ≃+* F} (hτ : orderOf τ = p) :
    IsCoatom (signalizerFixedSubgroup (psl2FieldAut F τ)) := by
  have : Fact (ringChar F).Prime := ⟨finiteField_characteristic_prime F⟩
  have hf := one_le_finiteFieldExponent F
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield
    (finiteField_characteristic_prime F) hf (finiteField_card_eq F) τ
  rw [hτ] at hdvd hcard
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hmeq : finiteFieldExponent F / p = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hp.pos
  rw [hmeq] at hcard
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
    (hp.odd_of_ne_two hp2) hτ
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedSubfield F τ) (ringChar F) m
    hm1 hcard
  exact CFSG.Glauberman.Dickson.MaxUp.isCoatom_of_mulEquiv_psl2 (F := F) (p := ringChar F)
    (f := finiteFieldExponent F) (finiteField_card_eq F) hodd hp hp2 (by rw [hm, mul_comm])
    (e.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)))

theorem fieldAutData_psl2_odd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hodd : ringChar F ≠ 2) : FieldAutData (PSL2 F) p :=
  fieldAutData_psl2 hp hp5 fun _ hτ =>
    Or.inl (isCoatom_fixed_psl2FieldAut hp (by omega) hodd hτ)

end Odd

theorem extSeitzAtOuter_A1_odd {q : TauCeti.PrimePower}
    (h2 : q.p ≠ 2) : ExtSeitzAtOuter (.A 1 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have e : K ≃* PSL2 (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hchar : ringChar (GaloisField q.p q.exponent) ≠ 2 := by
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p]
    exact h2
  have hd : FieldAutData K p :=
    (fieldAutData_psl2_odd hp hp5 hchar).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end CFSG.RankThree.PartOne.CTP
