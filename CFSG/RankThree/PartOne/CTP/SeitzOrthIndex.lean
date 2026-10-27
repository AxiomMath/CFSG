module

public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank TauCeti CFSG.ClassicalGroups.Orthogonal

theorem extSeitzAtInner_twistedD_four {q : PrimePower} (hq : q.p = 2) :
    ExtSeitzAtInner (.twistedD 4 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  obtain ⟨b, c, hbc, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj 4 q hv hq
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hF : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) =
      q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]
  have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) 2 :=
    ringChar.of_eq (by rw [ringChar_eq_of_card_eq q.prime_p q.exponent_pos hF, hq])
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (e0.trans φ) (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_quadMinus_four hbc hp hp5 E₁ hcard₁

theorem extSeitzAtOuter_twistedD_four_of_exponent_lt_five {q : PrimePower} (hq : q.p = 2)
    (he : q.exponent < 5) : ExtSeitzAtOuter (.twistedD 4 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hout
  exfalso
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hq e0
  have hpq : p ≠ q.p := by rw [hq]; omega
  obtain ⟨-, hpf, -⟩ := orthogonal_noninner_plane_local_core_product_odd_of_subfield
      orthogonal_prime_subfield_core_clause_unconditional K
    .POmegaMinus q.p q.exponent 4 p (Or.inr (Or.inr rfl)) hmodel hp (by omega) hpq ⊤ le_top E
    le_top hE hcard fun hle => hout fun φ hφ => by
      obtain ⟨g, hg⟩ := hle hφ
      exact ⟨g, hg.symm⟩
  have := Nat.le_of_dvd q.exponent_pos hpf
  omega

theorem extSeitzAtOuter_D_four_of_exponent_lt_five {q : PrimePower} (hq : q.p = 2)
    (he : q.exponent < 5) : ExtSeitzAtOuter (.D 4 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hout
  exfalso
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hq e0
  have hpq : p ≠ q.p := by rw [hq]; omega
  obtain ⟨-, hpf, -⟩ := orthogonal_noninner_plane_local_core_product_odd_of_subfield
      orthogonal_prime_subfield_core_clause_unconditional K
    .POmegaPlus q.p q.exponent 4 p (Or.inr (Or.inl rfl)) hmodel hp (by omega) hpq ⊤ le_top E
    le_top hE hcard fun hle => hout fun φ hφ => by
      obtain ⟨g, hg⟩ := hle hφ
      exact ⟨g, hg.symm⟩
  have := Nat.le_of_dvd q.exponent_pos hpf
  omega

end CFSG.RankThree.PartOne.CTP
