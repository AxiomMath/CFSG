module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434Rest
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section A3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem mem_range_conj_A3_prime {q : PrimePower} (hq3 : 3 < q.p) (he : q.exponent = 1)
    (hv : (LieTypeIndex.A 3 q).Valid)
    {φ : MulAut (ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩)} (hφ3 : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩ →*
      MulAut (ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩)).range := by
  by_contra hout
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩ ≃*
      projectiveSL (3 + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (3 + 1) _)
  have hφ'p : MulAut.congr e φ ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
  have hφ'out : MulAut.congr e φ ∉ innSL (3 + 1) (GaloisField q.p q.exponent) := by
    rintro ⟨g, hg⟩
    exact hout ⟨e.symm g, (eq_conj_of_congr_eq_conj e hg.symm).symm⟩
  have hcop : Nat.Coprime 3 (Nat.gcd (3 + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
    have := Nat.dvd_trans hd (Nat.gcd_dvd_left (3 + 1) (Nat.card (GaloisField q.p q.exponent) - 1))
    omega
  have hdvd := p_dvd_card_fieldAut_of_outer (by norm_num) Nat.prime_three (by norm_num) hcop hφ'p
    hφ'out
  have hcardAut : Nat.card (GaloisField q.p q.exponent ≃+* GaloisField q.p q.exponent) =
      q.exponent := by
    obtain ⟨-, -, -, -, hcardAut, -⟩ := finite_field_automorphism_fixed_field_cardinality
      q.prime_p q.exponent_pos (GaloisField.card q.p q.exponent q.exponent_pos.ne')
    exact hcardAut
  rw [hcardAut, he] at hdvd
  omega

end A3

section B2

open CFSG.RankThree.PartOne.KCSpComm CFSG.Assembly.LowTwoRank

theorem mem_range_conj_B2_prime {q : PrimePower} (hq3 : 3 < q.p) (he : q.exponent = 1)
    (hv : (LieTypeIndex.B 2 q).Valid)
    {E : Subgroup (MulAut (ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩))}
    [CFSG.IsElementaryAbelian 3 E] {φ : MulAut (ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩)}
    (hφ : φ ∈ E) :
    φ ∈ (MulAut.conj : ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩ →*
      MulAut (ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩)).range := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF := card_fixedField_B 2 q hv
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ q.prime_p.ne_zero)
  let e := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
  have hmem : MulAut.congr e φ ∈ E.map (MulAut.congr e).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hφ
  have : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  by_contra hout
  have hnot : MulAut.congr e φ ∉ inner (StatedProj (StatedSp 2
      (ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩))) := by
    rintro ⟨g, hg⟩
    exact hout ⟨e.symm g, (eq_conj_of_congr_eq_conj e hg.symm).symm⟩
  have : NeZero 2 := ⟨by norm_num⟩
  have hdvd := (noninner_element_data (spOuter q.prime_p q.exponent_pos le_rfl hF)
    Nat.prime_three (by norm_num) hmem hnot).1
  rw [he] at hdvd
  omega

end B2

section U4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.OuterAutomorphisms (equivalence)

theorem not_three_dvd_card_outer_twistedA_three_prime {q : PrimePower} (hq3 : 3 < q.p)
    (he : q.exponent = 1) (hv : (LieTypeIndex.twistedA 3 q).Valid) :
    ¬ 3 ∣ Nat.card (Outer (ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩)) := by
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _))
  obtain ⟨-, -, -, hOut, -⟩ := unitary_full_diagonal_outer_order hU hn3 hne
  have hid : idGram F (3 + 1) = ((1 : GL (Fin (3 + 1)) F) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) := by
    simp [idGram]
  have hOut' : Nat.card (Outer (primeFormP hU (idGram F (3 + 1)))) =
      2 * q.exponent * Nat.gcd (3 + 1) (q.p ^ q.exponent + 1) := by
    rw [hid]
    exact hOut
  rw [Nat.card_congr (equivalence θ).toEquiv, hOut', he]
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 ?_
  refine Nat.Coprime.mul_right (by norm_num) ?_
  exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)

end U4

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (equivalence)


theorem card_outer_G2_prime {q : PrimePower} (hq3 : 3 < q.p) (he : q.exponent = 1)
    (hv : (LieTypeIndex.G2 q).Valid) :
    Nat.card (Outer (ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)) = 1 := by
  have hq2 : q.p ≠ 2 := by omega
  have h3 : q.p ≠ 3 := by omega
  have hmodel := CFSG.TauCetiBridge.untwistedModel_of_bridge
    CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hq2 (MulEquiv.refl _)
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel
  rw [he] at hX
  have hX' : Nat.card X = q.p ^ 1 := hX
  have : Fintype X := Fintype.ofFinite X
  have h1 : Nat.card (Outer (ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)) =
      Nat.card (Outer (adjointGroup .G2 X)) := Nat.card_congr (equivalence e).toEquiv
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
    q.prime_p hq2 (le_refl 1) X hX' .G2 (Or.inr ⟨rfl, h3⟩)
  have hcardX := card_ringAut_and_isCyclic q.prime_p X hX'
  rw [h1, card_outer_eq_of_hom Θ hsurj hker]
  exact hcardX.1

end G2

section Assembly


theorem oddPrimeFieldPlanesInner_holds : Sec19.OddPrimeFieldPlanesInner := by
  rintro ⟨d, hv⟩ q hq3 hq1 hd E hE
  rcases hd with hd | hd | hd | hd
  · change d = LieTypeIndex.A 3 q at hd
    subst hd
    intro φ hφ
    exact mem_range_conj_A3_prime hq3 hq1 hv (hE.2 φ hφ)
  · change d = LieTypeIndex.twistedA 3 q at hd
    subst hd
    exact CFSG.AGLEmbedding.le_range_conj_of_not_dvd_card_outer Nat.prime_three
      (not_three_dvd_card_outer_twistedA_three_prime hq3 hq1 hv) hE
  · change d = LieTypeIndex.B 2 q at hd
    subst hd
    have := isElementaryAbelian_of_isElemAbelian hE
    intro φ hφ
    exact mem_range_conj_B2_prime hq3 hq1 hv hφ
  · change d = LieTypeIndex.G2 q at hd
    subst hd
    refine CFSG.AGLEmbedding.le_range_conj_of_not_dvd_card_outer Nat.prime_three ?_ hE
    rw [card_outer_G2_prime hq3 hq1 hv]
    norm_num

end Assembly

end CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof
