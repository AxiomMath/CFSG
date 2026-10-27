module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.RankThree.Classical.UnitaryRankWitness
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical

variable {p f : ℕ} {K : Type} [Field K]

theorem two_ne_zero_of_unitaryFieldData (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  have : CharP K p := h.charP
  intro h0
  have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp this)

theorem le_localRank_unitaryPSU [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {n r : ℕ}
    (hr : 1 ≤ r) (hn : 2 * r < n) : f * r ^ 2 ≤ localRank p (unitaryPSU h n) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := two_ne_zero_of_unitaryFieldData h hp2
  obtain ⟨P, hP⟩ := exists_evenFrame h h2 (n := n) (r := r) hn.le
  have hP' : hadj h P * P = frameGram r (n - 2 * r) K := hP
  have hnm : 2 * r + (n - 2 * r) = n := by omega
  obtain ⟨hU, hUcard⟩ := unitary_even_summand_unipotent h hn P hP
  exact le_localRank_of_commute_involution h.prime
    (orderOf_eq_prime (evenInvolution_sq h hP' hnm)
      (evenInvolution_ne_one h hP' hnm h2 hr (by omega))) hU hUcard
    (fun _ hx => (evenInvolution_comm h hP' hnm hx).symm)

theorem le_localRank_unitaryPSU_four [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    2 * f ≤ localRank p (unitaryPSU h 4) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := two_ne_zero_of_unitaryFieldData h hp2
  obtain ⟨P, hP⟩ := exists_fourFrame h h2
  have hP' : hadj h P * P = hypGram2 2 K := hP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hη0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hη : h.bar (c - h.bar c) = -(c - h.bar c) := by rw [map_sub, h.bar_bar, neg_sub]
  obtain ⟨hU, hUcard⟩ := unitary_four_paired_root h P hP hη0 hη
  exact le_localRank_of_commute_involution h.prime
    (orderOf_eq_prime (fourInvolution_sq h hP') (fourInvolution_ne_one h hP' h2)) hU hUcard
    (fun _ hx => (fourInvolution_comm h hP' hη hx).symm)

theorem unitaryFieldData_galoisField (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    UnitaryFieldData p f (GaloisField p (2 * f)) :=
  ⟨Fact.out, hf, GaloisField.card _ _ (by omega)⟩

theorem excluded433_twistedA_odd_of_four_le (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.p ≠ 2) (hr : 4 ≤ r) :
    Excluded433 (.lie ⟨.twistedA r q, hv⟩) := by
  intro G _ _ hG e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf := TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA r q, hv⟩
  have h := unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩) _ hf
  refine hG.false_of_four_le_localRank
    (p := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩)
    ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv)).trans
      (unitaryPSUEquiv h (n := r + 1) (by omega)).symm) Fact.out (by rw [hc]; exact hq) ?_
  have := le_localRank_unitaryPSU h (by rw [hc]; exact hq) (n := r + 1) (r := 2)
    (by norm_num) (by omega)
  nlinarith

theorem excluded433_twistedA_three_odd (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.p ≠ 2) (hf : 2 ≤ q.exponent) :
    Excluded433 (.lie ⟨.twistedA 3 q, hv⟩) := by
  intro G _ _ hG e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 3 q
  have h := unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩) _
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 3 q, hv⟩)
  refine hG.false_of_four_le_localRank
    (p := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
    ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)).trans
      (unitaryPSUEquiv h (n := 3 + 1) (by omega)).symm) Fact.out (by rw [hc]; exact hq) ?_
  have : 2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ ≤
      localRank (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
        (unitaryPSU h (3 + 1)) :=
    le_localRank_unitaryPSU_four h (by rw [hc]; exact hq)
  have hf' : 2 ≤ TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ := he ▸ hf
  omega

end CFSG.RankThree.PartTwo.Census
