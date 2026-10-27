module

public import CFSG.RankThree.PartOne.CTP.StrongPAssembly
public import CFSG.RankThree.PartOne.CTP.StrongPCharP
public import CFSG.RankThree.PartOne.CTP.StrongPCharPU
public import CFSG.RankThree.PartOne.CTP.StrongPG2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.RankThree.PartOne.StrongP CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem hasNoncommPair_of_isoLie_twistedA {p : ℕ} (hp5 : 5 ≤ p) {r : ℕ}
    (hr : r = 2 ∨ r = 3) {S : Type} [Group S] {q : TauCeti.PrimePower} (hq : q.p = p)
    (h : IsoLie S (.twistedA r q)) : HasNoncommPair p S := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have hcp : CharP K q.p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := q.exponent * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have key : HasNoncommPair q.p S := by
    refine (hasNoncommPair_statedSU (n := r + 1) hK (by omega) (by omega)).map
      φ.symm.toMonoidHom φ.symm.injective
  rwa [hq] at key

theorem hasNoncommPair_of_isoLie_B2 {p : ℕ} (hp5 : 5 ≤ p) {S : Type} [Group S]
    {q : TauCeti.PrimePower} (hq : q.p = p) (h : IsoLie S (.B 2 q)) : HasNoncommPair p S := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  have hcp : CharP K q.p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hK])
  have key : HasNoncommPair q.p S :=
    (noncentralPair_sp4 (K := K) (p := q.p) (by omega)).hasNoncommPair.map φ.symm.toMonoidHom
      φ.symm.injective
  rwa [hq] at key

section Exceptional


theorem hasNoncommPair_of_isoLie_G2 {p : ℕ} (hp5 : 5 ≤ p) {S : Type} [Group S]
    {q : TauCeti.PrimePower} (hq : q.p = p) (h : IsoLie S (.G2 q)) : HasNoncommPair p S := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq2 : q.p ≠ 2 := by omega
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.untwistedModel_of_bridge
    CFSG.TauCetiBridge.untwistedBridge_G2 q hv hq2 e
  have hcp : CharP K q.p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hK])
  have key : HasNoncommPair q.p S :=
    hasNoncommPair_adjointQuotient_G2.map φ.symm.toMonoidHom φ.symm.injective
  rwa [hq] at key

theorem charPNoncommInput : CharPNoncommInput := by
  intro p _ hp5 S _ q hq h
  rcases h with h | h | h | h
  · exact hasNoncommPair_of_isoLie_twistedA hp5 (Or.inl rfl) hq h
  · exact hasNoncommPair_of_isoLie_twistedA hp5 (Or.inr rfl) hq h
  · exact hasNoncommPair_of_isoLie_B2 hp5 hq h
  · exact hasNoncommPair_of_isoLie_G2 hp5 hq h

end Exceptional

end CFSG.RankThree.PartOne.CTP
