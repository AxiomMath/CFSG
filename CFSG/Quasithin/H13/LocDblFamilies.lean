module

public import CFSG.Quasithin.H13.LocDblReduce
public import CFSG.Quasithin.H13.LocDblOrder
public import CFSG.Quasithin.H13.LocDblMatrix
public import CFSG.Quasithin.H13.LocDblLie
public import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SporadicSylowNoDouble : Prop :=
  SylowNoDouble (NativeSporadic.Carrier .J2) ∧ SylowNoDouble (NativeSporadic.Carrier .HS) ∧
    SylowNoDouble (NativeSporadic.Carrier .He) ∧ SylowNoDouble (NativeSporadic.Carrier .Ru)

theorem sylowNoDouble_of_equiv {S T : Type} [Group S] [Group T] [Finite S] (e : S ≃* T)
    (h : SylowNoDouble T) : SylowNoDouble S := by
  have : Finite T := Finite.of_equiv S e.toEquiv
  exact SylowNoDouble.of_mulEquiv e.symm h

theorem sylowNoDouble_of_PSL {S : Type} [Group S] [Finite S] {n p f : ℕ} (hn : n = 2 ∨ n = 3)
    (h : StatedClassicalModel S .PSL n p f) : SylowNoDouble S := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  exact sylowNoDouble_of_equiv e (sylowNoDouble_statedProj hn (StatedSL n K))

theorem sylowNoDouble_of_PSU {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSU 3 p f) : SylowNoDouble S := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  exact sylowNoDouble_of_equiv e (sylowNoDouble_statedProj (Or.inr rfl) (StatedSU 3 (p ^ f) K))

theorem sylowNoDouble_of_PSL_two {S : Type} [Group S] [Finite S] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : StatedClassicalModel S .PSL n 2 1) : SylowNoDouble S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := n)
    (by omega)
  rw [hK, ← Nat.card_congr e.toEquiv] at hcard
  rcases hn with rfl | rfl
  · exact sylowNoDouble_of_card (n := 20160) (by rw [hcard]; decide)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 9999360) (by rw [hcard]; decide)
      (by simp [Nat.primeFactors]; decide)

theorem sylowNoDouble_of_alt {S : Type} [Group S] [Finite S] {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8)
    (e : S ≃* alternatingGroup (Fin n)) : SylowNoDouble S := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  · exact sylowNoDouble_of_card (n := 60) (by rw [hcard]; decide)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 360) (by rw [hcard]; decide)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 2520) (by rw [hcard]; decide)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 20160) (by rw [hcard]; decide)
      (by simp [Nat.primeFactors]; decide)

theorem sylowNoDouble_of_sporadic
    (hsp : SporadicSylowNoDouble) {S : Type} [Group S] [Finite S]
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru)
    (e : S ≃* NativeSporadic.Carrier s) : SylowNoDouble S := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sylowNoDouble_of_card (n := 7920)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 95040)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 443520)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 10200960)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m23_card)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 244823040)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M24)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_card (n := 175560)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1)
      (by simp [Nat.primeFactors]; decide)
  · exact sylowNoDouble_of_equiv e hsp.1
  · exact fun _ _ Y _ _ => noIsoDouble_of_card_dvd_J4
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4).dvd Y
  · exact sylowNoDouble_of_equiv e hsp.2.1
  · exact sylowNoDouble_of_equiv e hsp.2.2.1
  · exact sylowNoDouble_of_equiv e hsp.2.2.2

theorem simpleListNoDouble_of_sporadic
    (hsp : SporadicSylowNoDouble) : SimpleListNoDouble := by
  intro S _ _ hsimple _ h
  rcases h with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨f, hf, hm⟩ | hm | hm⟩ |
      (⟨f, ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨ho, h3, hm⟩ |
        ⟨ho, h3, hm⟩⟩ | hT) | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact sylowNoDouble_of_alt h5 h8 e
  · exact sylowNoDouble_of_PSL (Or.inl rfl) hm
  · exact sylowNoDouble_of_PSL (Or.inr rfl) hm
  · exact sylowNoDouble_of_PSU hm
  · exact sylowNoDouble_of_PSL (Or.inl rfl) hm
  · exact sylowNoDouble_of_PSL (Or.inr rfl) hm
  · exact sylowNoDouble_of_PSU hm
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    exact sylowNoDouble_of_equiv e (sylowNoDouble_projSp4 hcard h2)
  · obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hm
    exact sylowNoDouble_of_equiv e (sylowNoDouble_G2 hK h2)
  · obtain ⟨-, K, _, _, σ, hK, -, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hm
    exact sylowNoDouble_of_equiv e (sylowNoDouble_D4 h1 σ hK)
  · obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hm
    subst hfa
    exact sylowNoDouble_of_equiv e (sylowNoDouble_F4 ha hK)
  · exact sylowNoDouble_suzuki hm
  · exact sylowNoDouble_tits hT
  · exact sylowNoDouble_of_PSL_two hn hm
  · exact sylowNoDouble_of_sporadic hsp hs e

theorem local_double_embedding_exclusion_of_sporadic
    (hsp : SporadicSylowNoDouble) :
    LocalDoubleEmbeddingExclusion :=
  local_double_embedding_exclusion_of (simpleListNoDouble_of_sporadic hsp)

end CFSG.Quasithin.H13.LocDbl
