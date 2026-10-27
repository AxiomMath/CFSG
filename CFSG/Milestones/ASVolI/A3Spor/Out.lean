module

public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.Background.A318POutHe
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem burnsideA315s_exists_conj_of_card_outer_dvd {L : Type*} [Group L] {k : ℕ}
    (h : Nat.card (Outer L) ∣ 2 ^ k) (α : MulAut L) (hodd : Odd (orderOf α)) :
    ∃ l : L, α = MulAut.conj l := by
  set a : Outer L := (α : MulAut L ⧸ inner L) with ha
  have h1 : orderOf a ∣ 2 ^ k := (orderOf_dvd_natCard a).trans h
  have h2 : orderOf a ∣ orderOf α := orderOf_dvd_of_pow_eq_one (by
    rw [ha, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd' : Odd (orderOf a) := hodd.of_dvd_nat h2
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).mp hj
  exact ⟨g, hg.symm⟩

theorem burnsideA315s_oddInner_of_not_dvd {L : Type} [Group L] [Finite L]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (Outer L)) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l := by
  have := CFSG.Quasithin.A318P.finite_outer L
  have hne : Nat.card (Outer L) ≠ 0 := Nat.card_pos.ne'
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hne (p := 2) fun {d} hd hdd => by
    by_contra hd2
    exact h d hd hd2 hdd
  exact burnsideA315s_exists_conj_of_card_outer_dvd (k := _) (dvd_of_eq hpow)

theorem burnsideA315s_oddInner_M11
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M11) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_M11 e hp hp2

theorem burnsideA315s_oddInner_M12
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .M12) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_M12 e hp hp2

theorem burnsideA315s_oddInner_M22
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M22) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_M22 e hp hp2

theorem burnsideA315s_oddInner_M23
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M23) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_M23 e hp hp2

theorem burnsideA315s_oddInner_M24
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M24) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_M24 e hp hp2

theorem burnsideA315s_oddInner_J2
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .J2) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_J2 e hp hp2

theorem burnsideA315s_oddInner_HS
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .HS) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_HS e hp hp2

theorem burnsideA315s_oddInner_He
 {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .He) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_He e hp hp2

theorem burnsideA315s_oddInner_Ru
    {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .Ru) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l :=
  burnsideA315s_oddInner_of_not_dvd fun _ hp hp2 => CFSG.Quasithin.A318P.not_dvd_outer_Ru e hp hp2

theorem burnsideA315s_oddInner_J4
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .J4) :
    ∀ α : MulAut L, Odd (orderOf α) → ∃ l : L, α = MulAut.conj l := by
  have h1 : Nat.card (Outer L) = 1 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.card_outer_J4
  exact fun α hα => burnsideA315s_exists_conj_of_card_outer_dvd (k := 0) (by rw [h1, pow_zero]) α hα

theorem burnsideA315s_allInner_J1
    {L : Type} [Group L] (e : L ≃* NativeSporadic.Carrier .J1) :
    ∀ α : MulAut L, ∃ l : L, α = MulAut.conj l := by
  intro α
  have h1 : Nat.card (Outer L) = 1 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.at_j1_schreier.1
  have : Subsingleton (Outer L) := (Nat.card_eq_one_iff_unique.1 h1).1
  have ha : ((α : MulAut L ⧸ inner L) : Outer L) = 1 := Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).mp ha
  exact ⟨g, hg.symm⟩

end CFSG.ASVolI
