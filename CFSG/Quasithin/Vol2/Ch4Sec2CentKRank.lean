module

public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

private theorem pRank_quotient_two_top {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y)
    [N.Normal] (hN : IsPGroup 2 N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ N)) = CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ Nat.card N := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hN
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  exact CFSG.SectionRank.pRank_quotient_eq N hnd

theorem false_of_elemAbelian_quotient (hK : quasithinIsQTKECat G) {H : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : CFSG.Open.pRank p H ≤ 2 :=
    CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hK hH hp hp2
  have hH' : CFSG.Open.pRank p (⊤ : Subgroup ↥H) = CFSG.Open.pRank p H :=
    CFSG.Quasithin.pRank_top_subtype H
  have hq := pRank_quotient_two_top (CFSG.pCore 2 ↥H) CFSG.pCore_isPGroup hp hp2
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hE hcard
  omega

end CFSG.Quasithin.H13.Ch4.CentK
