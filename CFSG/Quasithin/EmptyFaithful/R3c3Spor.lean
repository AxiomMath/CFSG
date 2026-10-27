module

public import CFSG.Quasithin.EmptyFaithful.T1515eD
public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin.R3c3

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.SectionRank

theorem two_le_pRank_three_of_lemma115SporadicName
    {s : TauCeti.SporadicName}
    (hs : IsLemma115SporadicName s) {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier s) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have h3p : Nat.Prime 3 := Nat.prime_three
  have key : ∀ {G : Type} [Group G] [Finite G], (S ≃* G) →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
    fun e' h => by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e']
      exact h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : Finite NativeSporadic.M11 := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.M11) e two_le_pRank_M11_1515e
  · have : Finite NativeSporadic.M12 := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.M12) e two_le_pRank_M12_1515e
  · have : Finite NativeSporadic.M22 := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.M22) e two_le_pRank_M22_1515e
  · have : Finite NativeSporadic.M23 := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.M23) e two_le_pRank_M23_1515e
  · have : Finite NativeSporadic.M24 := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.M24) e two_le_pRank_M24_1515e
  · have : Finite NativeSporadic.J2 := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.J2) e two_le_pRank_J2_1515e
  · have : Finite NativeSporadic.J4 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J4_sylow3_cubic_witness
    exact key (G := NativeSporadic.J4) e
      (CFSG.RankThree.ThinCatalog.two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  · have : Finite NativeSporadic.HS := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, hy, hxy, hQ, -⟩ := HS_sylow3_square_witness
    exact key (G := NativeSporadic.HS) e
      (CFSG.RankThree.ThinCatalog.two_le_pRank_of_square_witness h3p hx hy hxy hQ)
  · have : Finite NativeSporadic.He := Finite.of_equiv S e.toEquiv
    exact key (G := NativeSporadic.He) e two_le_pRank_He_1515e
  · have : Finite NativeSporadic.Ru := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := Ru_sylow3_cubic_witness
    exact key (G := NativeSporadic.Ru) e
      (CFSG.RankThree.ThinCatalog.two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)

section Tits

theorem two_le_pRank_three_isTits {X : Type} [Group X] [Finite X] (h : CFSG.Quasithin.IsTits X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  (a318Exclusion_tits h).rank

end Tits

end CFSG.Quasithin.R3c3
