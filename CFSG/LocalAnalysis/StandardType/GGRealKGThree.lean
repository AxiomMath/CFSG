module

public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGRealQFourThree
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

theorem ggReflRealizedIn_three_of_rootSL2On {S : ℕ → LargeEvenLabel → Prop}
    (hKG : GGRealRootSL2On fun p lab => p = 3 ∧ S p lab) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hNT : GGNoTransvection p Bs) (hp3 : p = 3) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hq : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ S p lab) p Bs X) :
    GGReflRealizedIn p Bs X := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hM : GGInnerDiagOnLabel (fun p lab => GGRealRootLabel p lab ∧ S p lab) p Bs X := by
    subst hp3
    exact largeEvenMarking_mono (fun lab _ _ _ _ _ ⟨⟨h2, hs⟩, hN, hI⟩ =>
      ⟨⟨⟨hp2, h2, ggRealRootLabel_three_dvd _⟩, hs⟩, hN, hI⟩) hq
  obtain ⟨hXc, lab, hlab, hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGRealRootLabel p lab ∧ S p lab)
    (fun lab hlab hs => hKG p lab hp hlab hs.1 ⟨hp3, hs.2⟩) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  rcases hX with rfl | ⟨y, hnb⟩
  · obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
    exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI hr h3 hT
  · exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI
      (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hXc θ hBsN hlift)
      (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

@[expose] def GGRealKGThreeRow (i : GGKGRow) : Prop :=
  GGRealRootSL2On fun p lab => p = 3 ∧ GGKGRowLabel i p lab ∧ ¬ GGTypeALabel p lab

theorem ggKGRow_cover_three (lab : LargeEvenLabel) : ∃ i : GGKGRow, GGKGRowLabel i 3 lab := by
  obtain ⟨t, l, n⟩ := lab
  have h : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hm := Nat.mod_lt (2 ^ n) (show 0 < 3 by norm_num)
    have h0 : 2 ^ n % 3 ≠ 0 := fun h0 =>
      absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)))
        (by norm_num)
    omega
  rcases h with h | h <;> by_cases hd : 3 ∣ l + 1 <;> cases t <;>
    first
      | exact ⟨.aSplit, rfl, h, hd⟩ | exact ⟨.aSplitDvd, rfl, h, hd⟩
      | exact ⟨.aNonsplit, rfl, h, hd⟩ | exact ⟨.aNonsplitDvd, rfl, h, hd⟩
      | exact ⟨.uSplit, rfl, h, hd⟩ | exact ⟨.uSplitDvd, rfl, h, hd⟩
      | exact ⟨.uNonsplit, rfl, h, hd⟩ | exact ⟨.uNonsplitDvd, rfl, h, hd⟩
      | exact ⟨.spSplit, Or.inl rfl, h⟩ | exact ⟨.spSplit, Or.inr rfl, h⟩
      | exact ⟨.spNonsplit, Or.inl rfl, h⟩ | exact ⟨.spNonsplit, Or.inr rfl, h⟩
      | exact ⟨.dSplit, rfl, h⟩ | exact ⟨.dNonsplit, rfl, h⟩
      | exact ⟨.twdSplit, rfl, h⟩ | exact ⟨.twdNonsplit, rfl, h⟩
      | exact ⟨.e6Split, rfl, h⟩ | exact ⟨.e6Nonsplit, rfl, h⟩
      | exact ⟨.e7Split, rfl, h⟩ | exact ⟨.e7Nonsplit, rfl, h⟩
      | exact ⟨.e8Split, rfl, h⟩ | exact ⟨.e8Nonsplit, rfl, h⟩
      | exact ⟨.f4Split, rfl, h⟩ | exact ⟨.f4Nonsplit, rfl, h⟩
      | exact ⟨.twe6Split, rfl, h⟩ | exact ⟨.twe6Nonsplit, rfl, h⟩
      | exact ⟨.small, Or.inl rfl⟩ | exact ⟨.small, Or.inr (Or.inl rfl)⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inl rfl))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩

theorem ggRealKGThreeRow_aSplit : GGRealKGThreeRow .aSplit :=
  fun _ _ _ _ _ ⟨_, hi, hs⟩ => (hs (Or.inl hi)).elim

end CFSG.StandardType

end
