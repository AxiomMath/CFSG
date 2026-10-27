module

public import CFSG.RankThree.PartOne.N143.SectionListBound
public import CFSG.RankThree.PartOne.K159F.ExtFive
public import CFSG.RankThree.PartOne.CTP.StrongPSeitzThree
public import CFSG.RankThree.PartOne.K159F.AltLeaf
public import CFSG.RankThree.PartOne.K159F.L2Leaf
public import CFSG.RankThree.PartOne.K159F.NoRank
public import CFSG.RankThree.PartOne.K159F.SporadicLeaf

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.K159F
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def ExtFiveList : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeListHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
        Nat.card (omegaOne p P) = p ^ 3 →
        (Nat.card ↥(torusImage (omegaOne p P) S) ∣ 120 ∧
          ∀ g ∈ torusImage (omegaOne p P) S, orderOf g ≤ 6) →
        ∀ F : Subgroup H, F ≤ omegaOne p P → Nat.card ↥F = p ^ 2 →
          Subgroup.closure {s : H | s ∈ S ∧ ∃ F' : Subgroup H, F' ≤ F ∧ F' ≠ ⊥ ∧
            ∀ f ∈ F', f * s = s * f} = S

theorem extFiveList_of_inputs_seitzThree (hSeitz : ExtSeitzThree)
    (hCharP : CharPNoncommInput) (hSpor : SporadicFiveInput) :
    ExtFiveList := by
  intro p hp hp5 H _ _ S hSn hhyp hSc P hP hab hcard hauto F hFle hFcard
  have : Fact p.Prime := ⟨hp⟩
  have := hSn
  have := hhyp.isSimpleGroup
  have hlist : TheoremThreeList ↥S := hhyp.onList
  have hFab : IsElementaryAbelian p ↥F := isElemAb_of_le hab hFle
  have hρ := conjNormal_injective_of_centralizer S hSc
  have hnoRank : NoRankThree p ↥S → False := fun h => by
    have := hab
    exact h ⟨(omegaOne p P).map (MulAut.conjNormal (H := S)), CFSG.IsElementaryAbelian.map _,
      by rw [Subgroup.card_map_of_injective hρ, hcard]⟩
  have seitz : ∀ {d : TauCeti.LieTypeIndex}, Thm3LieIndex d → IsoLie ↥S d →
      d.characteristic ≠ p →
      Subgroup.closure {s : H | s ∈ S ∧ ∃ F' : Subgroup H, F' ≤ F ∧ F' ≠ ⊥ ∧
        ∀ f ∈ F', f * s = s * f} = S := by
    intro d hd hiso hne
    rcases generation_of_seitzAt (hSeitz d hd) hp5 S hhyp.nonabelian hiso (fun h => hne h.symm)
      hSc hFab hFcard with hgen | ⟨-, hexc⟩
    · exact hgen
    · exfalso
      rcases hexc with h | h
      · subst h
        exact hnoRank (noRankThree_of_isoLie_tits hiso hp hp5)
      · subst h
        exact hnoRank (noRankThree_of_isoLie_suzuki hhyp.nonabelian hiso hp hp5)
  have seitz2 : ∀ {d : TauCeti.LieTypeIndex}, Thm3LieIndex d → IsoLie ↥S d →
      d.characteristic = 2 →
      Subgroup.closure {s : H | s ∈ S ∧ ∃ F' : Subgroup H, F' ≤ F ∧ F' ≠ ⊥ ∧
        ∀ f ∈ F', f * s = s * f} = S := fun hd hiso hc =>
    seitz hd hiso (by rw [hc]; omega)
  have noncomm : HasNoncommPair p ↥S →
      Subgroup.closure {s : H | s ∈ S ∧ ∃ F' : Subgroup H, F' ≤ F ∧ F' ≠ ⊥ ∧
        ∀ f ∈ F', f * s = s * f} = S := fun h =>
    (false_of_hasNoncommPair S hP hab h).elim
  have hL := hlist
  rcases hlist with ⟨q, hq2, h5, hiso⟩ | ⟨q, hq2, hexp, hiso | hiso⟩ | hiso |
    ⟨q, hq2, hq1, hiso | hiso | hiso | hiso⟩ | ⟨n, hn5, hn12, ⟨e⟩⟩ | h6 |
    (⟨q, hq2, hiso⟩ | ⟨m, hiso⟩ | ⟨q, hq2, hiso | hiso | hiso | hiso | hiso | hiso | hiso⟩ |
      ⟨m, hiso⟩ | hiso) | ⟨q, hq2, hiso | hiso | hiso⟩ |
    ⟨q, hq2, hq1, hiso | hiso | hiso | hiso | hiso | hiso | hiso⟩
  ·
    by_cases hqp : q.p = p
    · exact (false_of_isoLie_A1_charP hp hp5 S hSc hP hcard hauto.2 hqp hiso).elim
    · exact seitz (thm3_A1_odd hq2 h5) hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hasNoncommPair_of_isoLie_A hp5 (le_refl 2) hqp hiso)
    · exact seitz (thm3_A2 hq2 hexp) hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inl hiso))
    · exact seitz (thm3_twistedA2 hq2 hexp) hiso (by simpa using hqp)
  ·
    exact seitz (thm3_reeG2) hiso (by simp; omega)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inr (Or.inr (Or.inr hiso))))
    · exact seitz (thm3_G2_odd hq2 hq1) hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inr (Or.inr (Or.inl hiso))))
    · exact seitz (thm3_B2_odd hq2 hq1) hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inr (Or.inl hiso)))
    · exact seitz (thm3_twistedA3_odd hq2 hq1) hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hasNoncommPair_of_isoLie_A hp5 (by norm_num) hqp hiso)
    · exact seitz (thm3_A3_odd hq2 hq1) hiso (by simpa using hqp)
  ·
    exact (false_of_alt_five hp5 hn5 hn12 S e hSc hP hcard).elim
  ·
    exact (hSpor p hp hp5 H S hSn hhyp.isSimpleGroup hhyp.nonabelian h6 hSc P hP hab hcard).elim
  ·
    exact seitz2 (thm3_A1_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_suzuki m) hiso (by simp)
  · exact seitz2 (thm3_twistedA2_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_A2_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_B2_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_G2_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_twistedA3_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_twistedA4_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_trialityD4_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_reeF4 m) hiso (by simp)
  · exact seitz2 (thm3_tits) hiso (by simp)
  ·
    exact seitz2 (thm3_A3_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_B3_even hq2) hiso (by simpa using hq2)
  · exact seitz2 (thm3_twistedD4_even hq2) hiso (by simpa using hq2)
  ·
    exact seitz2 (thm3_A4_two hq2 hq1) hiso (by simpa using hq2)
  · exact seitz2 (thm3_A5_two hq2 hq1) hiso (by simpa using hq2)
  · exact seitz2 (thm3_A6_two hq2 hq1) hiso (by simpa using hq2)
  · exact seitz2 (thm3_twistedA5_two hq2 hq1) hiso (by simpa using hq2)
  · exact seitz2 (thm3_B4_two hq2 hq1) hiso (by simpa using hq2)
  · exact seitz2 (thm3_D4_two hq2 hq1) hiso (by simpa using hq2)
  · exact seitz2 (thm3_F4_two hq2 hq1) hiso (by simpa using hq2)

end CFSG.RankThree.PartOne.N143
