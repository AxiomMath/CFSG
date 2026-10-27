module

public import CFSG.RankThree.PartOne.N143.SectionListBound
public import CFSG.RankThree.PartOne.CTP.StrongPSeitzThree
public import CFSG.RankThree.PartOne.CTP.AltLeaf

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne ExtSPE)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def ExtSPEList : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeListHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ Y : Subgroup H, IsStronglyPEmbedded p Y →
        ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
          (Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) →
          (∃ q : TauCeti.PrimePower, q.p = p ∧ (q.exponent = 2 ∨ q.exponent = 3) ∧
            Census3.IsoLie ↥S (.A 1 q)) ∨
          (p = 5 ∧ (Nonempty (↥S ≃* alternatingGroup (Fin 10)) ∨ Census3.IsoLie ↥S .tits ∨
            Census3.IsoLie ↥S (.suzuki 2)))

section Route

variable {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H]

theorem spe_conclusion_of_seitzThree_list (hSeitz : ExtSeitzThree)
    (hSchr : SchreierFor CFSG.Assembly.InCatalog) (hp5 : 5 ≤ p) (S : Subgroup H) [S.Normal]
    (hhyp : TheoremThreeListHyp ↥S) (hSc : Subgroup.centralizer (S : Set H) = ⊥)
    {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) {E : Subgroup H} (hEY : E ≤ Y)
    [CFSG.IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) {d : TauCeti.LieTypeIndex}
    (hd : Thm3LieIndex d) (hiso : IsoLie ↥S d) (hne : d.characteristic ≠ p) :
    SPEConclusion p ↥S := by
  have := hhyp.isSimpleGroup
  have : Group.IsSolvable (Outer ↥S) := hSchr ↥S hhyp.nonabelian hhyp.exists_index
  obtain ⟨hp5', hexc⟩ := seitzAt_stronglyPEmbedded (hSeitz d hd) hp5 S hhyp.nonabelian hiso
    (fun h => hne h.symm) hSc hY hEY hE
  refine Or.inr ⟨hp5', ?_⟩
  rcases hexc with h | h
  · exact Or.inr (Or.inl (h ▸ hiso))
  · exact Or.inr (Or.inr (h ▸ hiso))

end Route

theorem extSPEList_of_inputs_seitzThree (hSeitz : ExtSeitzThree)
    (hSchr : SchreierFor CFSG.Assembly.InCatalog) (hCharP : CharPNoncommInput)
    (hSpor : SporadicStrongPInput) : ExtSPEList := by
  intro p hp hp5 H _ _ S hSn hhyp hSc Y hY P hP hab hcard
  have : Fact p.Prime := ⟨hp⟩
  have := hSn
  have hlist : TheoremThreeList ↥S := hhyp.onList
  show SPEConclusion p ↥S
  obtain ⟨Y', E, hY', hEY, hEab, hEc⟩ := exists_pair_le hY hP hab hcard
  have := hEab
  have seitz : ∀ {d : TauCeti.LieTypeIndex}, Thm3LieIndex d → IsoLie ↥S d →
      d.characteristic ≠ p → SPEConclusion p ↥S := fun hd hiso hne =>
    spe_conclusion_of_seitzThree_list hSeitz hSchr hp5 S hhyp hSc hY' hEY hEc hd hiso hne
  have seitz2 : ∀ {d : TauCeti.LieTypeIndex}, Thm3LieIndex d → IsoLie ↥S d →
      d.characteristic = 2 → SPEConclusion p ↥S := fun hd hiso hc =>
    seitz hd hiso (by rw [hc]; omega)
  have noncomm : HasNoncommPair p ↥S → SPEConclusion p ↥S := fun h =>
    (false_of_hasNoncommPair S hP hab h).elim
  have hL := hlist
  rcases hlist with ⟨q, hq2, h5, hiso⟩ | ⟨q, hq2, hexp, hiso | hiso⟩ | hiso |
    ⟨q, hq2, hq1, hiso | hiso | hiso | hiso⟩ | ⟨n, hn5, hn12, ⟨e⟩⟩ | h6 |
    (⟨q, hq2, hiso⟩ | ⟨m, hiso⟩ | ⟨q, hq2, hiso | hiso | hiso | hiso | hiso | hiso | hiso⟩ |
      ⟨m, hiso⟩ | hiso) | ⟨q, hq2, hiso | hiso | hiso⟩ |
    ⟨q, hq2, hq1, hiso | hiso | hiso | hiso | hiso | hiso | hiso⟩
  ·
    by_cases hqp : q.p = p
    · exact spe_conclusion_A1 hp5 S hSc hP hcard hqp hiso
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
    obtain ⟨hp5', hn10⟩ := alt_stronglyPEmbedded hp5 hn5 hn12 S e hSc hY' hEY hEc
    subst hn10
    exact Or.inr ⟨hp5', Or.inl ⟨e⟩⟩
  ·
    exact (hSpor p hp hp5 H S hSn hhyp.isSimpleGroup hhyp.nonabelian h6 hSc Y hY P hP hab
      hcard).elim
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
