module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Core
import CFSG.Adapters.WholeGroupLayer
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6

section General

variable {G : Type} [Group G] [Finite G]

theorem pCore_le_relPPrimeCore_of_ne {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) :
    CFSG.pCore r G ≤ relPPrimeCore s (⊤ : Subgroup G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine le_sSup (s := {N : Subgroup G | N ≤ ⊤ ∧ (N.subgroupOf ⊤).Normal ∧
      Nat.Coprime s (Nat.card N)}) ⟨le_top, Subgroup.normal_subgroupOf, ?_⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := r) (G := G)).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hs hr).2 (Ne.symm hrs))

theorem fittingSubgroup_le_pCoreOf_sup_relPPrimeCore {s : ℕ} (hs : s.Prime) :
    CFSG.fittingSubgroup G ≤ pCoreOf s (⊤ : Subgroup G) ⊔ relPPrimeCore s (⊤ : Subgroup G) := by
  rw [CFSG.fitting_eq_sup_pCore G]
  refine iSup_le fun r => ?_
  have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
  by_cases hrs : r.1.1 = s
  · intro y hy
    have hy' : y ∈ CFSG.pCore s G := hrs ▸ hy
    exact Subgroup.mem_sup_left (mem_pCoreOf_top_of_mem_pCore hy')
  · exact le_sup_of_le_right (pCore_le_relPPrimeCore_of_ne hr hs hrs)

theorem commutator_pCoreOf_eq_bot_of_component_le {M L : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hL : CFSG.IsComponent L) (hLM : L ≤ M) : ⁅L, pCoreOf r M⁆ = ⊥ := by
  have hc : CFSG.IsComponent (L.subgroupOf M) := CFSG.LocalCores.component_overgroup hL hLM
  have hle : L.subgroupOf M ≤ CFSG.layer M := CFSG.LocalCores.component_le_layer hc
  have hcen := CFSG.WholeGroup.pCore_le_centralizer_layer (G := M) r
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 (hcen hq) ⟨x, hLM hx⟩ (hle hx)
  exact congrArg Subtype.val h1.symm

end General

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem comm_pCoreOf_two_eq_bot_of_component_le {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hLM : L ≤ M) : ⁅L, pCoreOf 2 M⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact commutator_pCoreOf_eq_bot_of_component_le hL hLM

theorem false_of_component_le {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (hLM : L ≤ M) : False :=
  hne (h.comm_pCoreOf_two_eq_bot_of_component_le hL hLM)

theorem exists_component : ∃ L : Subgroup G, CFSG.IsComponent L ∧ ⁅L, pCoreOf 2 M⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  set Q := pCoreOf 2 M with hQ
  have hFQ : CFSG.fittingSubgroup G ≤ centralizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact h.comm_fittingSubgroup hq hx
  have hEQ : CFSG.layer G ≤ centralizer (Q : Set G) := by
    refine sSup_le fun K hK => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hall K hK)
  have hstar : CFSG.generalizedFitting G ≤ centralizer (Q : Set G) := sup_le hFQ hEQ
  have hQstar : Q ≤ centralizer ((CFSG.generalizedFitting G : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 hstar
  have hQF : Q ≤ CFSG.fittingSubgroup G :=
    hQstar.trans (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup G)
  have h2 : Q ≤ relPPrimeCore 2 (⊤ : Subgroup G) := by
    have := hQF.trans (fittingSubgroup_le_pCoreOf_sup_relPPrimeCore (G := G) Nat.prime_two)
    rwa [h.pCoreOf_top_eq_bot, bot_sup_eq] at this
  have hodd : ¬ 2 ∣ Nat.card (relPPrimeCore 2 (⊤ : Subgroup G)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
        Nat.prime_two (⊤ : Subgroup G))
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ, pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  obtain ⟨a, ha⟩ := hQ2.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h.pCore_ne_bot (Subgroup.eq_bot_of_card_eq Q (by simpa using ha))
  exact hodd ((dvd_pow_self 2 ha0).trans (ha ▸ Subgroup.card_dvd_of_le h2))

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
