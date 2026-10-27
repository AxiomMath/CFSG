module

public import CFSG.RankThree.PartOne.S11c.EvenRootInverters
public import CFSG.RankThree.PartOne.S11c.TorusWords
public import CFSG.RankThree.PartOne.S11c.InverterData
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.RankThree.Chevalley.OddExceptionalRealRootElement

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.OddToralOrdinary CFSG.RankThree.Chevalley

@[expose] def e8Support : Fin 4 → Finset (Fin Tag.E8.rank) :=
  (![({1, 2} : Finset (Fin 8)), {1}, {1, 4}, {1, 4, 6}] : Fin 4 → Finset (Fin 8))

@[expose] def e8CentralSupport : Finset (Fin Tag.E8.rank) := ({0} : Finset (Fin 8))

theorem e8_parity_checks :
    (∀ i i', (∑ j ∈ e8Support i, ∑ k, Tag.E8.cartan j k * evenE8Roots i' k) % 2 =
      if i = i' then 1 else 0) ∧
    (∀ i, (∑ j ∈ e8CentralSupport, ∑ k, Tag.E8.cartan j k * evenE8Roots i k) % 2 = 0) ∧
    (∑ j ∈ e8CentralSupport, ∑ k, Tag.E8.cartan j k *
      (Pi.single (⟨2, by decide⟩ : Fin Tag.E8.rank) 1 : Fin Tag.E8.rank → ℤ) k) % 2 = 1 := by
  unfold e8Support e8CentralSupport
  decide +kernel

theorem isInverterData_E8_charThree (K : Type) [Field K] [CharP K 3] :
    IsInverterData (adjointGroup .E8 K) 3 (fun i => pinnedX .E8 K (evenE8Roots i) 1)
      (fun i => torusWord .E8 K (e8Support i)) (torusWord .E8 K e8CentralSupport) := by
  have hτ : (Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8) :=
    Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨hroot, -, -, -⟩ := evenE8_check
  have hα : ∀ i, IsRoot .E8 (evenE8Roots i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  obtain ⟨hcα, -⟩ := commute_pinnedX_of_check (K := K) hτ evenE8_check
  obtain ⟨hpar, hparz, hparγ⟩ := e8_parity_checks
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP (p := 3) (by norm_num)
  refine ⟨fun i => ⟨pinnedX_mem_adjointGroup _ _, orderOf_pinnedX_one .E8 K 3 _⟩, fun i j => ?_,
    fun i => torusWord_mem_adjointGroup _, fun i => ?_, fun i j hij => ?_,
    torusWord_mem_adjointGroup _, ?_,
    fun i => torusWord_commute_pinnedX_of_even _ (hα i) 1 (hparz i)⟩
  · by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact (hcα i j hij 1 1).1
  · exact torusWord_conj_pinnedX_of_odd _ (hα i) 1 (by rw [hpar i i]; simp)
  · rw [torusWord_conj_pinnedX _ (hα j) 1, hpar i j]
    simp [hij]
  · refine orderOf_eq_prime (torusWord_sq _) ?_
    exact torusWord_ne_one_of_odd _ (isRoot_single _ _) hparγ h2

end CFSG.RankThree.PartOne
