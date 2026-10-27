module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
public import CFSG.Sporadic.SuzRecog.C1ModelCent

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.PSL3Four

section Certificates


theorem TabRep.permC_eq {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) :
    permC n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    constructor
    · intro i hi
      rw [ht.2 ⟨i, hi⟩]
      exact (g ⟨i, hi⟩).isLt
    · intro i hi j hj hij
      have h1 : t[i]! = (g ⟨i, hi⟩ : ℕ) := ht.2 ⟨i, hi⟩
      have h2 : t[j]! = (g ⟨j, hj⟩ : ℕ) := ht.2 ⟨j, hj⟩
      have hg : g ⟨i, hi⟩ = g ⟨j, hj⟩ := Fin.ext (by rw [← h1, ← h2]; exact hij)
      exact congrArg Fin.val (g.injective hg)
  rw [permC]
  rw [@dite_eq_left_of_eq_true _ _ (Classical.propDecidable _) _ _ (eq_true hc)]
  apply Equiv.ext
  intro i
  rw [Equiv.ofBijective_apply]
  exact Fin.ext (ht.2 i)

theorem tabSubgroup_eq_of_enumerates {T : Array Tab}
    {H : Subgroup (Equiv.Perm (Fin 1782))} (h : Enumerates H T.toList) :
    tabSubgroup T = H := by
  refine le_antisymm ?_ ?_
  · rw [tabSubgroup, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change permC 1782 T[i.val]! ∈ H
    obtain ⟨g, hg, hrep⟩ := h.sound _ (getElem!_mem i.isLt)
    rwa [TabRep.permC_eq hrep]
  · intro g hg
    obtain ⟨t, ht, hrep⟩ := h.complete g hg
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    rw [← TabRep.permC_eq hrep]
    exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem fixedCard_eq_card_filter (p : Equiv.Perm (Fin 1782)) :
    fixedCard p = (Finset.univ.filter fun x => p x = x).card := by
  rw [fixedCard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Function.mem_fixedPoints_iff]

theorem decSubgroup_le_invE {l : List Dec} (h : ∀ d ∈ l, ∀ k ∈ d.1, k < 10) :
    decSubgroup l ≤ invE 1 := by
  rw [decSubgroup, Subgroup.closure_le]
  rintro _ ⟨d, hd, rfl⟩
  exact decPerm_mem (h d hd)

theorem permC_tTab : permC 1782 tTab = suzInv 1 := by
  have hsize : tTab.size = 1782 := by
    have h := CFSG.Sporadic.SuzRecog.LocalR.sizes_facts.2.1 0 (by norm_num)
    simpa [CFSG.Sporadic.SuzRecog.LocalR.lambdaTab] using h
  exact TabRep.permC_eq ⟨hsize, rep_tTab⟩

theorem tabSubgroup_t0Tabs : tabSubgroup t0Tabs = C1Model.T0 := by
  rw [C1Model.T0_eq]
  unfold tabSubgroup
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    have hi4 : i.val < 4 := by simpa [C1Model.t0Tabs] using i.isLt
    refine ⟨i.val, hi4, ?_⟩
    change t0Gen i.val = permC 1782 t0Tabs[i.val]!
    rw [C1Model.t0Tabs_get hi4]
    exact (TabRep.permC_eq (tabRep_t0Tab hi4)).symm
  · rintro ⟨j, hj, rfl⟩
    have hj4 : j < 4 := by simpa [Array.size_ofFn] using hj
    refine ⟨⟨j, by simpa [C1Model.t0Tabs] using hj4⟩, ?_⟩
    change permC 1782 t0Tabs[j]! = t0Gen j
    rw [C1Model.t0Tabs_get hj4]
    exact TabRep.permC_eq (tabRep_t0Tab hj4)

theorem tabSubgroup_v0Tabs : tabSubgroup v0Tabs = C1Model.V0 := by
  rw [C1Model.V0_eq_closure_v0Gen]
  unfold tabSubgroup
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    have hi7 : i.val < 7 := by simpa [C1Model.v0Tabs] using i.isLt
    have hget : v0Tabs[i.val]! = v0Tab i.val := by
      unfold C1Model.v0Tabs
      exact getElem!_ofFn' _ hi7
    refine ⟨i.val, by simp [C1Model.v0Tabs, hi7], ?_⟩
    change v0Gen i.val = permC 1782 v0Tabs[i.val]!
    rw [hget]
    exact (TabRep.permC_eq (tabRep_v0Tab i.val)).symm
  · rintro ⟨j, hj, rfl⟩
    have hj7 : j < 7 := by simpa [Array.size_ofFn] using hj
    have hget : v0Tabs[j]! = v0Tab j := by
      unfold C1Model.v0Tabs
      exact getElem!_ofFn' _ hj7
    refine ⟨⟨j, by simpa [C1Model.v0Tabs] using hj7⟩, ?_⟩
    change permC 1782 v0Tabs[j]! = v0Gen j
    rw [hget]
    exact TabRep.permC_eq (tabRep_v0Tab j)

theorem tabSubgroup_c0Tabs : tabSubgroup c0Tabs = C1Model.C0 :=
  tabSubgroup_eq_of_enumerates C1Model.enumerates_C0

theorem tabSubgroup_ct0Tabs : tabSubgroup ct0Tabs = C1Model.CT0 :=
  tabSubgroup_eq_of_enumerates C1Model.enumerates_CT0

end Certificates

end CFSG.Sporadic.SuzRecog.SuzL34Cert
