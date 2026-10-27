module

public import CFSG.Permutation.FiveTransitive.OddStableInvolution
public import CFSG.Permutation.FiveTransitive.StableInvolutionPairs

public section

namespace CFSG

namespace FiveTransitive.OddDNormalization

open MulAction FixedFiveInvolutionGeometry StableInvolutionPairs

private theorem preserves_blocks
    {G X : Type*} [Group G] [MulAction G X]
    (e : Fin 13 ↪ X) (a c d : G) (hd : d * d = 1)
    (had : a * d = d * a) (hcd : c * d = d * c)
    (hfixa : fixedBy X a = {e 0, e 1, e 2, e 3, e 4})
    (hfixc : fixedBy X c = {e 0, e 1, e 2, e 5, e 6})
    (hfixac : fixedBy X (a * c) = {e 0, e 1, e 2, e 7, e 8}) :
    (∀ x ∈ ({e 0, e 1, e 2} : Set X), d • x ∈ ({e 0, e 1, e 2} : Set X)) ∧
    (∀ x ∈ ({e 3, e 4} : Set X), d • x ∈ ({e 3, e 4} : Set X)) ∧
    (∀ x ∈ ({e 5, e 6} : Set X), d • x ∈ ({e 5, e 6} : Set X)) ∧
    (∀ x ∈ ({e 7, e 8} : Set X), d • x ∈ ({e 7, e 8} : Set X)) := by
  have hacd : (a * c) * d = d * (a * c) := by
    calc
      (a * c) * d = a * (c * d) := mul_assoc _ _ _
      _ = a * (d * c) := by rw [hcd]
      _ = (a * d) * c := (mul_assoc _ _ _).symm
      _ = (d * a) * c := by rw [had]
      _ = d * (a * c) := mul_assoc _ _ _
  have hA := fun (x : X) (hx : x ∈ fixedBy X a) => mem_fixedBy_smul_of_commute a d had (x := x) hx
  have hC := fun (x : X) (hx : x ∈ fixedBy X c) => mem_fixedBy_smul_of_commute c d hcd (x := x) hx
  have hAC := fun (x : X) (hx : x ∈ fixedBy X (a * c)) => mem_fixedBy_smul_of_commute (a * c) d hacd (x := x) hx
  have hinter : fixedBy X a ∩ fixedBy X c = {e 0, e 1, e 2} := by
    rw [hfixa, hfixc]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxA, hxC⟩
      rcases hxA with rfl | rfl | rfl | rfl | rfl <;> simp_all [e.injective.eq_iff]
    · intro hx
      rcases hx with rfl | rfl | rfl <;> simp
  have hT : ∀ x ∈ ({e 0, e 1, e 2} : Set X), d • x ∈ ({e 0, e 1, e 2} : Set X) := by
    rw [← hinter]
    intro x hx
    exact ⟨hA x hx.1, hC x hx.2⟩
  have hAdiff : fixedBy X a \ {e 0, e 1, e 2} = {e 3, e 4} := by
    rw [hfixa]
    simp [e.injective.eq_iff]
  have hCdiff : fixedBy X c \ {e 0, e 1, e 2} = {e 5, e 6} := by
    rw [hfixc]
    simp [e.injective.eq_iff]
  have hACdiff : fixedBy X (a * c) \ {e 0, e 1, e 2} = {e 7, e 8} := by
    rw [hfixac]
    simp [e.injective.eq_iff]
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [← hAdiff]
    exact preserves_diff d hd _ _ hA hT
  · rw [← hCdiff]
    exact preserves_diff d hd _ _ hC hT
  · rw [← hACdiff]
    exact preserves_diff d hd _ _ hAC hT

private theorem relabel_fixed_zero
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (e : Fin 13 ↪ X) (d : G) (hd : d * d = 1)
    (hmaxd : (fixedBy X d).ncard ≤ 5)
    (hT : ∀ x ∈ ({e 0, e 1, e 2} : Set X), d • x ∈ ({e 0, e 1, e 2} : Set X))
    (hd9 : d • e 9 = e 9) (hd10 : d • e 10 = e 10)
    (hd11 : d • e 11 = e 11) (hd12 : d • e 12 = e 12) :
    ∃ E : Fin 13 ↪ X,
      (∀ i : Fin 13, 3 ≤ i.val → E i = e i) ∧
      ({E 0, E 1, E 2} : Set X) = {e 0, e 1, e 2} ∧
      fixedBy X d = {E 0, E 9, E 10, E 11, E 12} ∧ d • E 0 = E 0 := by
  classical
  have hTcard : ({e 0, e 1, e 2} : Set X).ncard = 3 := by simp [e.injective.eq_iff]
  obtain ⟨u, hu, hdu⟩ := OddStableInvolution.exists_fixed d hd {e 0, e 1, e 2}
    (by rw [hTcard]; decide) hT
  obtain ⟨j, hj, heju⟩ : ∃ j : Fin 13, j.val < 3 ∧ e j = u := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
  let E : Fin 13 ↪ X := (Equiv.swap 0 j).toEmbedding.trans e
  have he0 : E 0 = e j := by simp [E]
  have hEhigh : ∀ i : Fin 13, 3 ≤ i.val → E i = e i := by
    intro i hi
    have hi0 : i ≠ 0 := by omega
    have hij : i ≠ j := by omega
    simp [E, Equiv.swap_apply_def, hi0, hij]
  have htriple : ({E 0, E 1, E 2} : Set X) = {e 0, e 1, e 2} := by
    fin_cases j <;> norm_num at hj
    all_goals ext z; simp [E, Equiv.swap_apply_def] <;> tauto
  have hd0 : d • E 0 = E 0 := by rw [he0, heju]; exact hdu
  have hfixed : fixedBy X d = {E 0, E 9, E 10, E 11, E 12} := by
    apply fixedBy_eq_of_five d hmaxd
    · simp [E.injective.eq_iff]
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hd0
      · change d • E 9 = E 9
        rw [hEhigh 9 (by decide)]
        exact hd9
      · change d • E 10 = E 10
        rw [hEhigh 10 (by decide)]
        exact hd10
      · change d • E 11 = E 11
        rw [hEhigh 11 (by decide)]
        exact hd11
      · change d • E 12 = E 12
        rw [hEhigh 12 (by decide)]
        exact hd12
  exact ⟨E, hEhigh, htriple, hfixed, hd0⟩

theorem normalize_d
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (e : Fin 13 ↪ X) (a c d : G) (hd : d * d = 1)
    (hmaxd : (fixedBy X d).ncard ≤ 5)
    (had : a * d = d * a) (hcd : c * d = d * c)
    (hfixa : fixedBy X a = {e 0, e 1, e 2, e 3, e 4})
    (hfixc : fixedBy X c = {e 0, e 1, e 2, e 5, e 6})
    (hfixac : fixedBy X (a * c) = {e 0, e 1, e 2, e 7, e 8})
    (hd9 : d • e 9 = e 9) (hd10 : d • e 10 = e 10)
    (hd11 : d • e 11 = e 11) (hd12 : d • e 12 = e 12) :
    ∃ E : Fin 13 ↪ X,
      (∀ i : Fin 13, 3 ≤ i.val → E i = e i) ∧
      fixedBy X a = {E 0, E 1, E 2, E 3, E 4} ∧
      fixedBy X c = {E 0, E 1, E 2, E 5, E 6} ∧
      fixedBy X (a * c) = {E 0, E 1, E 2, E 7, E 8} ∧
      fixedBy X d = {E 0, E 9, E 10, E 11, E 12} ∧
      d • E 0 = E 0 ∧ d • E 1 = E 2 ∧ d • E 2 = E 1 ∧
      d • E 3 = E 4 ∧ d • E 4 = E 3 ∧
      d • E 5 = E 6 ∧ d • E 6 = E 5 ∧
      d • E 7 = E 8 ∧ d • E 8 = E 7 := by
  obtain ⟨hT, h34, h56, h78⟩ := preserves_blocks e a c d hd had hcd hfixa hfixc hfixac
  obtain ⟨E, hEhigh, htriple, hfixd, hd0⟩ :=
    relabel_fixed_zero e d hd hmaxd hT hd9 hd10 hd11 hd12
  have hsets (i j : Fin 13) (hi : 3 ≤ i.val) (hj : 3 ≤ j.val) :
      ({E 0, E 1, E 2, E i, E j} : Set X) = {e 0, e 1, e 2, e i, e j} := by
    calc
      ({E 0, E 1, E 2, E i, E j} : Set X) = {E 0, E 1, E 2} ∪ {E i, E j} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
        tauto
      _ = {e 0, e 1, e 2} ∪ {e i, e j} := by rw [htriple, hEhigh i hi, hEhigh j hj]
      _ = {e 0, e 1, e 2, e i, e j} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
        tauto
  have hTE : ∀ x ∈ ({E 0, E 1, E 2} : Set X), d • x ∈ ({E 0, E 1, E 2} : Set X) := by
    rwa [htriple]
  have hdiff : ({E 0, E 1, E 2} : Set X) \ {E 0} = {E 1, E 2} := by
    simp [E.injective.eq_iff]
  have h12 : ∀ x ∈ ({E 1, E 2} : Set X), d • x ∈ ({E 1, E 2} : Set X) := by
    rw [← hdiff]
    apply preserves_diff d hd _ _ hTE
    intro x hx
    simpa only [Set.mem_singleton_iff] using (show d • x = E 0 from by
      rw [Set.mem_singleton_iff] at hx
      rw [hx, hd0])
  have h34E : ∀ x ∈ ({E 3, E 4} : Set X), d • x ∈ ({E 3, E 4} : Set X) := by
    simpa only [hEhigh 3 (by decide), hEhigh 4 (by decide)] using h34
  have h56E : ∀ x ∈ ({E 5, E 6} : Set X), d • x ∈ ({E 5, E 6} : Set X) := by
    simpa only [hEhigh 5 (by decide), hEhigh 6 (by decide)] using h56
  have h78E : ∀ x ∈ ({E 7, E 8} : Set X), d • x ∈ ({E 7, E 8} : Set X) := by
    simpa only [hEhigh 7 (by decide), hEhigh 8 (by decide)] using h78
  have hnonfix (i : Fin 13) (hi0 : i ≠ 0) (hi9 : i.val < 9) : d • E i ≠ E i := by
    intro he
    have hm : E i ∈ fixedBy X d := he
    rw [hfixd] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, E.injective.eq_iff] at hm
    rcases hm with h | h | h | h | h <;> omega
  obtain ⟨hd1, hd2⟩ := swap_pair d hd (E 1) (E 2) h12 (hnonfix 1 (by decide) (by decide))
  obtain ⟨hd3, hd4⟩ := swap_pair d hd (E 3) (E 4) h34E (hnonfix 3 (by decide) (by decide))
  obtain ⟨hd5, hd6⟩ := swap_pair d hd (E 5) (E 6) h56E (hnonfix 5 (by decide) (by decide))
  obtain ⟨hd7, hd8⟩ := swap_pair d hd (E 7) (E 8) h78E (hnonfix 7 (by decide) (by decide))
  refine ⟨E, hEhigh, ?_, ?_, ?_, hfixd, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  · exact hfixa.trans (hsets 3 4 (by decide) (by decide)).symm
  · exact hfixc.trans (hsets 5 6 (by decide) (by decide)).symm
  · exact hfixac.trans (hsets 7 8 (by decide) (by decide)).symm

end FiveTransitive.OddDNormalization

end CFSG
