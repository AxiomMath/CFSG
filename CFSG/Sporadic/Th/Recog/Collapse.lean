module

public import Certificates.Certificate687001
public import CFSG.Sporadic.Recognition.PresentedWordsClosure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.CosetTable
open CFSG.Sporadic.Recognition.PresentedWords

@[expose] def sbWord : List (Fin 8 × Bool) :=
  commWord [(5, true)] [(1, true)]

theorem mem_R0' (w : List (Fin 8 × Bool)) (hw : w ∈ R0') :
    w ∈ bfree ∨ w ∈ brel ∨ w = sbWord := by
  have hcheck : (R0'.all fun w =>
      (w.all fun l => l.1 ≠ 1) ||
        (w.any (fun l => l.1 = 1) && w.all fun l => l.1 ≠ 5) ||
          decide (w = sbWord)) = true := by
    simp only [R0', TauCeti.GroupPresentation.relators_def,
      TauCeti.Sporadic.Thompson.presentation, TauCeti.Sporadic.Thompson.relatorList,
      TauCeti.Sporadic.Thompson.relatorsOne, TauCeti.Sporadic.Thompson.relatorsTwo,
      TauCeti.Sporadic.Thompson.relatorsThree, TauCeti.Sporadic.Thompson.relatorsFour,
      TauCeti.Sporadic.Thompson.relatorsFive, TauCeti.Sporadic.Thompson.relatorsSix,
      TauCeti.Sporadic.Thompson.genA, TauCeti.Sporadic.Thompson.genB,
      TauCeti.Sporadic.Thompson.genC, TauCeti.Sporadic.Thompson.genD,
      TauCeti.Sporadic.Thompson.genE, TauCeti.Sporadic.Thompson.genS,
      TauCeti.Sporadic.Thompson.genT, TauCeti.Sporadic.Thompson.genU,
      TauCeti.Relator.toWord_gen, TauCeti.Relator.toWord_pow, TauCeti.Relator.toWord_mul,
      TauCeti.Relator.toWord_inv, TauCeti.Relator.toWord_div, TauCeti.Relator.toWord_conj,
      TauCeti.Relator.toWord_commInvInv, sbWord, commWord, List.map_cons, List.map_append,
      List.map_nil]
    decide
  have h := List.all_eq_true.mp hcheck w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (h | ⟨h1, h2⟩) | h
  · exact Or.inl (List.mem_filter.mpr ⟨hw, h⟩)
  · refine Or.inr (Or.inl (List.mem_filter.mpr ⟨hw, ?_⟩))
    rw [h1, h2]
    rfl
  · exact Or.inr (Or.inr (by simpa using h))

theorem mem_closure_of_collapse (c : Config)
    (hc : c ≠ (.id, 0)) {G : Type*} [Group G] (x : Fin 8 → G)
    (hx : ∀ w ∈ collapseRels c, wprod x w = 1) :
    x 1 ∈ Subgroup.closure (x '' {j | j ≠ 1}) := by
  obtain ⟨hfi, hle⟩ := Certificates.certificate687001 c hc
  have hsub : {j : Fin 8 | j ∈ subsetOf 8 [0, 2, 3, 4, 5, 6, 7]} = {j | j ≠ 1} := by
    ext j
    fin_cases j <;> decide
  set rels := {r : FreeGroup (Fin 8) | r ∈ (collapseRels c).map FreeGroup.mk}
  have htop : genSub rels (subsetOf 8 [0, 2, 3, 4, 5, 6, 7]) = ⊤ :=
    Subgroup.index_eq_one.mp (Nat.le_antisymm hle (Nat.pos_of_ne_zero hfi.index_ne_zero))
  have hmem : (PresentedGroup.of 1 : PG 8 (collapseRels c)) ∈
      genSub rels (subsetOf 8 [0, 2, 3, 4, 5, 6, 7]) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (pgHom x hx) hmem
  rw [MonoidHom.map_closure, pgHom_of] at hmap
  rw [← hsub]
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨y, ⟨j, hj, rfl⟩, rfl⟩
  rw [pgHom_of]
  exact Set.mem_image_of_mem x hj

theorem collapseRels_of {G : Type*} [Group G] (c : Config) (x : Fin 8 → G)
    (hfree : ∀ w ∈ bfree, wprod x w = 1)
    (hrel : ∀ w ∈ brel,
      wprod (fun i => wprod x ((hsK c.1).getD i [])) w = 1)
    (hcomm : ∀ j : Fin 2,
      Commute (x 5) (wprod x (substWord (hsK c.1) (xw c j)))) :
    ∀ w ∈ collapseRels c, wprod x w = 1 := by
  intro w hw
  rw [collapseRels] at hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · exact hfree w hw
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      rw [wprod_substWord]
      exact hrel r hr
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    have h5 : wprod x [(5, true)] = x 5 := by
      simp [wprod]
    rw [wprod_commWord, h5, ← mul_inv_rev, mul_assoc, (hcomm j).eq, inv_mul_cancel]

theorem hsw_of_parts {G : Type*} [Group G] (x : Fin 8 → G)
    (h1 : ∀ w ∈ bfree, wprod x w = 1) (h2 : ∀ w ∈ brel, wprod x w = 1)
    (h3 : wprod x sbWord = 1) : ∀ w ∈ R0', wprod x w = 1 := by
  intro w hw
  rcases mem_R0' w hw with hw | hw | rfl
  · exact h1 w hw
  · exact h2 w hw
  · exact h3

end CFSG.Sporadic.Th.Recog
