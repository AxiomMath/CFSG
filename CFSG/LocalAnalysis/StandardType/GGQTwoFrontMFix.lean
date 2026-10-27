module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkBlocks
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall

public section

namespace CFSG.StandardType.QTwo

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType

private theorem qTwoFrontM_fix_isSolvable_sup_of_comm {G : Type*} [Group G]
    {A B : Subgroup G} (hcomm : A ≤ Subgroup.centralizer (B : Set G))
    [Group.IsSolvable ↥A] [Group.IsSolvable ↥B] :
    Group.IsSolvable ↥(A ⊔ B) := by
  have hcomm' : ∀ (a : ↥A) (b : ↥B), Commute (a : G) (b : G) := fun a b =>
    (Subgroup.mem_centralizer_iff.mp (hcomm a.2) b b.2).symm
  let f : ↥A × ↥B →* G := MonoidHom.noncommCoprod A.subtype B.subtype hcomm'
  have hrange : f.range = A ⊔ B := by
    change (MonoidHom.noncommCoprod A.subtype B.subtype hcomm').range = A ⊔ B
    rw [MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm', Subgroup.range_subtype,
      Subgroup.range_subtype]
  let g : ↥A × ↥B →* ↥(A ⊔ B) :=
    f.codRestrict (A ⊔ B) fun x => by rw [← hrange]; exact ⟨x, rfl⟩
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := (show (y : G) ∈ f.range from by rw [hrange]; exact y.2)
    exact ⟨x, Subtype.ext hx⟩
  exact Group.isSolvable_of_surjective hsurj

private theorem qTwoFrontM_fix_le_centralizer_sup {G : Type*} [Group G]
    {A B C : Subgroup G} (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hAC : A ≤ Subgroup.centralizer (C : Set G)) :
    A ≤ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with hxB | hxC
  · exact (Subgroup.mem_centralizer_iff.mp (hAB ha)) x hxB
  · exact (Subgroup.mem_centralizer_iff.mp (hAC ha)) x hxC

private theorem qTwoFrontM_fix_le_centralizer_finset_sup {G ι : Type*} [Group G]
    {A : Subgroup G} {f : ι → Subgroup G} {s : Finset ι}
    (h : ∀ j ∈ s, A ≤ Subgroup.centralizer (f j : Set G)) :
    A ≤ Subgroup.centralizer ((s.sup f : Subgroup G) : Set G) := by
  classical
  revert h
  induction s using Finset.induction with
  | empty =>
    intro _
    rw [Finset.sup_empty]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_bot.mp hy]
    simp
  | insert i s hi ih =>
    intro h
    rw [Finset.sup_insert]
    exact qTwoFrontM_fix_le_centralizer_sup (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem qTwoFrontM_fix_isSolvable_finset_sup {G ι : Type*} [Group G]
    (f : ι → Subgroup G) (s : Finset ι)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      f i = f j ∨ f i ≤ Subgroup.centralizer (f j : Set G))
    (hsol : ∀ i ∈ s, Group.IsSolvable ↥(f i)) :
    Group.IsSolvable ↥(s.sup f) := by
  classical
  revert hcomm hsol
  induction s using Finset.induction with
  | empty =>
    intro _ _
    rw [Finset.sup_empty]
    exact Group.isSolvable_of_comm fun a b => Subtype.ext (by
      simp [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])
  | insert i s hi ih =>
    intro hcomm hsol
    rw [Finset.sup_insert]
    have hsol_i : Group.IsSolvable ↥(f i) := hsol i (Finset.mem_insert_self i s)
    have hsol_s : Group.IsSolvable ↥(s.sup f) :=
      ih (fun j hj k hk hjk =>
            hcomm j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
        (fun j hj => hsol j (Finset.mem_insert_of_mem hj))
    by_cases hex : ∃ j ∈ s, f j = f i
    · obtain ⟨j, hj, hji⟩ := hex
      rw [show f i ⊔ s.sup f = s.sup f from sup_eq_right.mpr (hji ▸ Finset.le_sup hj)]
      exact hsol_s
    · push Not at hex
      have hcent : f i ≤ Subgroup.centralizer ((s.sup f : Subgroup G) : Set G) :=
        qTwoFrontM_fix_le_centralizer_finset_sup (A := f i) (f := f) (s := s) fun j hj => by
          rcases hcomm i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
            (by rintro rfl; exact hi hj) with heq | hc
          · exact absurd heq.symm (hex j hj)
          · exact hc
      haveI := hsol_i
      haveI := hsol_s
      exact qTwoFrontM_fix_isSolvable_sup_of_comm hcent

private theorem qTwoFrontM_fix_blockSU_solvable {K : Type} [Field K] [Finite K] {d : ℕ}
    (h : UnitaryFieldData 2 1 K) {I : Finset (Fin d)} (h1 : 1 ≤ I.card) (h3 : I.card ≤ 3) :
    Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) I) := by
  haveI : Group.IsSolvable ↥(unitarySU 2 1 K I.card) :=
    SmallU.isSolvable_unitarySU_small h h1 h3
  let e := TableBUE.blockSUEquiv (K := K) (n := 1) I h
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
    (fun x y hxy => e.symm.injective hxy)

theorem qTwoFrontM_ggFix_solvable {K : Type} [Field K] [Finite K] (hKd : UnitaryFieldData 2 1 K)
    {t : Fin 4 → K} (ht : ∀ i, t i ≠ 0) (hnc : ∃ i j, t i ≠ t j)
    (δ : MulAut ↥(unitarySU 2 1 K 4))
    (hδ : ∀ s : ↥(unitarySU 2 1 K 4),
      (((δ s : ↥(unitarySU 2 1 K 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * diagonal t =
        diagonal t * ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    Group.IsSolvable ↥(ggFix δ) := by
  classical
  obtain ⟨-, hcommBlocks, hder⟩ :=
    ggFix_diag_block_structure (d := 4) (n := 1) hKd ht δ hδ
  let B : Fin 4 → Subgroup ↥(unitarySU 2 1 K 4) := fun i₀ =>
    TableBUE.blockSU (K := K) (n := 1) (Finset.univ.filter fun i => t i = t i₀)
  have hBsol : ∀ i₀ : Fin 4, Group.IsSolvable ↥(B i₀) := by
    intro i₀
    have hI1 : 1 ≤ (Finset.univ.filter fun i => t i = t i₀).card :=
      Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hI3 : (Finset.univ.filter fun i => t i = t i₀).card ≤ 3 := by
      have hle : (Finset.univ.filter fun i => t i = t i₀).card ≤ 4 := by
        have h := Finset.card_le_card (Finset.filter_subset (fun i => t i = t i₀) Finset.univ)
        simpa using h
      rcases lt_or_eq_of_le hle with hlt | heq
      · omega
      · exfalso
        have hIuniv : (Finset.univ.filter fun i => t i = t i₀) = Finset.univ :=
          Finset.eq_univ_of_card _ (by simpa using heq)
        obtain ⟨i, j, hij⟩ := hnc
        have hi : t i = t i₀ := by
          have hmem : i ∈ Finset.univ.filter (fun i => t i = t i₀) := by
            rw [hIuniv]; exact Finset.mem_univ i
          simpa using hmem
        have hj : t j = t i₀ := by
          have hmem : j ∈ Finset.univ.filter (fun i => t i = t i₀) := by
            rw [hIuniv]; exact Finset.mem_univ j
          simpa using hmem
        exact hij (hi.trans hj.symm)
    exact qTwoFrontM_fix_blockSU_solvable hKd hI1 hI3
  have hBcomm : ∀ i j : Fin 4, i ≠ j →
      B i = B j ∨ B i ≤ Subgroup.centralizer (B j : Set ↥(unitarySU 2 1 K 4)) := by
    intro i j _
    by_cases hval : t i = t j
    · left
      have hfilter : (Finset.univ.filter fun k => t k = t i) =
          (Finset.univ.filter fun k => t k = t j) := by
        apply Finset.filter_congr
        intro k _
        rw [hval]
      exact congrArg (fun I : Finset (Fin 4) =>
        TableBUE.blockSU (K := K) (n := 1) I) hfilter
    · right
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcommBlocks i j hval x hx y hy).symm
  have hJsol : Group.IsSolvable ↥(Finset.univ.sup B) :=
    qTwoFrontM_fix_isSolvable_finset_sup B Finset.univ
      (fun i _ j _ hij => hBcomm i j hij) (fun i _ => hBsol i)
  have hle : (commutator ↥(ggFix δ)).map (ggFix δ).subtype ≤ Finset.univ.sup B := by
    rw [Subgroup.map_subtype_commutator (ggFix δ), Finset.sup_univ_eq_iSup]
    exact hder
  haveI : Group.IsSolvable ↥(Finset.univ.sup B) := hJsol
  let e := Subgroup.equivMapOfInjective (commutator ↥(ggFix δ)) (ggFix δ).subtype
    (Subgroup.subtype_injective (ggFix δ))
  let g : ↥(commutator ↥(ggFix δ)) →* ↥(Finset.univ.sup B) :=
    (Subgroup.inclusion hle).comp e.toMonoidHom
  exact (Group.isSolvable_commutator_iff (G := ↥(ggFix δ))).mp
    (Group.isSolvable_of_isSolvable_injective (f := g)
      ((Subgroup.inclusion_injective hle).comp e.injective))

end CFSG.StandardType.QTwo

end
