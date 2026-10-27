module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
import CFSG.GF2Type.Smith1979W3.CaseD.Jordan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec19.Item19Res4Proof
open Equiv

private def a6a : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 0 2, by rw [Perm.mem_alternatingGroup]; decide⟩

private def a6b : alternatingGroup (Fin 6) :=
  ⟨swap 3 4 * swap 3 5, by rw [Perm.mem_alternatingGroup]; decide⟩

private lemma a6a_pow_three : a6a ^ 3 = 1 := by
  apply Subtype.ext
  change (swap 0 1 * swap 0 2 : Perm (Fin 6)) ^ 3 = 1
  decide

private lemma a6b_pow_three : a6b ^ 3 = 1 := by
  apply Subtype.ext
  change (swap 3 4 * swap 3 5 : Perm (Fin 6)) ^ 3 = 1
  decide

private lemma a6a_isThreeCycle : Perm.IsThreeCycle (a6a : Perm (Fin 6)) := by
  change Perm.IsThreeCycle (swap 0 1 * swap 0 2 : Perm (Fin 6))
  exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma a6b_isThreeCycle : Perm.IsThreeCycle (a6b : Perm (Fin 6)) := by
  change Perm.IsThreeCycle (swap 3 4 * swap 3 5 : Perm (Fin 6))
  exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma a6a_disjoint_a6b :
    Perm.Disjoint (a6a : Perm (Fin 6)) (a6b : Perm (Fin 6)) := by
  change Perm.Disjoint (swap 0 1 * swap 0 2 : Perm (Fin 6)) (swap 3 4 * swap 3 5)
  rw [Perm.disjoint_iff_eq_or_eq]
  intro x
  fin_cases x <;> decide

private lemma a6a_mul_a6b_eq : a6a * a6b = a6b * a6a :=
  Subtype.ext (Perm.Disjoint.commute a6a_disjoint_a6b)

theorem exists_noncommute_three_of_isA6ModZ3 {X : Type} [Group X] [Finite X]
    (hX : IsA6ModZ3 X) :
    ∃ P : Subgroup X, IsPGroup 3 P ∧
      ∃ x ∈ P, ∃ y ∈ P, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨⟨hq, ⟨e⟩⟩, hZcard⟩ := hX
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have htriple : IsTripleA6 X := ⟨hZcard, ⟨e⟩⟩
  let A : Subgroup (Perm (Fin 6)) := alternatingGroup (Fin 6)
  let Z : Subgroup X := Subgroup.center X
  let π : X →* A := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  set K : Set A := {a6a, a6b} with hK
  set H : Subgroup A := Subgroup.closure K with hH
  let P : Subgroup X := H.comap π
  have hπ_surj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (N := Z))
  have hcardX : Nat.card X = 1080 := card_eq_of_isTripleA6 htriple
  have hcardA : Nat.card A = 360 := card_alternatingGroup_six'
  have hker_eq : π.ker = Z := by
    ext x
    constructor
    · intro hx
      have hx1 : π x = 1 := MonoidHom.mem_ker.mp hx
      apply (QuotientGroup.eq_one_iff (N := Z) x).mp
      apply e.injective
      rw [map_one]
      change π x = 1
      exact hx1
    · intro hx
      change π x = 1
      change e (QuotientGroup.mk x : X ⧸ Z) = 1
      rw [(QuotientGroup.eq_one_iff (N := Z) x).mpr hx, map_one]
  have hkerπ : IsPGroup 3 π.ker := by
    rw [hker_eq]
    exact IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZcard)
  have hHcomm : IsMulCommutative H := by
    rw [hH]
    refine Subgroup.isMulCommutative_closure ?_
    rw [hK]
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact a6a_mul_a6b_eq
    · exact a6a_mul_a6b_eq.symm
    · exact (hxy rfl).elim
  have hHexp : ∀ y ∈ H, y ^ 3 = 1 := by
    intro y hy
    rw [hH] at hy
    refine Subgroup.closure_induction (p := fun z _ => z ^ 3 = 1) ?_ ?_ ?_ ?_ hy
    · intro x hx
      rw [hK] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact a6a_pow_three
      · exact a6b_pow_three
    · simp
    · intro x z hx hz hx3 hz3
      have hc : Commute x z := by
        have h := hHcomm.is_comm.comm (⟨x, by rwa [hH]⟩ : H) (⟨z, by rwa [hH]⟩ : H)
        exact congrArg Subtype.val h
      rw [hc.mul_pow 3, hx3, hz3, mul_one]
    · intro x _ hx3
      rw [inv_pow, hx3, inv_one]
  have hcardH : Nat.card H = 9 := by
    have hmap : H.map (Subgroup.subtype A) =
        Subgroup.closure ({(a6a : Perm (Fin 6)), (a6b : Perm (Fin 6))} :
          Set (Perm (Fin 6))) := by
      rw [hH, hK, MonoidHom.map_closure]
      congr 1
      ext x
      simp
    have hcard_map : Nat.card (H.map (Subgroup.subtype A)) = Nat.card H :=
      Subgroup.card_map_of_injective (K := H) (f := Subgroup.subtype A)
        (Subgroup.subtype_injective A)
    rw [← hcard_map, hmap]
    exact CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles
      a6a_isThreeCycle a6b_isThreeCycle a6a_disjoint_a6b
  have hH_pgroup : IsPGroup 3 H := by
    apply IsPGroup.of_card (n := 2)
    rw [hcardH]
    norm_num
  have hP_isP : IsPGroup 3 P := hH_pgroup.comap_of_ker_isPGroup π hkerπ
  have hIndex : P.index = H.index :=
    Subgroup.index_comap_of_surjective (H := H) hπ_surj
  have hHindex : H.index = 40 := by
    have h := Subgroup.card_mul_index H
    rw [hcardH, hcardA] at h
    omega
  have hPow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    have hπx3 : (π x) ^ 3 = 1 := hHexp (π x) hx
    apply pow_three_eq_one_of_isTripleA6 htriple
    apply e.injective
    rw [map_pow, map_one]
    change (π x) ^ 3 = 1
    exact hπx3
  have hPnoncomm : ¬ IsMulCommutative P := by
    intro hPcomm
    have hE : CFSG.Open.IsElemAbelian 3 P := ⟨hPcomm, fun x hx => hPow x hx⟩
    have hcardP : Nat.card P = 27 := by
      have h := Subgroup.card_mul_index P
      rw [hIndex, hHindex, hcardX] at h
      omega
    exact card_ne_twentySeven_of_isTripleA6 htriple P hE hcardP
  rw [isMulCommutative_iff] at hPnoncomm
  push Not at hPnoncomm
  obtain ⟨x, y, hxy⟩ := hPnoncomm
  exact ⟨P, hP_isP, x.1, x.2, y.1, y.2, hPow x.1 x.2, hPow y.1 y.2,
    fun h => hxy (Subtype.ext h)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
