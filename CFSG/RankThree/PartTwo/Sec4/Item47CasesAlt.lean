module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveOut
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_isQuasisimple_of_isSolvable {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X)
    (hs : Group.IsSolvable X) : False := by
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hp : Group.IsPerfect X := hq.1
  have htop : ∀ m : ℕ, derivedSeries X m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [derivedSeries_succ, ih]
      exact Group.IsPerfect.commutator_eq_top
  obtain ⟨n, hn⟩ := hs.solvable
  rw [htop n] at hn
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  have hx : x ∈ (⊥ : Subgroup X) := hn ▸ Subgroup.mem_top x
  have hy : y ∈ (⊥ : Subgroup X) := hn ▸ Subgroup.mem_top y
  rw [Subgroup.mem_bot] at hx hy
  exact hxy (hx.trans hy.symm)

theorem isSolvable_alternatingGroup_of_le_four {n : ℕ} (hn : n ≤ 4) :
    Group.IsSolvable (alternatingGroup (Fin n)) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    have : Subsingleton (alternatingGroup (Fin n)) := inferInstance
    infer_instance
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h
    have hcard : Fintype.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
      rw [card_alternatingGroup, Fintype.card_fin]
    interval_cases n
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 0)
        (b := 0) Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcard]; decide)
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 0)
        (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcard]; decide)
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 2)
        (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcard]; decide)

theorem cubeInner_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    CubeInner (alternatingGroup (Fin n)) := by
  apply cubeInner_of_not_three_dvd_card_outer
  rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with h | rfl | h
  · intro h3
    have h2 := outer_card_dvd_two_of_equiv_outside_six (Or.inl h) (MulEquiv.refl _)
    have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
    omega
  · exact CFSG.Quasithin.A10.three_not_dvd_card_outer (MulEquiv.refl _)
  · intro h3
    have h2 := outer_card_dvd_two_of_equiv_outside_six (Or.inr h) (MulEquiv.refl _)
    have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
    omega

theorem cubeInner_of_isExtOf {X Y : Type} [Group X] [Group Y] (hX : CFSG.IsQuasisimple X)
    (hY : Subgroup.center Y = ⊥) (hYc : CubeInner Y)
    (h : IsExtOf X Y (Multiplicative (ZMod 3))) : CubeInner X := by
  obtain ⟨-, ⟨e⟩⟩ := (isTripleCover_iff_isExtOf hX hY).mpr h
  have : Group.IsPerfect X := hX.1
  exact cubeInner_of_center_quotient (hYc.of_mulEquiv e)

theorem false_of_list46_four (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hL : (∃ n : ℕ, n ≤ 9 ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin n))) ∨
      IsExtOf (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6))
        (Multiplicative (ZMod 3)) ∨
      IsExtOf (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7))
        (Multiplicative (ZMod 3)))
    {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  rcases hL with ⟨n, -, he₁⟩ | h6 | h7
  · obtain ⟨e₁⟩ := he₁
    rcases Nat.lt_or_ge n 5 with hn | hn
    · exact false_of_isQuasisimple_of_isSolvable hq
        (by
          have := isSolvable_alternatingGroup_of_le_four (n := n) (by omega)
          exact Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)
    · exact false_of_cubeInner e₁ (cubeInner_alternatingGroup hn) ha3 hout
  · exact false_of_cubeInner (MulEquiv.refl _)
      (cubeInner_of_isExtOf hq (alternatingGroup.center_eq_bot (by simp))
        (cubeInner_alternatingGroup (by norm_num)) h6) ha3 hout
  · exact false_of_cubeInner (MulEquiv.refl _)
      (cubeInner_of_isExtOf hq (alternatingGroup.center_eq_bot (by simp))
        (cubeInner_alternatingGroup (by norm_num)) h7) ha3 hout

theorem false_of_list46_five
    (hin : Inputs47NoD4)
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hL : (∃ s ∈ sporadics46,
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.Carrier s)) ∨
      ∃ s ∈ sporadicCovers46, IsExtOf (L ⧸ aschbacherSolvableCore 3 L)
        (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3)))
    {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  rcases hL with ⟨s, hs, he₁⟩ | ⟨s, hs, h⟩
  · obtain ⟨e₁⟩ := he₁
    exact false_of_cubeInner e₁
      (cubeInner_of_not_three_dvd_card_outer (hin.outSporadic s (Or.inl hs))) ha3 hout
  · exact false_of_cubeInner (MulEquiv.refl _)
      (cubeInner_of_isExtOf hq (hin.centerSporadic s hs)
        (cubeInner_of_not_three_dvd_card_outer (hin.outSporadic s (Or.inr hs))) h) ha3 hout

end CFSG.RankThree.PartTwo.Sec4
