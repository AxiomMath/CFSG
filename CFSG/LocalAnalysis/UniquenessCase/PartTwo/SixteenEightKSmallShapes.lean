module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.CharacterTheory.Burnside
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LieType.BorelTits (orthGroup statedOmega_le_orthGroup)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
  (card_orthGroup_quadPlus_two)

private theorem s16k_not_isSolvable_of_isQuasisimple {Q : Type} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hs
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at h
  exact lt_irrefl _ h

private theorem s16k_card_GL_fin_le_six {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {d : ℕ} (hd : d ≤ 2) : Nat.card (GL (Fin d) K) < 60 := by
  rw [Matrix.card_GL_field]
  interval_cases d <;> simp_all <;> norm_num

private theorem s16k_card_GL_le_six {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Fintype K] (hK : Fintype.card K = 2) (hι : Fintype.card ι ≤ 2) :
    Nat.card (GL ι K) < 60 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h := Nat.card_congr (Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv).toEquiv
  rw [h]
  exact s16k_card_GL_fin_le_six hK hι

private theorem s16k_isSolvable_GL_of_card_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2) :
    Group.IsSolvable (GL ι K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact CFSG.GroupTheory.groups_order_below_sixty_solvable (s16k_card_GL_le_six hK' hι)

private theorem s16k_isSolvable_subgroup_GL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2)
    (H : Subgroup (GL ι K)) : Group.IsSolvable ↥H :=
  haveI := s16k_isSolvable_GL_of_card_le_two hK hι
  Group.isSolvable_of_isSolvable_injective (f := H.subtype) H.subtype_injective

private theorem s16k_isSolvable_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2)
    (H : Subgroup (GL ι K)) : Group.IsSolvable (StatedProj H) :=
  haveI := s16k_isSolvable_subgroup_GL hK hι H
  Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective ((StatedScalars ι K).subgroupOf H))

private theorem s16k_isSolvable_orthGroup_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(orthGroup (StatedQuadPlus 2 K)) := by
  have hcard : Nat.card ↥(orthGroup (StatedQuadPlus 2 K)) = 2 ^ 3 * 3 ^ 2 := by
    rw [card_orthGroup_quadPlus_two, hK]
    norm_num
  haveI : Fintype ↥(orthGroup (StatedQuadPlus 2 K)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

private theorem s16k_isSolvable_statedOmega_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) :=
  haveI := s16k_isSolvable_orthGroup_quadPlus_two hK
  Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (statedOmega_le_orthGroup (StatedQuadPlus 2 K)))
    (Subgroup.inclusion_injective _)

private theorem s16k_isSolvable_statedProj_statedOmega_quadPlus_two {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
  haveI := s16k_isSolvable_statedOmega_quadPlus_two hK
  Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadPlus 2 K))))

theorem s16k_three_le_of_isSLn {X : Type} [Group X] {n : ℕ} (hq : CFSG.Open.IsQuasisimple X)
    (h : IsSLn X n 1) : 3 ≤ n := by
  by_contra hlt
  have hn : n ≤ 2 := by omega
  obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  haveI : Group.IsSolvable ↥(StatedSL n K) :=
    s16k_isSolvable_subgroup_GL hK (by simpa using hn) (StatedSL n K)
  haveI : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance

theorem s16k_six_le_of_isSpn {X : Type} [Group X] {n : ℕ} (hq : CFSG.Open.IsQuasisimple X)
    (h : IsSpn X n 1) : 6 ≤ n := by
  by_contra hlt
  have hn : n ≤ 5 := by omega
  obtain ⟨hev, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨r, hr⟩ := hev
  have hn' : n = 0 ∨ n = 2 ∨ n = 4 := by omega
  rcases hn' with rfl | rfl | rfl
  · haveI : Group.IsSolvable ↥(StatedSp (0 / 2) K) :=
      s16k_isSolvable_subgroup_GL hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num) (StatedSp (0 / 2) K)
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable ↥(StatedSp (2 / 2) K) :=
      s16k_isSolvable_subgroup_GL hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num) (StatedSp (2 / 2) K)
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    obtain ⟨f⟩ :=
      CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := K) hK'
    haveI : Group.IsPerfect X := by rw [Group.isPerfect_def]; exact hq.1
    haveI : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
      Group.IsPerfect.ofSurjective (f := (e.trans f).toMonoidHom) (e.trans f).surjective
    have htop : (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))) = ⊤ := by
      have hc := alternatingGroup.commutator_perm_eq (α := Fin 6) (by simp)
      rw [Group.IsPerfect.commutator_eq_top] at hc
      exact hc.symm
    have hswap : Equiv.swap (0 : Fin 6) 1 ∈
        (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hswap
    exact absurd hswap (by decide)

theorem s16k_six_le_of_isOmegaPlus {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsOmegaPlus X n 1) : 6 ≤ n := by
  by_contra hlt
  have hn : n ≤ 5 := by omega
  obtain ⟨hev, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨r, hr⟩ := hev
  have hn' : n = 0 ∨ n = 2 ∨ n = 4 := by omega
  rcases hn' with rfl | rfl | rfl
  · haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (0 / 2) K))) :=
      s16k_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadPlus (0 / 2) K))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (2 / 2) K))) :=
      s16k_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadPlus (2 / 2) K))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
      s16k_isSolvable_statedProj_statedOmega_quadPlus_two hK
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance

theorem s16k_four_le_of_isOmegaMinus {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsOmegaMinus X n 1) : 4 ≤ n := by
  by_contra hlt
  have hn : n ≤ 3 := by omega
  obtain ⟨hev, K, hF, hfin, b, c, hcard, hpoly, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨r, hr⟩ := hev
  have hn' : n = 0 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl
  · haveI : Group.IsSolvable
        (StatedProj (StatedOmega (StatedQuadMinus (0 / 2) K b c))) :=
      s16k_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadMinus (0 / 2) K b c))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable
        (StatedProj (StatedOmega (StatedQuadMinus (2 / 2) K b c))) :=
      s16k_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadMinus (2 / 2) K b c))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance

theorem s16k_five_le_of_isAlt {X : Type} [Group X] {n : ℕ} (hq : CFSG.Open.IsQuasisimple X)
    (h : IsAlt X n) : 5 ≤ n := by
  by_contra hlt
  have hn : n ≤ 4 := by omega
  obtain ⟨e⟩ := h
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by simpa using hn)
  haveI : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (s16k_not_isSolvable_of_isQuasisimple hq) inferInstance

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
