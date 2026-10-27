module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.Background.A3FactsClassical
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.OmegaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
public import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (orthGroup orthGroup_preserves statedOmega_le_orthGroup)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
  (card_orthGroup_quadPlus_two)
open scoped commutatorElement

variable {W : Type} [CommGroup W]

private theorem s16h_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

private theorem s16h_not_isMulCommutative_of_isQuasisimple {X : Type} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) : ¬ IsMulCommutative X := by
  intro h
  haveI := h
  have hc : Subgroup.center X = ⊤ := Subgroup.center_eq_top
  haveI : Subsingleton (X ⧸ Subgroup.center X) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨a, b, hab⟩ := hX.2.exists_pair_ne
  exact hab (Subsingleton.elim a b)

private theorem s16h_isSolvable_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    [Group.IsSolvable H] : Group.IsSolvable G :=
  Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_false_of_two_le_pRank [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) (h2 : 2 ≤ CFSG.Open.pRank 3 L) : False := by
  have h1 := hc.thin 3 Nat.prime_three (by norm_num)
  omega

private theorem s16h_pRank_eq_top_of_mulEquiv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {X : Type} [Group X] [Finite X] (e : ↥L ≃* X) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L).trans
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e)

private def s16h_diag2 {K : Type} [Field K] (A : GL (Fin 1 ⊕ Fin 1) K) : Prop :=
  (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inr 0) = 0 ∧
    (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inl 0) = 0

private def s16h_anti2 {K : Type} [Field K] (A : GL (Fin 1 ⊕ Fin 1) K) : Prop :=
  (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inl 0) = 0 ∧
    (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inr 0) = 0

private lemma s16h_diag2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hB : s16h_diag2 B) : s16h_diag2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_diag2_comm {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hB : s16h_diag2 B) : Commute A B := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  rw [Commute, SemiconjBy]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rcases i with i | i <;> fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2, mul_comm]

private lemma s16h_anti2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_anti2 A) (hB : s16h_anti2 B) : s16h_diag2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_diag2_anti2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hB : s16h_anti2 B) : s16h_anti2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_anti2_diag2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_anti2 A) (hB : s16h_diag2 B) : s16h_anti2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_isometry_quadPlus_one_class {K : Type} [Field K]
    (g : GL (Fin 1 ⊕ Fin 1) K) (hg : g ∈ orthGroup (StatedQuadPlus 1 K)) :
    s16h_diag2 g ∨ s16h_anti2 g := by
  have hquad : ∀ v : Fin 1 ⊕ Fin 1 → K,
      StatedQuadPlus 1 K v = v (Sum.inl 0) * v (Sum.inr 0) := by
    intro v
    simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_one]
  set p := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inl 0) with hp
  set q := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inr 0) with hq
  set r := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inl 0) with hr
  set s := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inr 0) with hs
  have h1 : p * r = 0 := by
    have h := orthGroup_preserves (StatedQuadPlus 1 K) hg (Pi.single (Sum.inl 0) 1)
    rw [hquad, hquad] at h
    simpa [Matrix.mulVec_single_one, hp, hr, Pi.single_apply] using h
  have h2 : q * s = 0 := by
    have h := orthGroup_preserves (StatedQuadPlus 1 K) hg (Pi.single (Sum.inr 0) 1)
    rw [hquad, hquad] at h
    simpa [Matrix.mulVec_single_one, hq, hs, Pi.single_apply] using h
  have h3 : (p + q) * (r + s) = 1 := by
    have h := orthGroup_preserves (StatedQuadPlus 1 K) hg
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
    rw [hquad, hquad] at h
    simp only [Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply, Matrix.col_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne (by simp : (Sum.inl 0 : Fin 1 ⊕ Fin 1) ≠ Sum.inr 0),
      add_zero, mul_one, zero_mul, hp, hq, hr, hs] at h
    simpa using h
  have h3' : p * s + q * r = 1 := by
    have e : (p + q) * (r + s) = p * s + q * r + (p * r + q * s) := by ring
    rw [e, h1, h2, add_zero] at h3
    simpa using h3
  by_cases hp0 : p = 0
  · right
    refine ⟨hp0, ?_⟩
    have hqr : q * r = 1 := by rw [hp0, zero_mul, zero_add] at h3'; exact h3'
    have hq0 : q ≠ 0 := by intro h0; rw [h0, zero_mul] at hqr; exact zero_ne_one hqr
    exact (mul_eq_zero.mp h2).resolve_left hq0
  · left
    have hr0 : r = 0 := (mul_eq_zero.mp h1).resolve_left hp0
    refine ⟨?_, hr0⟩
    have hps : p * s = 1 := by rw [hr0, mul_zero, add_zero] at h3'; exact h3'
    have hs0 : s ≠ 0 := by intro h0; rw [h0, mul_zero] at hps; exact zero_ne_one hps
    exact (mul_eq_zero.mp h2).resolve_right hs0

private lemma s16h_not_diag2_and_anti2 {K : Type} [Field K] {A : GL (Fin 1 ⊕ Fin 1) K}
    (h1 : s16h_diag2 A) (h2 : s16h_anti2 A) : False := by
  have hzero : (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) = 0 := by
    ext i j
    rcases i with i | i <;> fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
      simp [h1.1, h1.2, h2.1, h2.2]
  have h : ((A * A⁻¹ : GL (Fin 1 ⊕ Fin 1) K) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) =
      ((1 : GL (Fin 1 ⊕ Fin 1) K) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) :=
    congrArg Units.val (mul_inv_cancel A)
  rw [Units.val_mul, hzero, zero_mul, Units.val_one] at h
  exact zero_ne_one h

private lemma s16h_diag2_inv {K : Type} [Field K] {A : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hAis : A ∈ orthGroup (StatedQuadPlus 1 K)) :
    s16h_diag2 A⁻¹ := by
  rcases s16h_isometry_quadPlus_one_class A⁻¹ (inv_mem hAis) with h | h
  · exact h
  · exfalso
    have h' := s16h_anti2_diag2_mul h hA
    rw [inv_mul_cancel] at h'
    exact s16h_not_diag2_and_anti2 (by simp [s16h_diag2]) h'

private lemma s16h_anti2_inv {K : Type} [Field K] {A : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_anti2 A) (hAis : A ∈ orthGroup (StatedQuadPlus 1 K)) :
    s16h_anti2 A⁻¹ := by
  rcases s16h_isometry_quadPlus_one_class A⁻¹ (inv_mem hAis) with h | h
  · exfalso
    have h' := s16h_diag2_anti2_mul h hA
    rw [inv_mul_cancel] at h'
    exact s16h_not_diag2_and_anti2 (by simp [s16h_diag2]) h'
  · exact h

private lemma s16h_diag2_commutator {K : Type} [Field K] {g h : GL (Fin 1 ⊕ Fin 1) K}
    (hg : g ∈ orthGroup (StatedQuadPlus 1 K)) (hh : h ∈ orthGroup (StatedQuadPlus 1 K)) :
    s16h_diag2 ⁅g, h⁆ := by
  have dg := s16h_isometry_quadPlus_one_class g hg
  have dh := s16h_isometry_quadPlus_one_class h hh
  rw [commutatorElement_def]
  rcases dg with dg | dg <;> rcases dh with dh | dh
  · exact s16h_diag2_mul (s16h_diag2_mul (s16h_diag2_mul dg dh)
      (s16h_diag2_inv dg hg)) (s16h_diag2_inv dh hh)
  · exact s16h_anti2_mul (s16h_anti2_diag2_mul (s16h_diag2_anti2_mul dg dh)
      (s16h_diag2_inv dg hg)) (s16h_anti2_inv dh hh)
  · exact s16h_diag2_mul (s16h_anti2_mul (s16h_anti2_diag2_mul dg dh)
      (s16h_anti2_inv dg hg)) (s16h_diag2_inv dh hh)
  · exact s16h_anti2_mul (s16h_diag2_anti2_mul (s16h_anti2_mul dg dh)
      (s16h_anti2_inv dg hg)) (s16h_anti2_inv dh hh)

private lemma s16h_isMulCommutative_statedOmega_quadPlus_one {K : Type} [Field K] :
    IsMulCommutative ↥(StatedOmega (StatedQuadPlus 1 K)) := by
  have hC : ({g : GL (Fin 1 ⊕ Fin 1) K |
      ∃ g₁ ∈ orthGroup (StatedQuadPlus 1 K),
        ∃ g₂ ∈ orthGroup (StatedQuadPlus 1 K), ⁅g₁, g₂⁆ = g}).Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := ha
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hb
    exact s16h_diag2_comm (s16h_diag2_commutator hg₁ hg₂) (s16h_diag2_commutator hh₁ hh₂)
  exact Subgroup.isMulCommutative_closure hC

private theorem s16h_isMulCommutative_statedOmega_quadPlus_le_one {K : Type} [Field K]
    {m : ℕ} (hm : m ≤ 1) : IsMulCommutative ↥(StatedOmega (StatedQuadPlus m K)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with h0 | h1
  · rw [h0]
    haveI : Subsingleton (GL (Fin 0 ⊕ Fin 0) K) :=
      Subsingleton.units_of_isUnit fun a _ => Subsingleton.elim a 1
    exact IsMulCommutative.of_comm fun x y => Subsingleton.elim _ _
  · rw [h1]
    exact s16h_isMulCommutative_statedOmega_quadPlus_one

private theorem s16h_isMulCommutative_statedProj_quadPlus_le_one {K : Type} [Field K]
    {m : ℕ} (hm : m ≤ 1) :
    IsMulCommutative (StatedProj (StatedOmega (StatedQuadPlus m K))) := by
  haveI hΩ : IsMulCommutative ↥(StatedOmega (StatedQuadPlus m K)) :=
    s16h_isMulCommutative_statedOmega_quadPlus_le_one hm
  refine IsMulCommutative.of_comm fun x y => ?_
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
  exact congrArg (QuotientGroup.mk' _) (mul_comm' x' y')

private theorem s16h_false_of_isOmegaPlus_le_one {X : Type} [Group X]
    (hq : CFSG.Open.IsQuasisimple X) {K : Type} [Field K] {m : ℕ} (hm : m ≤ 1)
    (e : X ≃* StatedProj (StatedOmega (StatedQuadPlus m K))) : False := by
  haveI : IsMulCommutative (StatedProj (StatedOmega (StatedQuadPlus m K))) :=
    s16h_isMulCommutative_statedProj_quadPlus_le_one hm
  refine s16h_not_isMulCommutative_of_isQuasisimple hq ?_
  exact IsMulCommutative.of_comm fun x y => e.injective (by
    rw [map_mul, map_mul]
    exact mul_comm' (e x) (e y))

private theorem s16h_not_isSolvable_of_isQuasisimple {Q : Type} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hs
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at h
  exact lt_irrefl _ h

private theorem s16h_card_GL_fin_le_six {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {d : ℕ} (hd : d ≤ 2) : Nat.card (GL (Fin d) K) < 60 := by
  rw [Matrix.card_GL_field]
  interval_cases d <;> simp_all <;> norm_num

private theorem s16h_card_GL_le_six {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Fintype K] (hK : Fintype.card K = 2) (hι : Fintype.card ι ≤ 2) :
    Nat.card (GL ι K) < 60 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h := Nat.card_congr (Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv).toEquiv
  rw [h]
  exact s16h_card_GL_fin_le_six hK hι

private theorem s16h_isSolvable_GL_of_card_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2) :
    Group.IsSolvable (GL ι K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact CFSG.GroupTheory.groups_order_below_sixty_solvable (s16h_card_GL_le_six hK' hι)

private theorem s16h_isSolvable_subgroup_GL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2)
    (H : Subgroup (GL ι K)) : Group.IsSolvable ↥H :=
  haveI := s16h_isSolvable_GL_of_card_le_two hK hι
  Group.isSolvable_of_isSolvable_injective (f := H.subtype) H.subtype_injective

private theorem s16h_isSolvable_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2)
    (H : Subgroup (GL ι K)) : Group.IsSolvable (StatedProj H) :=
  haveI := s16h_isSolvable_subgroup_GL hK hι H
  Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective ((StatedScalars ι K).subgroupOf H))

private theorem s16h_isSolvable_orthGroup_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(orthGroup (StatedQuadPlus 2 K)) := by
  have hcard : Nat.card ↥(orthGroup (StatedQuadPlus 2 K)) = 2 ^ 3 * 3 ^ 2 := by
    rw [card_orthGroup_quadPlus_two, hK]
    norm_num
  haveI : Fintype ↥(orthGroup (StatedQuadPlus 2 K)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

private theorem s16h_isSolvable_statedOmega_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) :=
  haveI := s16h_isSolvable_orthGroup_quadPlus_two hK
  Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (statedOmega_le_orthGroup (StatedQuadPlus 2 K)))
    (Subgroup.inclusion_injective _)

private theorem s16h_isSolvable_statedProj_statedOmega_quadPlus_two {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
  haveI := s16h_isSolvable_statedOmega_quadPlus_two hK
  Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadPlus 2 K))))

theorem s16h_H5_isOmegaPlus_class [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {n a : ℕ} (h : IsOmegaPlus ↥L n a) : False := by
  classical
  have hcopy : IsOmegaPlus ↥L n a := h
  obtain ⟨hEven, K, hF, hFin, hKcard, ⟨e⟩⟩ := hcopy
  letI := hF
  letI := hFin
  have hq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  haveI : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hq
  by_cases hm1 : n / 2 ≤ 1
  · exact s16h_false_of_isOmegaPlus_le_one hq hm1 e
  · have hm2 : 2 ≤ n / 2 := by omega
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have ha1 : a = 1 := by
        rcases Nat.eq_zero_or_pos a with h0 | hpos
        · exfalso
          have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
          rw [h0, pow_zero] at hKcard
          omega
        · omega
      have hK2 : Nat.card K = 2 := by rw [ha1] at hKcard; simpa using hKcard
      rcases Nat.lt_or_ge (n / 2) 3 with hm3 | hm3
      · have hm_eq : n / 2 = 2 := by omega
        haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) := by
          rw [hm_eq]
          exact s16h_isSolvable_statedProj_statedOmega_quadPlus_two hK2
        haveI : Group.IsSolvable ↥L := s16h_isSolvable_of_mulEquiv e
        exact (Group.IsPerfect.not_isSolvable ↥L) inferInstance
      · rcases Nat.lt_or_ge (n / 2) 4 with hm4 | hm4
        · have hm_eq3 : n / 2 = 3 := by omega
          have hn6 : n = 6 := by
            have h2 : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hEven
            omega
          have h61 : IsOmegaPlus ↥L 6 1 := by
            have h' := h
            rw [hn6, ha1] at h'
            exact h'
          obtain ⟨e8⟩ := s15k_omp6_isAlt8 (X := ↥L) h61
          have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
            rw [s16h_pRank_eq_top_of_mulEquiv e8]
            exact CFSG.Quasithin.A3Facts.two_le_pRank_alternating (n := 8) (by norm_num)
          exact s16h_false_of_two_le_pRank hc h2
        · haveI : CharP K 2 := by
            haveI : Fintype K := Fintype.ofFinite K
            exact charP_of_card_eq_prime_pow (p := 2) (f := a) (by
              rw [← Nat.card_eq_fintype_card]; exact hKcard)
          have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
            rw [s16h_pRank_eq_top_of_mulEquiv e]
            exact (by norm_num : 2 ≤ 3).trans
              (CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three
                (K := K) (n := n / 2) hm4)
          exact s16h_false_of_two_le_pRank hc h2
    · haveI : Fintype K := Fintype.ofFinite K
      haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := a) (by
        rw [← Nat.card_eq_fintype_card]; exact hKcard)
      have h4 : 4 ≤ Fintype.card K := by
        rw [← Nat.card_eq_fintype_card, hKcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
      obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
        by_contra hcon
        rw [not_exists] at hcon
        have hsub : (Finset.univ : Finset K) ⊆ ({0, 1} : Finset K) := by
          intro x _
          rw [Finset.mem_insert, Finset.mem_singleton]
          by_cases h0 : x = 0
          · exact Or.inl h0
          · exact Or.inr (by by_contra h1; exact hcon x ⟨h0, h1⟩)
        have hle : Fintype.card K ≤ 2 := by
          have := Finset.card_le_card hsub
          rwa [Finset.card_univ, Finset.card_insert_of_notMem (by simp),
            Finset.card_singleton] at this
        omega
      have hcsq : c ^ 2 ≠ 1 := by
        intro hsq
        rw [sq_eq_one_iff] at hsq
        rcases hsq with h1 | h1
        · exact hc1 h1
        · exact hc1 (h1.trans (CharTwo.neg_eq (1 : K)))
      have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
        rw [s16h_pRank_eq_top_of_mulEquiv e]
        exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.two_le_pRank_plus
          (K := K) (n := n / 2) hm2 hc0 hcsq
      exact s16h_false_of_two_le_pRank hc h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
