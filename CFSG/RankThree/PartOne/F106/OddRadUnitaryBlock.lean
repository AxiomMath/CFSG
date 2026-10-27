module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.RankThree.PartOne.F106.OddRadUnitary

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial Polynomial
open scoped commutatorElement

universe u

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}
  {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

@[expose] noncomputable def MS (B : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) : Subgroup (LinearMap.GeneralLinearGroup K V) :=
  unitaryCentralizer B x ⊓ sesqSpecialUnitaryGroup B

theorem finite_gl (hK : UnitaryFieldData 2 f K) : Finite (LinearMap.GeneralLinearGroup K V) := by
  have := hK.finite
  have : Finite V := Module.finite_of_finite K
  have : Finite (Module.End K V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[K] V))
  exact Finite.of_injective _ Units.val_injective

theorem specialBlockFacts_of_mult_le_one (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V))
    (hm : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1) : SpecialBlockFacts B x a := by
  have hq : 2 ≤ 2 ^ f := by
    have := Nat.one_lt_two_pow (n := f) (by have := hK.one_le; omega)
    omega
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
      (fun h2 => absurd hm (by omega))
  · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))

theorem isSolvable_orbitFactor_of_not_good (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : ¬ IsGoodBlock hK x a) :
    Group.IsSolvable ↥(orbitFactor B x (a : K[X])) := by
  have := finite_gl (V := V) hK
  by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
  · have hself : dualPoly hK.bar (a : K[X]) = a := by
      by_contra hne
      exact ha ⟨hm, fun h => absurd h hne⟩
    have hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
        2 ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
      by_contra hnot
      exact ha ⟨hm, fun _ => hnot⟩
    obtain ⟨h1, h2, h3⟩ := card_orbitFactor_exceptional H a hself
    apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hbad
    rcases hbad with ⟨hm', hQ⟩ | ⟨hm', hQ⟩ | ⟨hm', hQ⟩
    · rw [h1 hm' hQ, show (18 : ℕ) = 2 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three,
        Nat.Prime.primeFactors Nat.prime_two]
      decide
    · rw [h2 hm' hQ, show (96 : ℕ) = 2 ^ 5 * 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      decide
    · rw [h3 hm' hQ, show (648 : ℕ) = 2 ^ 3 * 3 ^ 4 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide
  · have hm1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 := by omega
    have hS := (specialBlockFacts_of_mult_le_one H a hm1).abelian hm1
    exact Group.isSolvable_of_comm fun g g' => Subtype.ext (hS g g.2 g' g'.2).eq

omit [FiniteDimensional K V] in
theorem MS_le_unitaryCentralizer : MS B x ≤ unitaryCentralizer B x := inf_le_left

omit [FiniteDimensional K V] in
theorem MS_le_gl_centralizer : MS B x ≤ gl_centralizer x := fun _ hg => hg.1.2

@[expose] noncomputable def restrictMS (B : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) (a : K[X]) :
    ↥(MS B x) →* blockGL (x : Module.End K V) a :=
  (blockRestrict x a).comp (Subgroup.inclusion MS_le_gl_centralizer)

omit [FiniteDimensional K V] in
theorem blockApply_restrictMS (a : K[X]) (g : ↥(MS B x)) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) a) :
    blockApply (restrictMS B x a g) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
  rfl

theorem isSolvable_range_restrictMS_of_not_good (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : ¬ IsGoodBlock hK x a) :
    Group.IsSolvable ↥(restrictMS B x (a : K[X])).range := by
  have hsolv := isSolvable_orbitFactor_of_not_good H a ha
  let κ : ↥(orbitFactor B x (a : K[X])) →* blockGL (x : Module.End K V) (a : K[X]) :=
    (blockRestrict x (a : K[X])).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)
  have hκ : Group.IsSolvable ↥κ.range :=
    Group.isSolvable_of_surjective (f := κ.rangeRestrict) κ.rangeRestrict_surjective
  have hle : (restrictMS B x (a : K[X])).range ≤ κ.range := by
    rintro _ ⟨g, rfl⟩
    have hO : ∀ b ∈ primaryFactors (x : Module.End K V),
        b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) →
          dualPoly hK.bar b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) := by
      intro b hb hbO
      rcases hbO with rfl | hbO
      · exact Or.inr rfl
      · rw [Set.mem_singleton_iff] at hbO
        subst hbO
        exact Or.inl (dualPoly_dualPoly_of_mem H a.2)
    obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO (MS_le_unitaryCentralizer g.2)
    refine ⟨⟨gO, hgO⟩, ?_⟩
    refine blockGL_ext fun v hv => ?_
    change ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
    exact hgOeq (a : K[X]) a.2 (Or.inl rfl) v hv
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem apply_eq_of_mem_perfectResidual_of_not_good (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : ¬ IsGoodBlock hK x a)
    {r : ↥(MS B x)} (hr : r ∈ perfectResidual ↥(MS B x)) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])) :
    ((r : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
  have := finite_gl (V := V) hK
  have hs := isSolvable_range_restrictMS_of_not_good H a ha
  set φ := restrictMS B x (a : K[X]) with hφ
  have hfin : Finite ↥φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h1 := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq φ.rangeRestrict
    φ.rangeRestrict_surjective
  have h2 : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥φ.range = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mpr hs
  have h3 : φ.rangeRestrict r ∈
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(MS B x)).map φ.rangeRestrict :=
    Subgroup.mem_map_of_mem _ hr
  rw [h1, h2, Subgroup.mem_bot] at h3
  have h4 : φ r = 1 := congrArg Subtype.val h3
  have h5 := blockApply_restrictMS (B := B) (x := x) (a : K[X]) r v hv
  rw [← hφ, h4, blockApply_one] at h5
  exact h5.symm

@[expose] noncomputable def RadMS (B : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) : Subgroup ↥(MS B x) :=
  (solvableRadical ↥(perfectResidual ↥(MS B x))).map (perfectResidual ↥(MS B x)).subtype

theorem RadMS_isSolvable : Group.IsSolvable ↥(RadMS B x) := by
  have := finite_gl (V := V) hK
  have h1 : Group.IsSolvable ↥(solvableRadical ↥(perfectResidual ↥(MS B x))) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  exact Group.isSolvable_of_surjective
    (MonoidHom.subgroupMap_surjective (perfectResidual ↥(MS B x)).subtype _)

theorem RadMS_isSubnormal : (RadMS B x).IsSubnormal := by
  have := finite_gl (V := V) hK
  have h1 : (solvableRadical ↥(perfectResidual ↥(MS B x))).Normal :=
    CFSG.ABGLocalTools.solvableRadical_normal
  exact h1.isSubnormal.trans' (inferInstance : (perfectResidual ↥(MS B x)).Normal).isSubnormal

theorem commute_of_mem_RadMS_good (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {r : ↥(MS B x)} (hr : r ∈ RadMS B x) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ specialBlock B x (a : K[X])) :
    Commute (r : LinearMap.GeneralLinearGroup K V) g := by
  have := finite_gl (V := V) hK
  have hq : 2 ≤ 2 ^ f := by
    have := Nat.one_lt_two_pow (n := f) (by have := hK.one_le; omega)
    omega
  have hle : specialBlock B x (a : K[X]) ≤ MS B x :=
    le_inf specialBlock_le_unitaryCentralizer
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a ha)
  have hQ : CFSG.IsQuasisimple ↥((specialBlock B x (a : K[X])).subgroupOf (MS B x)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
      ((specialBlockFacts_of_good H hq a ha).quasisimple ha.1)
  have hN : ((specialBlock B x (a : K[X])).subgroupOf (MS B x)).Normal := by
    refine ⟨fun n hn g' => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_specialBlock (MS_le_unitaryCentralizer g'.2) hn
    simpa using this
  have hcomp : CFSG.IsComponent ((specialBlock B x (a : K[X])).subgroupOf (MS B x)) :=
    ⟨hQ, hN.isSubnormal⟩
  have hcen := (CFSG.LocalCores.component_solvable_centralizer
    (RadMS_isSolvable (B := B) (x := x)) (RadMS_isSubnormal (B := B) (x := x))).1 _ hcomp
  have hmem : ⁅(⟨g, hle hg⟩ : ↥(MS B x)), r⁆ ∈
      ⁅(specialBlock B x (a : K[X])).subgroupOf (MS B x), RadMS B x⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hg) hr
  rw [hcen, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
  have h := congrArg (fun y : ↥(MS B x) => ((y : LinearMap.GeneralLinearGroup K V))) hmem.eq
  exact h.symm

theorem apply_eq_of_mem_RadMS_good (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {r : ↥(MS B x)} (hr : r ∈ RadMS B x) (hr2 : r ^ 2 = 1) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])) :
    ((r : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
  have hq : 2 ≤ 2 ^ f := by
    have := Nat.one_lt_two_pow (n := f) (by have := hK.one_le; omega)
    omega
  obtain ⟨c, hc⟩ := (specialBlockFacts_of_good H hq a ha).scalar
    (r : LinearMap.GeneralLinearGroup K V) (MS_le_unitaryCentralizer r.2)
    (fun _ g hg => commute_of_mem_RadMS_good H a ha hr hg)
  have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  have hK2 : CharP K 2 := hK.charP
  have hchar : CharP (AdjoinRoot (a : K[X])) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a : K[X]))).injective 2
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot H.squarefree a.2)
  have hrr : ((r : LinearMap.GeneralLinearGroup K V) : Module.End K V) *
      ((r : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 := by
    have h1 : (r : LinearMap.GeneralLinearGroup K V) ^ 2 = 1 := by
      have := congrArg Subtype.val hr2
      simpa using this
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K V => (g : Module.End K V)) h1
    simpa [pow_two] using h2
  have hw1 := hc ⟨w, hw⟩
  have hw2 := hc (c • ⟨w, hw⟩)
  have hcw : (c • c • (⟨w, hw⟩ : primaryComponent (x : Module.End K V) (a : K[X]))) =
      ⟨w, hw⟩ := by
    apply Subtype.ext
    have h3 : (((r : LinearMap.GeneralLinearGroup K V) : Module.End K V) *
        ((r : LinearMap.GeneralLinearGroup K V) : Module.End K V)) w = w := by
      rw [hrr]; rfl
    rw [Module.End.mul_apply] at h3
    change ((r : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      (((r : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) = w at h3
    rw [hw1] at h3
    rw [hw2] at h3
    exact h3
  have hcc : c * c = 1 := by
    have h4 : (c * c - 1) • (⟨w, hw⟩ : primaryComponent (x : Module.End K V) (a : K[X])) = 0 := by
      rw [sub_smul, mul_smul, hcw, one_smul, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd (by simpa using congrArg Subtype.val h5) hw0
  have hc1 : c = 1 := by
    have h2 : (2 : AdjoinRoot (a : K[X])) = 0 := CharP.cast_eq_zero _ 2
    have h6 : (c - 1) ^ 2 = 0 := by linear_combination hcc + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp h6)
  have := hc ⟨v, hv⟩
  rw [hc1, one_smul] at this
  exact this

theorem odd_card_radical_perfectResidual_MS (H : UnitaryPrimaryData hK.bar B x) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(MS B x)))) := by
  have := finite_gl (V := V) hK
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(solvableRadical ↥(perfectResidual ↥(MS B x))) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r0, hr0⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set r : ↥(MS B x) := ((r0 : ↥(perfectResidual ↥(MS B x))) : ↥(MS B x)) with hrdef
  have hrR : r ∈ RadMS B x := ⟨(r0 : ↥(perfectResidual ↥(MS B x))), r0.2, rfl⟩
  have hrY : r ∈ perfectResidual ↥(MS B x) := (r0 : ↥(perfectResidual ↥(MS B x))).2
  have hr02 : r0 ^ 2 = 1 := by rw [← hr0]; exact pow_orderOf_eq_one r0
  have hr2 : r ^ 2 = 1 := by
    have := congrArg (fun y : ↥(solvableRadical ↥(perfectResidual ↥(MS B x))) =>
      (((y : ↥(perfectResidual ↥(MS B x))) : ↥(MS B x)))) hr02
    simpa using this
  have hr1 : r = 1 := by
    apply Subtype.ext
    refine eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => ?_
    by_cases hgood : IsGoodBlock hK x ⟨b, hb⟩
    · exact apply_eq_of_mem_RadMS_good H ⟨b, hb⟩ hgood hrR hr2 v hv
    · exact apply_eq_of_mem_perfectResidual_of_not_good H ⟨b, hb⟩ hgood hrY v hv
  have hr01 : r0 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hr1
  rw [hr01, orderOf_one] at hr0
  norm_num at hr0

end CFSG.RankThree.PartOne.F106.OddRadUnitary
