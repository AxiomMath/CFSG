module

public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryPairing
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.Classical

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary (coeff_zero_ne_zero_of_mem_primaryFactors
  eq_sum_primaryProjection finrank_le_of_forall_eq_zero injective_unit)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial natDegree_reciprocalPolynomial
  monic_reciprocalPolynomial reciprocalPolynomial_reciprocalPolynomial
  irreducible_reciprocalPolynomial aeval_reciprocalPolynomial_of_unit)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Adjoint

variable {B : LinearMap.BilinForm K V} {X Y : Module.End K V}

theorem bilin_apply_left_eq (hXY : X * Y = 1) (hB : ∀ u v, B (X u) (X v) = B u v) (u v : V) :
    B (X u) v = B u (Y v) := by
  conv_lhs => rw [show v = X (Y v) by rw [← Module.End.mul_apply, hXY, Module.End.one_apply]]
  exact hB u (Y v)

theorem bilin_pow_left (hXY : X * Y = 1) (hB : ∀ u v, B (X u) (X v) = B u v) (n : ℕ) (u v : V) :
    B ((X ^ n) u) v = B u ((Y ^ n) v) := by
  induction n generalizing u v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, bilin_apply_left_eq hXY hB, ih, pow_succ,
      Module.End.mul_apply]

theorem bilin_aeval_left (hXY : X * Y = 1) (hB : ∀ u v, B (X u) (X v) = B u v) (f : K[X])
    (u v : V) : B (aeval X f u) v = B u (aeval Y f v) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
      LinearMap.add_apply, hf, hg, map_add]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smul₂,
      LinearMap.map_smul, bilin_pow_left hXY hB]

end Adjoint

theorem mem_primaryComponent_reciprocal_iff (x : LinearMap.GeneralLinearGroup K V) {h : K[X]}
    (h0 : h.coeff 0 ≠ 0) {v : V} :
    v ∈ primaryComponent (x : Module.End K V) (reciprocalPolynomial h) ↔
      aeval ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) h v = 0 := by
  rw [mem_primaryComponent, aeval_reciprocalPolynomial_of_unit x h]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, smul_eq_zero, inv_eq_zero, h0,
    false_or]
  have hinj : Function.Injective ((x : Module.End K V) ^ h.natDegree) := by
    rw [Module.End.coe_pow]
    exact Function.Injective.iterate (injective_unit x) h.natDegree
  exact map_eq_zero_iff _ hinj

theorem reciprocalPolynomial_X_sub_one : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := by
  have h1 : (X - 1 : K[X]).coeff 0 = -1 := by simp
  have hX : (X : K[X]).reverse = 1 := by
    rw [show (X : K[X]) = C 1 * X by rw [C_1, one_mul], reverse_mul_X, reverse_C, C_1]
  have h2 : (X - 1 : K[X]).reverse = 1 - X := by
    rw [show (X - 1 : K[X]) = X + C (-1) by rw [C_neg, C_1, sub_eq_add_neg], reverse_add_C,
      hX, natDegree_X, pow_one, C_neg, C_1]
    ring
  rw [reciprocalPolynomial, h1, h2, inv_neg, inv_one, C_neg, C_1]
  ring

structure AltPrimaryData (B : LinearMap.BilinForm K V) (x : LinearMap.GeneralLinearGroup K V) :
    Prop where
  alt : B.IsAlt
  sep : ∀ v, (∀ w, B v w = 0) → v = 0
  isom : x ∈ sesqUnitaryGroup B
  squarefree : Squarefree (minpoly K (x : Module.End K V))

namespace AltPrimaryData

variable [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
  {x : LinearMap.GeneralLinearGroup K V} (H : AltPrimaryData B x)
include H

omit [FiniteDimensional K V] in
theorem skew (u v : V) : B v u = -B u v :=
  (H.alt.neg_eq u v).symm

omit [FiniteDimensional K V] in
theorem sep_right {w : V} (h : ∀ v, B v w = 0) : w = 0 :=
  H.sep w fun v => by rw [H.skew, h, neg_zero]

omit [FiniteDimensional K V] in
theorem nondegenerate : B.Nondegenerate := ⟨H.sep, fun _ hw => H.sep_right hw⟩

omit [FiniteDimensional K V] in
theorem isom_apply (u v : V) :
    B ((x : Module.End K V) u) ((x : Module.End K V) v) = B u v :=
  mem_sesqUnitaryGroup.mp H.isom u v

@[expose] noncomputable def adj (r : Module.End K V) : Module.End K V :=
  B.leftAdjointOfNondegenerate H.nondegenerate r

theorem adj_spec' (r : Module.End K V) (v w : V) : B (H.adj r v) w = B v (r w) :=
  LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate B H.nondegenerate r v w

theorem adj_spec (r : Module.End K V) (v w : V) : B (r v) w = B v (H.adj r w) := by
  rw [H.skew (H.adj r w) v, H.adj_spec', H.skew (r v) w, neg_neg]

theorem adj_unique {r s : Module.End K V} (h : ∀ v w, B (r v) w = B v (s w)) : H.adj r = s := by
  ext w
  refine sub_eq_zero.mp (H.sep_right fun v => ?_)
  rw [map_sub, ← H.adj_spec, h, sub_self]

theorem adj_mul (r s : Module.End K V) : H.adj (r * s) = H.adj s * H.adj r :=
  H.adj_unique fun v w => by
    rw [Module.End.mul_apply, H.adj_spec, H.adj_spec, Module.End.mul_apply]

theorem adj_one : H.adj 1 = 1 :=
  H.adj_unique fun _ _ => rfl

theorem adj_adj (r : Module.End K V) : H.adj (H.adj r) = r :=
  H.adj_unique fun v w => H.adj_spec' r v w

theorem adj_x : H.adj (x : Module.End K V) =
    ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) :=
  H.adj_unique fun v w => bilin_apply_left_eq (Units.mul_inv x) H.isom_apply v w

theorem adj_aeval (f : K[X]) : H.adj (aeval (x : Module.End K V) f) =
    aeval ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) f :=
  H.adj_unique fun v w => bilin_aeval_left (Units.mul_inv x) H.isom_apply f v w

theorem adj_commute {r : Module.End K V} (hr : Commute r (x : Module.End K V)) :
    Commute (H.adj r) (x : Module.End K V) := by
  set X : Module.End K V := (x : Module.End K V) with hX
  set Y : Module.End K V := ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
  have hXY : X * Y = 1 := Units.mul_inv x
  have hYX : Y * X = 1 := Units.inv_mul x
  have h1 : H.adj (r * X) = H.adj (X * r) := by rw [hr.eq]
  rw [H.adj_mul, H.adj_mul, H.adj_x] at h1
  change Y * H.adj r = H.adj r * Y at h1
  calc H.adj r * X = X * (Y * H.adj r) * X := by rw [← mul_assoc, hXY, one_mul]
    _ = X * (H.adj r * Y) * X := by rw [h1]
    _ = X * H.adj r := by rw [mul_assoc, mul_assoc, hYX, mul_one]

theorem adj_mem_commutant {r : Module.End K V} (hr : r ∈ commutant (x : Module.End K V)) :
    H.adj r ∈ commutant (x : Module.End K V) :=
  (mem_commutant _).mpr (H.adj_commute ((mem_commutant _).mp hr))

theorem adj_mul_self_eq_one_iff (g : LinearMap.GeneralLinearGroup K V) :
    H.adj (g : Module.End K V) * (g : Module.End K V) = 1 ↔ g ∈ sesqUnitaryGroup B := by
  rw [mem_sesqUnitaryGroup]
  constructor
  · intro h u v
    rw [H.adj_spec, ← Module.End.mul_apply, h, Module.End.one_apply]
  · intro h
    have hg : H.adj (g : Module.End K V) =
        ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) :=
      H.adj_unique fun v w => bilin_apply_left_eq (Units.mul_inv g) h v w
    rw [hg]
    exact Units.inv_mul g

theorem coeff_zero_ne {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    a.coeff 0 ≠ 0 :=
  coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha

theorem orthogonal_of_ne {a b : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hb : b ∈ primaryFactors (x : Module.End K V)) (hab : b ≠ reciprocalPolynomial a) {v w : V}
    (hv : v ∈ primaryComponent (x : Module.End K V) a)
    (hw : w ∈ primaryComponent (x : Module.End K V) b) : B v w = 0 := by
  have h0 := H.coeff_zero_ne ha
  have hai := irreducible_of_mem_primaryFactors ha
  have hbi := irreducible_of_mem_primaryFactors hb
  set X : Module.End K V := (x : Module.End K V) with hX
  set Y : Module.End K V := ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hY
  have hXY : Commute X Y := by
    rw [Commute, SemiconjBy, hX, hY, Units.mul_inv, Units.inv_mul]
  set T : Module.End K V := aeval Y a with hT
  have hcomm : Commute T X := (commute_aeval hXY a).symm
  have hmaps : ∀ u ∈ primaryComponent X b, T u ∈ primaryComponent X b :=
    fun u hu => apply_mem_primaryComponent hcomm hu
  let Tb : primaryComponent X b →ₗ[K] primaryComponent X b := T.restrict hmaps
  have hinj : Function.Injective Tb := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hTu : T (u : V) = 0 := congrArg Subtype.val hu
    have hu' : (u : V) ∈ primaryComponent X (reciprocalPolynomial a) :=
      (mem_primaryComponent_reciprocal_iff x h0).mpr hTu
    have hcop : IsCoprime b (reciprocalPolynomial a) := by
      rw [hbi.coprime_iff_not_dvd]
      intro hd
      exact hab (eq_of_monic_of_associated (monic_of_mem_primaryFactors hb)
        (monic_reciprocalPolynomial h0)
        (hbi.associated_of_dvd (irreducible_reciprocalPolynomial hai h0) hd))
    have hdisj := Polynomial.disjoint_ker_aeval_of_isCoprime X hcop
    exact Subtype.ext (Submodule.disjoint_def.mp hdisj u u.2 hu')
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  have hu' : T (u : V) = w := congrArg Subtype.val hu
  rw [← hu', hT, ← bilin_aeval_left (Units.mul_inv x) H.isom_apply a v u,
    mem_primaryComponent.mp hv, map_zero, LinearMap.zero_apply]

theorem eq_zero_of_forall {v : V}
    (h : ∀ k ∈ primaryFactors (x : Module.End K V),
      ∀ w ∈ primaryComponent (x : Module.End K V) k, B v w = 0) : v = 0 :=
  H.sep v fun w => by
    rw [eq_sum_primaryProjection H.squarefree w, map_sum]
    exact Finset.sum_eq_zero fun k hk => h k hk _ (primaryProjection_mem H.squarefree hk w)

theorem eq_zero_of_forall' {w : V}
    (h : ∀ k ∈ primaryFactors (x : Module.End K V),
      ∀ u ∈ primaryComponent (x : Module.End K V) k, B u w = 0) : w = 0 :=
  H.sep_right fun u => by
    rw [eq_sum_primaryProjection H.squarefree u, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun k hk => h k hk _ (primaryProjection_mem H.squarefree hk u)

theorem reciprocal_mem {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    reciprocalPolynomial a ∈ primaryFactors (x : Module.End K V) := by
  by_contra hnot
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot H.squarefree ha)
  exact hv0 (H.eq_zero_of_forall fun k hk w hw =>
    H.orthogonal_of_ne ha hk (fun h => hnot (h ▸ hk)) hv hw)

theorem reciprocal_reciprocal {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    reciprocalPolynomial (reciprocalPolynomial a) = a :=
  reciprocalPolynomial_reciprocalPolynomial (monic_of_mem_primaryFactors ha) (H.coeff_zero_ne ha)

theorem reciprocal_injOn :
    Set.InjOn reciprocalPolynomial (primaryFactors (x : Module.End K V) : Set K[X]) :=
  fun a ha b hb h => by rw [← H.reciprocal_reciprocal ha, h, H.reciprocal_reciprocal hb]

theorem bijOn_reciprocal :
    Set.BijOn reciprocalPolynomial (primaryFactors (x : Module.End K V) : Set K[X])
      (primaryFactors (x : Module.End K V) : Set K[X]) :=
  ⟨fun _ ha => H.reciprocal_mem ha, H.reciprocal_injOn,
    fun _ ha => ⟨_, H.reciprocal_mem ha, H.reciprocal_reciprocal ha⟩⟩

theorem B_eq_sum (v w : V) :
    B v w = ∑ b ∈ primaryFactors (x : Module.End K V),
      B (primaryProjection (x : Module.End K V) b v)
        (primaryProjection (x : Module.End K V) (reciprocalPolynomial b) w) := by
  have hsq := H.squarefree
  have h1 : B v w = ∑ b ∈ primaryFactors (x : Module.End K V),
      B (primaryProjection (x : Module.End K V) b v) w := by
    conv_lhs => rw [eq_sum_primaryProjection hsq v]
    rw [map_sum, LinearMap.sum_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun b hb => ?_
  conv_lhs => rw [eq_sum_primaryProjection hsq w]
  rw [map_sum, Finset.sum_eq_single (reciprocalPolynomial b)]
  · intro c hc hcb
    exact H.orthogonal_of_ne hb hc hcb (primaryProjection_mem hsq hb v)
      (primaryProjection_mem hsq hc w)
  · intro h
    exact absurd (H.reciprocal_mem hb) h

theorem eq_zero_of_perfect_left {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    {v : V} (hv : v ∈ primaryComponent (x : Module.End K V) a)
    (h : ∀ w ∈ primaryComponent (x : Module.End K V) (reciprocalPolynomial a), B v w = 0) :
    v = 0 := by
  refine H.eq_zero_of_forall fun k hk w hw => ?_
  by_cases hka : k = reciprocalPolynomial a
  · subst hka
    exact h w hw
  · exact H.orthogonal_of_ne ha hk hka hv hw

theorem eq_zero_of_perfect_right {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    {w : V} (hw : w ∈ primaryComponent (x : Module.End K V) (reciprocalPolynomial a))
    (h : ∀ v ∈ primaryComponent (x : Module.End K V) a, B v w = 0) : w = 0 := by
  refine H.eq_zero_of_forall' fun k hk u hu => ?_
  by_cases hka : k = a
  · subst hka
    exact h u hu
  · exact H.orthogonal_of_ne hk (H.reciprocal_mem ha)
      (fun h' => hka (H.reciprocal_injOn hk ha h'.symm)) hu hw

theorem finrank_reciprocal {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    finrank K (primaryComponent (x : Module.End K V) (reciprocalPolynomial a)) =
      finrank K (primaryComponent (x : Module.End K V) a) :=
  le_antisymm
    (finrank_le_of_forall_eq_zero (B := B) fun _ hw h => H.eq_zero_of_perfect_right ha hw h)
    (finrank_le_of_forall_eq_zero (B := B) fun w hw h =>
      H.eq_zero_of_perfect_left ha hw fun v hv => by rw [H.skew v w, h v hv, neg_zero])

theorem primaryMultiplicity_reciprocal {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) :
    primaryMultiplicity (x : Module.End K V) (reciprocalPolynomial a) =
      primaryMultiplicity (x : Module.End K V) a := by
  have hb := H.reciprocal_mem ha
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have : Fact (Irreducible (reciprocalPolynomial a)) := ⟨irreducible_of_mem_primaryFactors hb⟩
  have h1 := finrank_primaryComponent (x : Module.End K V) a
  have h2 := finrank_primaryComponent (x : Module.End K V) (reciprocalPolynomial a)
  rw [H.finrank_reciprocal ha, h1, natDegree_reciprocalPolynomial (H.coeff_zero_ne ha)] at h2
  have hd : 0 < a.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
  exact (Nat.eq_of_mul_eq_mul_left hd h2).symm

theorem adj_primaryProjection {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    H.adj (primaryProjection (x : Module.End K V) a) =
      primaryProjection (x : Module.End K V) (reciprocalPolynomial a) := by
  have hsq := H.squarefree
  have hb := H.reciprocal_mem ha
  refine H.adj_unique fun v w => ?_
  rw [H.B_eq_sum (primaryProjection (x : Module.End K V) a v) w, H.B_eq_sum v
    (primaryProjection (x : Module.End K V) (reciprocalPolynomial a) w)]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
  · rw [primaryProjection_of_mem hsq ha (primaryProjection_mem hsq ha v),
      primaryProjection_of_mem hsq hb (primaryProjection_mem hsq hb w)]
  · intro c hc hca
    have hne : reciprocalPolynomial a ≠ reciprocalPolynomial c :=
      fun h => hca (H.reciprocal_injOn hc ha h.symm)
    rw [primaryProjection_of_mem_ne hsq (H.reciprocal_mem hc) hb hne
      (primaryProjection_mem hsq hb w), map_zero]
  · intro h
    exact absurd ha h
  · intro c hc hca
    rw [primaryProjection_of_mem_ne hsq hc ha (Ne.symm hca) (primaryProjection_mem hsq ha v),
      map_zero, LinearMap.zero_apply]
  · intro h
    exact absurd ha h

end AltPrimaryData

end CFSG.RankThree.Classical
