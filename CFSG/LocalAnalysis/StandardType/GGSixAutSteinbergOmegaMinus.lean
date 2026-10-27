module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaModel
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.RankThree.PartOne.AUTSL.OmegaStab
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace AutOm

section Tail

variable {K : Type} [Field K] (n : ℕ) (hn : 1 ≤ n) (b c : K)

noncomputable abbrev tailVec : Fin (2 * n) → K := Pi.single (tailZero n hn) 1

theorem tailVec_zero : (tailVec n hn : Fin (2 * n) → K) (tailZero n hn) = 1 :=
  Pi.single_eq_same _ _

theorem tailVec_one : (tailVec n hn : Fin (2 * n) → K) (tailOne n hn) = 0 :=
  Pi.single_eq_of_ne (tailOne_ne_tailZero n hn) _

theorem tailVec_inl (i : Fin (n - 1)) :
    (tailVec n hn : Fin (2 * n) → K) (minusIndexEquiv n hn (.inl i)) = 0 :=
  Pi.single_eq_of_ne (tailZero_ne_inl n hn i) _

theorem tailVec_inr (i : Fin (n - 1)) :
    (tailVec n hn : Fin (2 * n) → K) (minusIndexEquiv n hn (.inr (.inl i))) = 0 :=
  Pi.single_eq_of_ne (tailZero_ne_inr n hn i) _

theorem polar_tailVec [CharP K 2] (x : Fin (2 * n) → K) :
    QuadraticMap.polar (coordinateQuadMinus n K hn b c) (tailVec n hn) x =
      b * x (tailOne n hn) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.polar, coordQuadMinus_apply', coordQuadMinus_apply', coordQuadMinus_apply']
  simp only [Pi.add_apply, tailVec_inl, tailVec_inr, tailVec_zero, tailVec_one, zero_add,
    mul_zero, Finset.sum_const_zero, add_zero]
  linear_combination x (tailZero n hn) * h2

theorem tailVec_form : coordinateQuadMinus n K hn b c (tailVec n hn) = 1 :=
  form_single_tailZero n hn b c

theorem tailVec_form_ne_zero : coordinateQuadMinus n K hn b c (tailVec n hn) ≠ 0 := by
  rw [tailVec_form]
  exact one_ne_zero

end Tail

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def frobAut : MulAut (matrixDerived (Qm n hn4 b c)) :=
  conjAct (Qm n hn4 b c) (frobPair n (by omega) b c (ne_zero_of_irreducible_tail b c hirr))

noncomputable abbrev tailRefl : MulAut (matrixDerived (Qm n hn4 b c)) :=
  reflAut (Qm n hn4 b c) (tailVec n (by omega)) (tailVec_form_ne_zero n (by omega) b c)

include hirr in
theorem frobAut_pow_f {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    frobAut hn4 hirr ^ f = tailRefl hn4 (b := b) (c := c) := by
  have hn : 1 ≤ n := by omega
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hb := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨A, hA, -, hTf⟩ := frobPair_pow_f_eq_inclusion n hn b c hb hf hirr hnd hT
  obtain ⟨p, hp0, -, hform⟩ := frobPair_pow_f n hn b c hb hf hirr
  have hAv : ∀ v : Fin (2 * n) → K,
      Matrix.mulVec (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) v =
        v + (p * v (tailOne n hn)) • tailVec n hn := by
    intro v
    funext k
    have h := hform v k
    rw [hTf, matrixIsometryInclusion_val, coordinateSemilinearMap_inl, matrixLinearEquiv_apply] at h
    rw [h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = tailZero n hn
    · subst hk
      simp
    · simp [hk]
  have hpb : p = b := by
    have h := (mem_matrixIsometries_iff _ A).1 hA (Pi.single (tailOne n hn) 1)
    rw [matrixLinearEquiv_apply, hAv, Pi.single_eq_same, mul_one] at h
    have e1 := QuadraticMap.map_add (coordinateQuadMinus n K hn b c)
      (Pi.single (tailOne n hn) 1) (p • tailVec n hn)
    rw [QuadraticMap.map_smul, tailVec_form, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_comm, polar_tailVec, Pi.single_eq_same, smul_eq_mul, smul_eq_mul] at e1
    have h3 : p * (p + b) = 0 := by linear_combination e1.symm.trans h
    have h4 := (mul_eq_zero.1 h3).resolve_left hp0
    linear_combination h4 - b * h2
  have hAr : A = reflMat (Qm n hn4 b c) (tailVec n hn) (tailVec_form_ne_zero n hn b c) := by
    apply Units.ext
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hAv,
      reflMat_mulVec_one _ (tailVec_form n hn b c), polar_tailVec, hpb]
  rw [frobAut, ← map_pow, hTf, tailRefl, reflAut]
  congr 2
  exact Subtype.ext hAr

include hirr in
theorem frobAut_pow_two_mul {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    frobAut hn4 hirr ^ (2 * f) = 1 := by
  rw [pow_mul', frobAut_pow_f hn4 hirr hf, sq, tailRefl, reflAut_mul_self]

include hirr in
theorem frobAut_pow_f_not_mem_inner {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    frobAut hn4 hirr ^ f ∉ inner (matrixDerived (Qm n hn4 b c)) := by
  rw [frobAut_pow_f hn4 hirr hf]
  exact reflAut_not_mem_inner n hn4 b c hirr hf _ _

include hirr in
theorem dvd_of_frobAut_pow_mem_inner {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) {k : ℕ}
    (hk : frobAut hn4 hirr ^ k ∈ inner (matrixDerived (Qm n hn4 b c))) : f ∣ k := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  obtain ⟨γ, hγ⟩ := hk
  have hγO : γ.val ∈ matrixIsometries (Qm n hn4 b c) := matrixDerived_le_isometries _ γ.2
  have e : conjAct (Qm n hn4 b c) (matrixIsometryInclusion (Qm n hn4 b c) ⟨γ.val, hγO⟩) =
      MulAut.conj γ :=
    conjAct_inclusion_of_mem ⟨γ.val, hγO⟩ γ.2
  have h1 : conjAct (Qm n hn4 b c) (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k *
      (matrixIsometryInclusion (Qm n hn4 b c) ⟨γ.val, hγO⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, e, hγ]
    exact mul_inv_cancel _
  have h2 : matrixProjectiveConjugationHom (Qm n hn4 b c)
      (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k *
        (matrixIsometryInclusion (Qm n hn4 b c) ⟨γ.val, hγO⟩)⁻¹) = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective _ x
    change matrixProjectiveConjugation _ _ (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ A
    rw [matrixProjectiveConjugation_mk]
    congr 1
    exact congrArg (fun α : MulAut (matrixDerived (Qm n hn4 b c)) => α A) h1
  have h3 := ((CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _
    hnd hT hAP _).1 h2).1
  have h4 : (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k *
      (matrixIsometryInclusion (Qm n hn4 b c) ⟨γ.val, hγO⟩)⁻¹).val.right =
        (frobeniusEquiv K 2) ^ k := by
    rw [← fieldProjection_apply, map_mul, map_inv, map_pow, fieldProjection_apply, frobPair_right,
      fieldProjection_apply, matrixIsometryInclusion_val, SemidirectProduct.right_inl, inv_one,
      mul_one]
  obtain ⟨σ, hσ, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf1 hf
  have hσφ : σ = frobeniusEquiv K 2 := RingEquiv.ext fun a => by
    rw [hσ, frobeniusEquiv_apply, frobenius_def]
  rw [← hord, hσφ]
  exact orderOf_dvd_of_pow_eq_one (h4 ▸ h3)

include hirr in
theorem exists_inner_mul_frobAut_pow {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (α : MulAut (matrixDerived (Qm n hn4 b c))) :
    ∃ ι ∈ inner (matrixDerived (Qm n hn4 b c)), ∃ k : ℕ, α = ι * frobAut hn4 hirr ^ k := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hw0 : Qm n hn4 b c (tailVec n hn) ≠ 0 := tailVec_form_ne_zero n hn b c
  have htop :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  obtain ⟨g, hgα⟩ := exists_pair_of_aut ⟨_, hw0⟩ htop α
  subst hgα
  obtain ⟨i, hi⟩ := exists_frob_pow g.val.right
  have hℓ : ((frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ i)⁻¹ * g).val.right =
      1 := by
    rw [← fieldProjection_apply, map_mul, map_inv, map_pow, fieldProjection_apply, frobPair_right,
      fieldProjection_apply,
      hi, inv_mul_cancel]
  obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.OutStructure.exists_isometry_of_linear _ ⟨_, hw0⟩
    ⟨_, (mem_linearSimilarityPairs_iff _ _).2 hℓ⟩
  have hℓB := conjAct_eq_of_isometry hB
  have hα : conjAct (Qm n hn4 b c) g =
      frobAut hn4 hirr ^ i * conjAct (Qm n hn4 b c) (matrixIsometryInclusion _ B) := by
    rw [← hℓB, frobAut, ← map_pow, ← map_mul]
    congr 1
    exact (mul_inv_cancel_left _ g).symm
  have hN := inner_normal (matrixDerived (Qm n hn4 b c))
  rcases mem_or_mul_reflMat_mem hnd hT B.2 (tailVec n hn) hw0 with hBΓ | hBΓ
  · refine ⟨frobAut hn4 hirr ^ i * conjAct (Qm n hn4 b c) (matrixIsometryInclusion _ B) *
      (frobAut hn4 hirr ^ i)⁻¹, hN.conj_mem _ (conjAct_inclusion_mem_inner B hBΓ) _, i, ?_⟩
    rw [hα, inv_mul_cancel_right]
  · have hR := reflMat_mem_isometries (Q := Qm n hn4 b c) (tailVec n hn) hw0
    have hιB : matrixIsometryInclusion (Qm n hn4 b c) B =
        matrixIsometryInclusion (Qm n hn4 b c)
          ⟨B.val * reflMat (Qm n hn4 b c) (tailVec n hn) hw0, mul_mem B.2 hR⟩ *
          matrixIsometryInclusion (Qm n hn4 b c) ⟨reflMat _ (tailVec n hn) hw0, hR⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change B.val = B.val * reflMat _ (tailVec n hn) hw0 * reflMat _ (tailVec n hn) hw0
      rw [mul_assoc, reflMat_mul_self, mul_one]
    have hn₁ := conjAct_inclusion_mem_inner
      (Q := Qm n hn4 b c) ⟨B.val * reflMat _ (tailVec n hn) hw0, mul_mem B.2 hR⟩ hBΓ
    have hrefl : conjAct (Qm n hn4 b c)
        (matrixIsometryInclusion (Qm n hn4 b c) ⟨reflMat _ (tailVec n hn) hw0, hR⟩) =
          frobAut hn4 hirr ^ f :=
      (frobAut_pow_f hn4 hirr hf).symm
    refine ⟨frobAut hn4 hirr ^ i * conjAct (Qm n hn4 b c) (matrixIsometryInclusion _
      ⟨B.val * reflMat _ (tailVec n hn) hw0, mul_mem B.2 hR⟩) * (frobAut hn4 hirr ^ i)⁻¹,
      hN.conj_mem _ hn₁ _, i + f, ?_⟩
    rw [hα, hιB, map_mul, hrefl, pow_add]
    group

include hirr in
theorem isOfFinOrder_frobAut {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) :
    IsOfFinOrder (frobAut hn4 hirr) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨2 * f, by omega, frobAut_pow_two_mul hn4 hirr hf⟩

include hirr in
theorem frobAut_pow_f_sq {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    (frobAut hn4 hirr ^ f) ^ 2 = 1 := by
  rw [← pow_mul', frobAut_pow_two_mul hn4 hirr hf]

include hirr in
theorem inner_inf_zpowers_frobAut {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) :
    inner (matrixDerived (Qm n hn4 b c)) ⊓ Subgroup.zpowers (frobAut hn4 hirr) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxI, hxC⟩
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff x _).1
    ((isOfFinOrder_frobAut hn4 hirr hf hf1).mem_powers_iff_mem_zpowers.2 hxC)
  obtain ⟨j, rfl⟩ := dvd_of_frobAut_pow_mem_inner hn4 hirr hf hf1 hxI
  have hsq := frobAut_pow_f_sq hn4 hirr hf
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [pow_mul, ← two_mul, pow_mul, hsq, one_pow]
  · exfalso
    rw [pow_mul, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one] at hxI
    exact frobAut_pow_f_not_mem_inner hn4 hirr hf hxI

include hirr in
theorem eq_tailRefl_of_mem_zpowers {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    {x : MulAut (matrixDerived (Qm n hn4 b c))} (hx : x ∈ Subgroup.zpowers (frobAut hn4 hirr))
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : x = tailRefl hn4 := by
  have hfin := isOfFinOrder_frobAut hn4 hirr hf hf1
  have : Finite (Subgroup.zpowers (frobAut hn4 hirr)) := hfin.finite_zpowers
  have hmem : frobAut hn4 hirr ^ f ∈ Subgroup.zpowers (frobAut hn4 hirr) :=
    Subgroup.npow_mem_zpowers _ f
  have hne : frobAut hn4 hirr ^ f ≠ 1 := fun h =>
    frobAut_pow_f_not_mem_inner hn4 hirr hf (h ▸ one_mem _)
  have h := eq_of_sq_eq_one_of_isCyclic (C := Subgroup.zpowers (frobAut hn4 hirr))
    (y := ⟨x, hx⟩) (z := ⟨_, hmem⟩) (Subtype.ext hx2) (fun h1 => hx1 (congrArg Subtype.val h1))
    (Subtype.ext (frobAut_pow_f_sq hn4 hirr hf)) (fun h1 => hne (congrArg Subtype.val h1))
  rw [← frobAut_pow_f hn4 hirr hf]
  exact congrArg Subtype.val h

end Frob

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem tailRefl_apply_eq_iff (X : matrixDerived (Qm n hn4 b c)) :
    tailRefl hn4 X = X ↔
      Matrix.mulVec ((X : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
        (tailVec n (by omega)) = tailVec n (by omega) := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, -⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hXO : (X : GL (Fin (2 * n)) K) ∈ matrixIsometries (Qm n hn4 b c) :=
    matrixDerived_le_isometries _ X.2
  rw [← comm_reflMat_iff hnd hXO (tailVec_form n hn b c) (tailVec_form_ne_zero n hn b c)]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [tailRefl, reflAut_apply_val] at h'
    calc (X : GL (Fin (2 * n)) K) * reflMat _ _ (tailVec_form_ne_zero n hn b c) =
        reflMat _ _ (tailVec_form_ne_zero n hn b c) * X * (reflMat _ _
          (tailVec_form_ne_zero n hn b c))⁻¹ * reflMat _ _ (tailVec_form_ne_zero n hn b c) := by
          rw [h']
      _ = _ := by rw [inv_mul_cancel_right]
  · intro h
    apply Subtype.ext
    rw [tailRefl, reflAut_apply_val, ← h, mul_inv_cancel_right]

include hirr in
theorem eq_bot_of_tailRefl (S : Subgroup (matrixDerived (Qm n hn4 b c)))
    (hfix : ∀ q ∈ S, tailRefl hn4 q = q) (hS : IsPGroup 2 S)
    (hnorm : ∀ y, tailRefl hn4 y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) : S = ⊥ := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  set R := S.map (matrixDerived (Qm n hn4 b c)).subtype with hRdef
  have hR : R = ⊥ := by
    refine eq_bot_of_normal_two_subgroup hnd hT (tailVec_form n hn b c) (by omega) R
      (hS.map _) ?_ ?_ ?_
    · rintro _ ⟨q, -, rfl⟩
      exact q.2
    · rintro _ ⟨q, hq, rfl⟩
      exact (tailRefl_apply_eq_iff hn4 hirr q).1 (hfix q hq)
    · rintro s hs hsw _ ⟨q, hq, rfl⟩
      have hy := (tailRefl_apply_eq_iff hn4 hirr ⟨s, hs⟩).2 hsw
      exact ⟨_, hnorm _ hy q hq, rfl⟩
  rw [hRdef] at hR
  exact (Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).1 hR

end Fixed

end AutOm

end CFSG.StandardType
