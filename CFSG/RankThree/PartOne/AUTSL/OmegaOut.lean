module

public import CFSG.RankThree.PartOne.AUTSL.OmegaModel
public import CFSG.RankThree.PartOne.AUTSL.FrobDickson
public import CFSG.RankThree.PartOne.AUTSL.CycInv
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification
  CFSG.RankThree.OrthogonalInvolutions Matrix

section Action

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def conjAct : similarityPairs Q →* MulAut (matrixDerived Q) where
  toFun := matrixDerivedConjugation Q
  map_one' := by
    refine MulEquiv.ext fun A => ?_
    change matrixDerivedConjugation Q 1 A = A
    exact matrixDerivedConjugation_one Q A
  map_mul' g h := by
    refine MulEquiv.ext fun A => ?_
    change matrixDerivedConjugation Q (g * h) A =
      matrixDerivedConjugation Q g (matrixDerivedConjugation Q h A)
    exact matrixDerivedConjugation_mul Q g h A

variable {Q}

theorem conjAct_apply (g : similarityPairs Q) (A : matrixDerived Q) :
    conjAct Q g A = matrixDerivedConjugation Q g A := rfl

theorem conjAct_inclusion_val (B : matrixIsometries Q) (A : matrixDerived Q) :
    (conjAct Q (matrixIsometryInclusion Q B) A).val = B.val * A.val * B.val⁻¹ := by
  rw [conjAct_apply, matrixDerivedConjugation_val]
  simp only [matrixIsometryInclusion_val, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    map_one, MulAut.one_apply]

theorem conjAct_inclusion_of_mem (B : matrixIsometries Q) (hB : B.val ∈ matrixDerived Q) :
    conjAct Q (matrixIsometryInclusion Q B) = MulAut.conj ⟨B.val, hB⟩ := by
  refine MulEquiv.ext fun A => Subtype.ext ?_
  rw [conjAct_inclusion_val]
  rfl

theorem conjAct_inclusion_mem_inner (B : matrixIsometries Q) (hB : B.val ∈ matrixDerived Q) :
    conjAct Q (matrixIsometryInclusion Q B) ∈ OuterAutomorphisms.inner (matrixDerived Q) := by
  rw [conjAct_inclusion_of_mem B hB]
  exact ⟨⟨B.val, hB⟩, rfl⟩

theorem conjAct_eq_of_isometry {g : similarityPairs Q} {B : matrixIsometries Q}
    (h : ∀ C : matrixDerived Q, (conjAct Q g C).val = B.val * C.val * B.val⁻¹) :
    conjAct Q g = conjAct Q (matrixIsometryInclusion Q B) :=
  MulEquiv.ext fun C => Subtype.ext (by rw [h C, conjAct_inclusion_val])

theorem scalar_eq_one_of_mem_isometries [CharP K 2] (hQ : ∃ v, Q v ≠ 0) {a : Kˣ}
    (ha : Matrix.GeneralLinearGroup.scalar (Fin d) a ∈ matrixIsometries Q) : a = 1 := by
  obtain ⟨v, hv⟩ := hQ
  have h1 := (mem_matrixIsometries_iff Q _).1 ha v
  have h2 : matrixLinearEquiv (Matrix.GeneralLinearGroup.scalar (Fin d) a) v = (a : K) • v := by
    ext i
    simp [matrixLinearEquiv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal]
  rw [h2, QuadraticMap.map_smul, smul_eq_mul] at h1
  have h3 : ((a : K) * (a : K) - 1) * Q v = 0 := by linear_combination h1
  have h4 : (a : K) * (a : K) = 1 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have h5 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h4 + (1 - (a : K)) * h2'
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h5))

end Action

section AutAction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
theorem exists_pair_of_aut (hQ : ∃ v, Q v ≠ 0) (htop : matrixProjectiveImage Q = ⊤)
    (α : MulAut (matrixDerived Q)) : ∃ g : similarityPairs Q, conjAct Q g = α := by
  let Φ := derivedProjEquiv Q hQ
  have hmem : MulAut.congr Φ α ∈ matrixProjectiveImage Q := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ _).1 hmem
  refine ⟨g, MulEquiv.ext fun A => ?_⟩
  have h1 : Φ (α A) = Φ (matrixDerivedConjugation Q g A) := by
    have h2 : MulAut.congr Φ α (Φ A) = Φ (α A) := congr_apply_apply' Φ α A
    rw [← h2, ← hg]
    show matrixProjectiveConjugation _ g (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ _
    exact matrixProjectiveConjugation_mk _ g A
  exact (Φ.injective h1).symm

omit [Finite K] [CharP K 2] in
theorem scalar_of_conjAct_eq_one (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q))
    {g : similarityPairs Q} (hg : conjAct Q g = 1) :
    ∃ a : Kˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a := by
  have h1 : matrixProjectiveConjugationHom Q g = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
    change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q A
    rw [matrixProjectiveConjugation_mk]
    congr 1
    have := congrArg (fun α : MulAut (matrixDerived Q) => α A) hg
    exact this
  obtain ⟨-, a, ha⟩ :=
    (CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff Q hnd hS3 hAP
      g).1 h1
  exact ⟨a, ha⟩

theorem exists_frob_pow (σ : K ≃+* K) : ∃ i : ℕ, σ = (frobeniusEquiv K 2) ^ i := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let σ' : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    have h : (σ.toRingHom.comp (algebraMap (ZMod 2) K) : ZMod 2 →+* K) =
        algebraMap (ZMod 2) K := RingHom.ext_zmod _ _
    exact congrArg (fun φ : ZMod 2 →+* K => φ x) h)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K σ'
  refine ⟨i, RingEquiv.ext fun x => ?_⟩
  rw [frobeniusEquiv_pow_apply]
  have := hi x
  rw [Nat.card_zmod] at this
  exact this

end AutAction

section Reflections

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def reflAut (w : Fin d → K) (hw : Q w ≠ 0) : MulAut (matrixDerived Q) :=
  conjAct Q (matrixIsometryInclusion Q ⟨reflMat Q w hw, reflMat_mem_isometries w hw⟩)

variable {Q}

theorem reflAut_apply_val (w : Fin d → K) (hw : Q w ≠ 0) (C : matrixDerived Q) :
    (reflAut Q w hw C).val = (reflMat Q w hw) * C.val * (reflMat Q w hw)⁻¹ :=
  conjAct_inclusion_val ⟨reflMat Q w hw, reflMat_mem_isometries w hw⟩ C

theorem reflAut_mul_self (w : Fin d → K) (hw : Q w ≠ 0) :
    reflAut Q w hw * reflAut Q w hw = 1 := by
  rw [reflAut, ← map_mul, ← map_mul]
  have : (⟨reflMat Q w hw, reflMat_mem_isometries w hw⟩ * ⟨reflMat Q w hw,
      reflMat_mem_isometries w hw⟩ : matrixIsometries Q) = 1 :=
    Subtype.ext (reflMat_mul_self w hw)
  rw [this, map_one, map_one]

end Reflections

section Structure

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev Qm (n : ℕ) (hn4 : 4 ≤ n) (b c : K) :
    QuadraticForm K (Fin (2 * n) → K) :=
  coordinateQuadMinus n K (by omega) b c

theorem exists_frobenius_class (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    ∃ τ : MulAut (matrixDerived (Qm n hn4 b c)),
      (∀ α : MulAut (matrixDerived (Qm n hn4 b c)), ∃ k : ℕ,
        (τ ^ k)⁻¹ * α ∈ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c))) ∧
      τ ^ (2 * f) ∈ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ∧
      τ ^ f ∉ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ∧
      ∀ (w : Fin (2 * n) → K) (hw : Qm n hn4 b c w ≠ 0),
        ∃ ν ∈ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)),
          reflAut (Qm n hn4 b c) w hw = ν * τ ^ f := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hQ : ∃ v, Qm n hn4 b c v ≠ 0 := exists_ne_zero_of_polar_nondegenerate (by omega) _ hnd
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c
    hirr
  have hb : b ≠ 0 := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨A, hA, hAΓ, hTf⟩ := frobPair_pow_f_eq_inclusion n hn b c hb hf hirr hnd hT
  set T := frobPair n hn b c hb with hTdef
  set Q := Qm n hn4 b c with hQdef
  have hτf : (conjAct Q T) ^ f = conjAct Q (matrixIsometryInclusion Q ⟨A, hA⟩) := by
    rw [← map_pow, hTf]
  have key4 : ∀ (w : Fin (2 * n) → K) (hw : Q w ≠ 0),
      ∃ ν ∈ OuterAutomorphisms.inner (matrixDerived Q), reflAut Q w hw = ν * (conjAct Q T) ^ f := by
    intro w hw
    have hR := reflMat_mem_isometries (Q := Q) w hw
    have hAR : A * reflMat Q w hw ∈ matrixDerived Q := by
      rcases mem_or_mul_reflMat_mem hnd hT hA w hw with h | h
      · exact absurd h hAΓ
      · exact h
    refine ⟨(conjAct Q (matrixIsometryInclusion Q ⟨A * reflMat Q w hw, mul_mem hA hR⟩))⁻¹,
      inv_mem (conjAct_inclusion_mem_inner _ hAR), ?_⟩
    have hιA : matrixIsometryInclusion Q ⟨A, hA⟩ =
        matrixIsometryInclusion Q ⟨A * reflMat Q w hw, mul_mem hA hR⟩ *
          matrixIsometryInclusion Q ⟨reflMat Q w hw, hR⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change A = A * reflMat Q w hw * reflMat Q w hw
      rw [mul_assoc, reflMat_mul_self, mul_one]
    rw [hτf, hιA, map_mul, inv_mul_cancel_left]
    rfl
  have hN2 : (conjAct Q T) ^ (2 * f) ∈ OuterAutomorphisms.inner (matrixDerived Q) := by
    rw [pow_mul', hτf, ← map_pow, ← map_pow]
    refine conjAct_inclusion_mem_inner _ ?_
    change (A ^ 2) ∈ matrixDerived Q
    rw [sq]
    exact mul_self_mem_matrixDerived hnd hT hA
  have hN3 : (conjAct Q T) ^ f ∉ OuterAutomorphisms.inner (matrixDerived Q) := by
    rintro ⟨γ, hγ⟩
    have hγO : γ.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q γ.2
    have e : conjAct Q (matrixIsometryInclusion Q ⟨γ.val, hγO⟩) = MulAut.conj γ :=
      conjAct_inclusion_of_mem ⟨γ.val, hγO⟩ γ.2
    have h1 : conjAct Q (matrixIsometryInclusion Q ⟨A, hA⟩ *
        (matrixIsometryInclusion Q ⟨γ.val, hγO⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hτf, ← hγ, e, mul_inv_cancel]
    obtain ⟨a, ha⟩ := scalar_of_conjAct_eq_one hnd hT hAP h1
    have hleft : (matrixIsometryInclusion Q ⟨A, hA⟩ *
        (matrixIsometryInclusion Q ⟨γ.val, hγO⟩)⁻¹).val.left = A * (γ.val)⁻¹ := by
      rw [← map_inv, ← map_mul, matrixIsometryInclusion_val, SemidirectProduct.left_inl]
      rfl
    rw [hleft] at ha
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin (2 * n)) a ∈ matrixIsometries Q := by
      rw [← ha]
      exact mul_mem hA (inv_mem hγO)
    have ha1 := scalar_eq_one_of_mem_isometries hQ hmem
    rw [ha1, map_one] at ha
    have hAγ : A = γ.val := by
      have := congrArg (· * γ.val) ha
      simpa using this
    exact hAΓ (hAγ ▸ γ.2)
  have hgen : ∀ α : MulAut (matrixDerived Q), ∃ k : ℕ,
      ((conjAct Q T) ^ k)⁻¹ * α ∈ OuterAutomorphisms.inner (matrixDerived Q) := by
    intro α
    obtain ⟨g, rfl⟩ := exists_pair_of_aut hQ htop α
    obtain ⟨i, hi⟩ := exists_frob_pow g.val.right
    let ℓ : similarityPairs Q := (T ^ i)⁻¹ * g
    have hℓ : ℓ.val.right = 1 := by
      have hfT : fieldProjection Q T = frobeniusEquiv K 2 := rfl
      have : fieldProjection Q ℓ = 1 := by
        simp only [ℓ, map_mul, map_inv, map_pow, hfT, fieldProjection_apply, hi, inv_mul_cancel]
      exact this
    obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.OutStructure.exists_isometry_of_linear Q hQ
      ⟨ℓ, (mem_linearSimilarityPairs_iff Q ℓ).2 hℓ⟩
    have hℓB : conjAct Q ℓ = conjAct Q (matrixIsometryInclusion Q B) :=
      conjAct_eq_of_isometry hB
    have hg : g = T ^ i * ℓ := (mul_inv_cancel_left (T ^ i) g).symm
    have hα : conjAct Q g = (conjAct Q T) ^ i * conjAct Q (matrixIsometryInclusion Q B) := by
      rw [← hℓB, ← map_pow, ← map_mul, ← hg]
    obtain ⟨w₁, hw₁⟩ := hQ
    rcases mem_or_mul_reflMat_mem hnd hT B.2 w₁ hw₁ with hBΓ | hBΓ
    · refine ⟨i, ?_⟩
      rw [hα, inv_mul_cancel_left]
      exact conjAct_inclusion_mem_inner B hBΓ
    · refine ⟨i + f, ?_⟩
      have hR := reflMat_mem_isometries (Q := Q) w₁ hw₁
      obtain ⟨ν, hν, hrefl⟩ := key4 w₁ hw₁
      have hιB : matrixIsometryInclusion Q B =
          matrixIsometryInclusion Q ⟨B.val * reflMat Q w₁ hw₁, mul_mem B.2 hR⟩ *
            matrixIsometryInclusion Q ⟨reflMat Q w₁ hw₁, hR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        change B.val = B.val * reflMat Q w₁ hw₁ * reflMat Q w₁ hw₁
        rw [mul_assoc, reflMat_mul_self, mul_one]
      have hn₁ := conjAct_inclusion_mem_inner
        (Q := Q) ⟨B.val * reflMat Q w₁ hw₁, mul_mem B.2 hR⟩ hBΓ
      have hcalc : ((conjAct Q T) ^ (i + f))⁻¹ * conjAct Q g =
          ((conjAct Q T) ^ f)⁻¹ *
            (conjAct Q (matrixIsometryInclusion Q ⟨B.val * reflMat Q w₁ hw₁, mul_mem B.2 hR⟩) *
              ν) * (((conjAct Q T) ^ f)⁻¹)⁻¹ := by
        rw [hα, hιB, map_mul]
        change _ = _ * (conjAct Q (matrixIsometryInclusion Q ⟨B.val * reflMat Q w₁ hw₁,
          mul_mem B.2 hR⟩) * _) * _
        have hr : conjAct Q (matrixIsometryInclusion Q ⟨reflMat Q w₁ hw₁, hR⟩) =
            ν * (conjAct Q T) ^ f := hrefl
        rw [hr, pow_add, _root_.mul_inv_rev, inv_inv]
        simp only [mul_assoc, inv_mul_cancel_left]
      rw [hcalc]
      exact (OuterAutomorphisms.inner_normal _).conj_mem _ (mul_mem hn₁ hν) _
  exact ⟨conjAct Q T, hgen, hN2, hN3, key4⟩

theorem reflAut_not_mem_inner (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (w : Fin (2 * n) → K) (hw : Qm n hn4 b c w ≠ 0) :
    reflAut (Qm n hn4 b c) w hw ∉ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := by
  obtain ⟨τ, -, -, hτf, key⟩ := exists_frobenius_class n hn4 b c hirr hf
  obtain ⟨ν, hν, hrefl⟩ := key w hw
  intro hmem
  apply hτf
  have : τ ^ f = ν⁻¹ * reflAut (Qm n hn4 b c) w hw := by rw [hrefl, inv_mul_cancel_left]
  rw [this]
  exact mul_mem (inv_mem hν) hmem

theorem reflAut_mem_of_two_power (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (matrixDerived (Qm n hn4 b c))))
    (hN : OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ≤ H)
    {x : MulAut (matrixDerived (Qm n hn4 b c))} (hx : x ∈ H)
    (hxN : x ∉ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c))) {a : ℕ}
    (hxa : x ^ 2 ^ a = 1) (w : Fin (2 * n) → K) (hw : Qm n hn4 b c w ≠ 0) :
    reflAut (Qm n hn4 b c) w hw ∈ H := by
  obtain ⟨τ, hgen, h2f, hτf, key⟩ := exists_frobenius_class n hn4 b c hirr hf
  obtain ⟨ν, hν, hrefl⟩ := key w hw
  obtain ⟨m, hm⟩ := exists_pow_mem_coset (OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)))
    τ f hgen h2f hτf x hxN a (by rw [hxa]; exact one_mem _)
  have h1 : τ ^ f = x ^ m * ((τ ^ f)⁻¹ * x ^ m)⁻¹ := by group
  rw [hrefl, h1]
  exact mul_mem (hN hν) (mul_mem (pow_mem hx m) (hN (inv_mem hm)))

end Structure

end CFSG.RankThree.PartOne.AUTSL
