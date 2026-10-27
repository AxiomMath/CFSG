module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusGood

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace AutOm

section Group

variable {G : Type*} [Group G] {t r p : G}

theorem triality_sq_eq (ht : t ^ 3 = 1) (hrr : r * r = 1)
    (hr : ∀ l : ℕ, r * t ^ l = t ^ (2 * l) * r)
    (hp : ∀ l : ℕ, p * t ^ l = t ^ l * p) (hrp : r * p = p * r) (k : ℕ) :
    (t ^ k * (r * p)) ^ 2 = p * p := by
  have h3 : t ^ (3 * k) = 1 := by rw [pow_mul, ht, one_pow]
  simp only [sq, mul_assoc]
  rw [← mul_assoc p, hp, mul_assoc, ← mul_assoc r, hr, mul_assoc, ← mul_assoc (t ^ k), ← pow_add,
    show k + 2 * k = 3 * k by ring, h3, one_mul, ← mul_assoc p r, ← hrp, mul_assoc,
    ← mul_assoc r r, hrr, one_mul]

theorem triality_conj_eq (ht : t ^ 3 = 1) (hr : ∀ l : ℕ, r * t ^ l = t ^ (2 * l) * r)
    (hp : ∀ l : ℕ, p * t ^ l = t ^ l * p) (k : ℕ) :
    t ^ k * (r * p) = t ^ (2 * k) * (r * p) * (t ^ (2 * k))⁻¹ := by
  have h3 : t ^ (3 * k) = 1 := by rw [pow_mul, ht, one_pow]
  have hinv : (t ^ (2 * k))⁻¹ = t ^ k := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 * k + k = 3 * k by ring, h3]
  rw [hinv, mul_assoc, mul_assoc, hp, ← mul_assoc r, hr, ← mul_assoc, ← mul_assoc,
    ← mul_assoc (t ^ (2 * k)) (t ^ (2 * k)), ← pow_add, show 2 * k + 2 * k = k + 3 * k by ring,
    pow_add, h3, mul_one, mul_assoc]

end Group

section Triality

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem goodAut_plusRefl (hn4 : 4 ≤ n) {r : matrixDerived (coordinateQuadPlus n K)}
    (hr : PlusRootElt (by omega) r) : GGGoodAut r (plusRefl (by omega)) :=
  goodAut_plus_of (by omega) (eq_bot_of_plusRefl (by omega))
    (fun _ _ hij s t hi hj => plusRefl_fix_longRoot (by omega) hij hi hj s t 1) hr

theorem goodAut_fieldAutP (hn4 : 4 ≤ n) (σ : K ≃+* K) {r : matrixDerived (coordinateQuadPlus n K)}
    (hr : PlusRootElt (by omega) r) : GGGoodAut r (fieldAutP n σ) :=
  goodAut_plus_of (by omega) (fun S _ hS hnorm => eq_bot_of_fieldAutP (by omega) σ S hS hnorm)
    (fun _ _ hij s t _ _ => fieldAutP_fix_longRoot (by omega) σ hij s t) hr

theorem goodAut_reflFieldAutP (hn4 : 4 ≤ n) {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {r : matrixDerived (coordinateQuadPlus n K)} (hr : PlusRootElt (by omega) r) :
    GGGoodAut r (plusRefl (by omega) * fieldAutP n σ) :=
  goodAut_plus_of (by omega)
    (fun S _ hS hnorm => eq_bot_of_reflFieldAutP hn4 hσσ hσ1 S hS hnorm)
    (fun _ _ hij s t hi hj => reflField_fix_longRoot (by omega) σ hij hi hj s t) hr

variable (hn4 : 4 ≤ n) {θ : MulAut (matrixDerived (coordinateQuadPlus n K))}
  (hθ3 : θ ^ 3 = 1) (hρθ : plusRefl (by omega) * θ * plusRefl (by omega) = θ⁻¹)
  (hφθ : ∀ σ : K ≃+* K, θ * fieldAutP n σ = fieldAutP n σ * θ)

include hθ3 hρθ in
theorem plusRefl_mul_pow (l : ℕ) :
    plusRefl (by omega) * θ ^ l = θ ^ (2 * l) * plusRefl (K := K) (by omega : 1 ≤ n) := by
  have hρ := plusRefl_mul_self (K := K) (n := n) (by omega)
  have h1 : plusRefl (by omega) * θ = θ⁻¹ * plusRefl (K := K) (by omega : 1 ≤ n) := by
    rw [← hρθ, mul_assoc, mul_assoc, hρ, mul_one]
  have hinv : θ⁻¹ = θ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hθ3]
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, h1, hinv, ← mul_assoc, ← pow_add]
    ring_nf

include hθ3 hρθ hφθ in
theorem compl_mul_pow {c : MulAut (matrixDerived (coordinateQuadPlus n K))}
    (hc : c ∈ plusCompl (by omega : 1 ≤ n)) (l : ℕ) : ∃ l' : ℕ, c * θ ^ l = θ ^ l' * c := by
  have hφ : ∀ σ : K ≃+* K, fieldAutP n σ * θ ^ l = θ ^ l * fieldAutP n σ := fun σ => by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, ← hφθ, ← mul_assoc, ← pow_succ]
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact ⟨l, hφ σ⟩
  · refine ⟨2 * l, ?_⟩
    rw [mul_assoc, hφ, ← mul_assoc, plusRefl_mul_pow hn4 hθ3 hρθ, mul_assoc]

@[expose] noncomputable def trialityCompl :
    Subgroup (MulAut (matrixDerived (coordinateQuadPlus n K))) where
  carrier := {x | ∃ k : ℕ, ∃ c ∈ plusCompl (by omega : 1 ≤ n), x = θ ^ k * c}
  mul_mem' := by
    rintro x y ⟨k, c, hc, rfl⟩ ⟨l, c', hc', rfl⟩
    obtain ⟨l', hl'⟩ := compl_mul_pow hn4 hθ3 hρθ hφθ hc l
    exact ⟨k + l', c * c', mul_mem hc hc', by
      rw [pow_add, mul_assoc, ← mul_assoc c, hl', mul_assoc, mul_assoc]⟩
  one_mem' := ⟨0, 1, one_mem _, by rw [pow_zero, one_mul]⟩
  inv_mem' := by
    rintro x ⟨k, c, hc, rfl⟩
    obtain ⟨l', hl'⟩ := compl_mul_pow hn4 hθ3 hρθ hφθ (inv_mem hc) (2 * k)
    refine ⟨l', c⁻¹, inv_mem hc, ?_⟩
    have hinv : (θ ^ k)⁻¹ = θ ^ (2 * k) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hθ3,
        one_pow]
    rw [_root_.mul_inv_rev, hinv, hl']

omit [Finite K] [CharP K 2] in
include hφθ in
theorem fieldAutP_mul_pow (σ : K ≃+* K) (l : ℕ) :
    fieldAutP n σ * θ ^ l = θ ^ l * fieldAutP n σ := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, ← hφθ, ← mul_assoc, ← pow_succ]

omit [Finite K] [CharP K 2] in
include hθ3 in
theorem pow_three_mul (k : ℕ) : θ ^ (3 * k) = 1 := by
  rw [pow_mul, hθ3, one_pow]

omit [Finite K] [CharP K 2] in
include hθ3 in
theorem inv_pow_two_mul (k : ℕ) : (θ ^ (2 * k))⁻¹ = θ ^ k := by
  rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 * k + k = 3 * k by ring, pow_three_mul hθ3]

omit [Finite K] [CharP K 2] in
include hθ3 in
theorem pow_eq_one_of_pow_two_mul (k : ℕ) (h : θ ^ (2 * k) = 1) : θ ^ k = 1 := by
  rw [← inv_pow_two_mul hθ3, h, inv_one]

omit [Finite K] [CharP K 2] in
theorem pow_apply_plusRootElt
    (hroot : ∀ r, PlusRootElt (K := K) (by omega : 3 ≤ n) r → PlusRootElt (by omega) (θ r))
    (m : ℕ) {r : matrixDerived (coordinateQuadPlus n K)} (hr : PlusRootElt (by omega) r) :
    PlusRootElt (by omega : 3 ≤ n) ((θ ^ m) r) := by
  induction m with
  | zero => simpa using hr
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact hroot _ ih

include hθ3 hρθ hφθ in
theorem autModel_of_triality
    (hgen : ∀ α : MulAut (matrixDerived (coordinateQuadPlus n K)),
      ∃ ι ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)), ∃ k : ℕ,
        ∃ c ∈ plusCompl (by omega : 1 ≤ n), α = ι * (θ ^ k * c))
    (huniq : ∀ k : ℕ, ∀ c ∈ plusCompl (by omega : 1 ≤ n),
      θ ^ k * c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) → θ ^ k = 1 ∧ c = 1)
    (hroot : ∀ r, PlusRootElt (K := K) (by omega : 3 ≤ n) r → PlusRootElt (by omega) (θ r)) :
    GGAutModel (matrixDerived (coordinateQuadPlus n K)) (PlusRootElt (by omega)) := by
  refine ⟨inner _, trialityCompl hn4 hθ3 hρθ hφθ, inner_normal _, le_rfl, ?_, fun α => ?_, ?_,
    fun r hr x hx hx2 hx1 e he => AutSt.goodAut_conj_inner ?_ he⟩
  · rw [show inner (matrixDerived (coordinateQuadPlus n K)) =
        (MulAut.conj : matrixDerived (coordinateQuadPlus n K) →* _).range from rfl,
      Subgroup.relIndex_self]
    exact odd_one
  · obtain ⟨ι, hι, k, c, hc, rfl⟩ := hgen α
    exact ⟨ι, hι, _, ⟨k, c, hc, rfl⟩, rfl⟩
  · rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxI, k, c, hc, rfl⟩
    obtain ⟨h1, h2⟩ := huniq k c hc hxI
    rw [h1, h2, one_mul]
  · obtain ⟨k, c, hc, rfl⟩ := hx
    obtain ⟨σ, rfl | rfl⟩ := hc
    · have hsq : (θ ^ k * fieldAutP n σ) ^ 2 = θ ^ (2 * k) * fieldAutP n (σ * σ) := by
        rw [sq, mul_assoc, ← mul_assoc (fieldAutP n σ), fieldAutP_mul_pow hφθ, mul_assoc,
          ← mul_assoc, ← pow_add, map_mul, ← two_mul k]
      obtain ⟨hk2, hσ2⟩ := huniq (2 * k) (fieldAutP n (σ * σ)) ⟨σ * σ, Or.inl rfl⟩
        (by rw [← hsq, hx2]; exact one_mem _)
      have hk := pow_eq_one_of_pow_two_mul hθ3 k hk2
      rw [hk, one_mul] at hx1 ⊢
      exact goodAut_fieldAutP hn4 σ hr
    · have hρ := plusRefl_mul_self (K := K) (n := n) (by omega)
      have hr' : ∀ l : ℕ, plusRefl (K := K) (by omega : 1 ≤ n) * θ ^ l =
          θ ^ (2 * l) * plusRefl (by omega) := plusRefl_mul_pow hn4 hθ3 hρθ
      have hsq : (θ ^ k * (plusRefl (by omega) * fieldAutP n σ)) ^ 2 =
          fieldAutP n (σ * σ) := by
        rw [triality_sq_eq hθ3 hρ hr' (fieldAutP_mul_pow hφθ σ) (plusRefl_mul_fieldAutP _ σ),
          map_mul]
      have hσσ : σ * σ = 1 :=
        eq_one_of_fieldAutP_eq_one (n := n) (by omega) (by rw [← hsq, hx2])
      have hconj := triality_conj_eq hθ3 hr' (fieldAutP_mul_pow hφθ σ) k
      have hgood0 : ∀ r', PlusRootElt (K := K) (by omega : 3 ≤ n) r' →
          GGGoodAut r' (plusRefl (by omega) * fieldAutP n σ) := by
        intro r' hr'
        by_cases hσ1 : σ = 1
        · subst hσ1
          rw [map_one, mul_one]
          exact goodAut_plusRefl hn4 hr'
        · exact goodAut_reflFieldAutP hn4 hσσ hσ1 hr'
      rw [hconj]
      have hr' : PlusRootElt (K := K) (by omega : 3 ≤ n) ((θ ^ (2 * k))⁻¹ r) := by
        rw [inv_pow_two_mul hθ3]
        exact pow_apply_plusRootElt hn4 hroot k hr
      have h := (hgood0 _ hr').congr (θ ^ (2 * k))
      rw [ggMulAut_congr_self] at h
      rwa [MulAut.apply_inv_self] at h

end Triality

end AutOm

@[expose] def PlusFourTrialityInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    ∃ θ : MulAut (matrixDerived (coordinateQuadPlus 4 K)),
      θ ^ 3 = 1 ∧
      AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) * θ * AutOm.plusRefl (by norm_num) = θ⁻¹ ∧
      (∀ σ : K ≃+* K, θ * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * θ) ∧
      (∀ α : MulAut (matrixDerived (coordinateQuadPlus 4 K)),
        ∃ ι ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus 4 K)), ∃ k : ℕ,
            ∃ c ∈ AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4), α = ι * (θ ^ k * c)) ∧
      (∀ k : ℕ, ∀ c ∈ AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4),
        θ ^ k * c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus 4 K)) → θ ^ k = 1 ∧ c = 1) ∧
      ∀ r, AutOm.PlusRootElt (K := K) (by norm_num : 3 ≤ 4) r →
        AutOm.PlusRootElt (by norm_num : 3 ≤ 4) (θ r)

section Family

theorem ggU_POmegaPlus_eq {n f : ℕ} (hn : 3 ≤ n) :
    ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
      plusDatum n (GaloisField 2 f) hn⟩ :=
  dite_eq_left hn

theorem plusFourInput_of_triality (hT : PlusFourTrialityInput) : GGAutModelPlusFourInput := by
  intro f hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ggU_POmegaPlus_eq (show 3 ≤ 4 by norm_num)]
  obtain ⟨θ, h3, hρθ, hφθ, hgen, huniq, hroot⟩ := hT (GaloisField 2 f)
  refine ⟨matrixDerived (coordinateQuadPlus 4 (GaloisField 2 f)), inferInstance,
    AutOm.spinModelPlus (by norm_num), AutOm.spinModelPlus_surjective _,
    AutOm.ker_spinModelPlus _, ?_⟩
  exact (AutOm.autModel_of_triality le_rfl h3 hρθ hφθ hgen huniq hroot).mono
    fun r hr => AutOm.plusRootElt_of_modelRoot _ hr

theorem ggAutModelAt_POmegaPlus_of_triality (hT : PlusFourTrialityInput) :
    GGAutModelAt .POmegaPlus :=
  ggAutModelAt_POmegaPlus_of_four (plusFourInput_of_triality hT)

theorem ggAutStructureAt_POmegaPlus_of_triality (hT : PlusFourTrialityInput) :
    GGAutStructureAt .POmegaPlus :=
  ggAutStructureAt_of_autModelAt (ggAutModelAt_POmegaPlus_of_triality hT)

end Family

end CFSG.StandardType
