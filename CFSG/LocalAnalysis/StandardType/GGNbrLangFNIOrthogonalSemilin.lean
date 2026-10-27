module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEndMat
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorSemilin
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorFix
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.StandardType

open CFSG.Assembly QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.AUTSL
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthComm
  CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCPrimary
  CFSG.StandardType.RecipeFieldOmega
  CFSG.SeitzReduction
  CFSG.RankThree.Classical2
  Polynomial

structure SemilinearRepresentative {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (p : ℕ) where
  gamma : matrixDerived Q
  g : similarityPairs Q
  gamma_pow : gamma ^ p = 1
  isIsoPair : IsIsoPair Q g.val
  field_order : orderOf g.val.right = p
  pair_comm : ∀ v : Fin d → K,
    pairMap Q g (matrixLinearEquiv gamma.val v) =
      matrixLinearEquiv gamma.val (pairMap Q g v)

theorem exists_conj_pow_eq_one_of_mem_innSet {R Γ : Type} [Group R] [Group Γ]
    (Θ : R ≃* Γ) {h : MulAut R} (hh : h ∈ LargeEvenInnSet R)
    (hZ : Subgroup.center Γ = ⊥) {p : ℕ} (hhp : h ^ p = 1) :
    ∃ γ : Γ, MulAut.congr Θ h = MulAut.conj γ ∧ γ ^ p = 1 := by
  obtain ⟨r, rfl⟩ := hh
  refine ⟨Θ r, CFSG.mulAut_congr_conj Θ r, ?_⟩
  have hconj : (MulAut.conj (Θ r)) ^ p = 1 := by
    rw [← CFSG.mulAut_congr_conj]
    rw [← map_pow, hhp, map_one]
  have hpow : MulAut.conj ((Θ r) ^ p) = 1 := by
    rw [map_pow]
    exact hconj
  exact OrthRest.conj_injective (R := Γ) hZ (by
    rw [hpow, map_one])

theorem conj_eq_self_of_commute_conj {Γ : Type} [Group Γ] {F : MulAut Γ} {γ : Γ}
    (hcomm : MulAut.conj γ * F = F * MulAut.conj γ)
    (hZ : Subgroup.center Γ = ⊥) : F γ = γ := by
  have hFH : F * MulAut.conj γ * F⁻¹ = MulAut.conj γ := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : MulAut.conj (F γ) = MulAut.conj γ := by
    calc
      MulAut.conj (F γ) = F * MulAut.conj γ * F⁻¹ :=
        (OrthRestOdd.conj_map_mulAut F γ).symm
      _ = MulAut.conj γ := hFH
  exact OrthRest.conj_injective (R := Γ) hZ hconj


theorem kappa_mk_eq_of_matrixDerivedConjugation_eq
    {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) {γ : matrixDerived Q}
    (h : matrixDerivedConjugation Q g γ = γ) :
    kappa Q g (QuotientGroup.mk (matrixDerivedEquiv Q γ)) =
      QuotientGroup.mk (matrixDerivedEquiv Q γ) := by
  change matrixProjEquiv Q (matrixProjectiveConjugationHom Q g
    ((matrixProjEquiv Q).symm (QuotientGroup.mk (matrixDerivedEquiv Q γ)))) =
      QuotientGroup.mk (matrixDerivedEquiv Q γ)
  have hsymm : (matrixProjEquiv Q).symm
      (QuotientGroup.mk (matrixDerivedEquiv Q γ)) = QuotientGroup.mk γ := by
    rw [← matrixProjEquiv_mk Q γ, MulEquiv.symm_apply_apply]
  rw [hsymm]
  change matrixProjEquiv Q (matrixProjectiveConjugation Q g
    (matrixProjectiveProjection Q γ)) = QuotientGroup.mk (matrixDerivedEquiv Q γ)
  rw [matrixProjectiveConjugation_mk, h]
  change matrixProjEquiv Q (QuotientGroup.mk γ) =
    QuotientGroup.mk (matrixDerivedEquiv Q γ)
  exact matrixProjEquiv_mk Q γ


theorem matrixDerivedEquiv_pow_eq_one {K : Type} [Field K] {d p : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {γ : matrixDerived Q} (h : γ ^ p = 1) :
    (matrixDerivedEquiv Q γ) ^ p = 1 := by
  rw [← map_pow, h, map_one]

theorem matrixDerivedEquiv_coe_pow_eq_one {K : Type} [Field K] {d p : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {γ : matrixDerived Q} (h : γ ^ p = 1) :
    ((matrixDerivedEquiv Q γ : orthDerived Q) :
      (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ p = 1 := by
  have hx : (matrixDerivedEquiv Q γ) ^ p = 1 := matrixDerivedEquiv_pow_eq_one h
  rw [← Subgroup.coe_pow, hx]
  rfl

theorem dvd_of_frobeniusEquiv_pow_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {e k : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e)
    (hk : (frobeniusEquiv K 2) ^ k = 1) : e ∣ k := by
  obtain ⟨σ₀, hσ₀, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two he hK
  have hσ₀φ : σ₀ = frobeniusEquiv K 2 := RingEquiv.ext fun a => by
    rw [hσ₀, frobeniusEquiv_apply, frobenius_def]
  rw [← hord, hσ₀φ]
  exact orderOf_dvd_of_pow_eq_one hk

namespace RecipeFieldOmega

theorem exists_plus_semilinear_representatives
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} (hm1 : 1 ≤ m) (hm4 : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {f h : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ LargeEvenMatFieldImage
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))
    (hford : orderOf f = p)
    (hh : h ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (hhp : h ^ p = 1) (hcomm : h * f = f * h) :
    ∃ (σ : K ≃+* K)
      (data : SemilinearRepresentative (coordinateQuadPlus m K) p),
      MulAut.congr (plusEquiv hm1) h = MulAut.conj data.gamma ∧
      MulAut.congr (plusEquiv hm1) f = AutOm.fieldAutP m σ ∧
      data.g = CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
        (coordinateQuadPlus m K) σ (E7Pilot.coordinateQuadPlus_fieldMap m σ) ∧
      MulAut.congr (plusEquiv hm1) f =
        conjAct (coordinateQuadPlus m K) data.g ∧
      data.g.val.right = σ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hm3 : 3 ≤ m := by omega
  let Θ : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) ≃*
      matrixDerived (coordinateQuadPlus m K) := plusEquiv hm1
  obtain ⟨σ, hσF⟩ := congr_plusEquiv_of_mem_field hm1 hf
  have hnd : (coordinateQuadPlus m K).polarBilin.Nondegenerate :=
    (regular_coordinateQuadPlus m K hm3).1
  have hZ : Subgroup.center (matrixDerived (coordinateQuadPlus m K)) = ⊥ :=
    OrthRestOdd.center_matrixDerived_eq_bot hnd (by omega : 8 ≤ 2 * m)
  obtain ⟨γ, hγ, hγp⟩ :=
    exists_conj_pow_eq_one_of_mem_innSet Θ hh hZ hhp
  let g : similarityPairs (coordinateQuadPlus m K) :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair (coordinateQuadPlus m K) σ
      (E7Pilot.coordinateQuadPlus_fieldMap m σ)
  have hFg : MulAut.congr Θ f = conjAct (coordinateQuadPlus m K) g := by
    rw [hσF]
    exact AutOm.fieldAutP_apply m σ
  have hS : IsIsoPair (coordinateQuadPlus m K) g.val := fun v => by
    have hmap : coordinateSemilinearMap g.val v = coordinateFieldMap (2 * m) σ v :=
      AutOm.coordinateSemilinearMap_fieldPair (K := K) (n := m) σ v
    rw [hmap]
    exact E7Pilot.coordinateQuadPlus_fieldMap m σ v
  have hFp : (MulAut.congr Θ f) ^ p = 1 := by
    have hordF : orderOf (MulAut.congr Θ f) = p := by
      rw [(MulAut.congr Θ).orderOf_eq f, hford]
    rw [← hordF]
    exact pow_orderOf_eq_one (MulAut.congr Θ f)
  have hσp : σ ^ p = 1 := by
    have h1 : AutOm.fieldAutP m (σ ^ p) = 1 := by
      rw [map_pow, ← hσF]
      exact hFp
    exact AutOm.eq_one_of_fieldAutP_eq_one hm3 h1
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hF1 : MulAut.congr Θ f = 1 := by
      rw [hσF, h1, map_one]
    have hord1 : orderOf (MulAut.congr Θ f) = 1 := by
      rw [hF1, orderOf_one]
    have hordF : orderOf (MulAut.congr Θ f) = p := by
      rw [(MulAut.congr Θ).orderOf_eq f, hford]
    exact hp.ne_one (hordF.symm.trans hord1)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hcomm' : MulAut.conj γ * conjAct (coordinateQuadPlus m K) g =
      conjAct (coordinateQuadPlus m K) g * MulAut.conj γ := by
    rw [← hγ, ← hFg, ← map_mul, ← map_mul, hcomm]
  have hFγ : conjAct (coordinateQuadPlus m K) g γ = γ :=
    conj_eq_self_of_commute_conj hcomm' hZ
  have hconjγ : matrixDerivedConjugation (coordinateQuadPlus m K) g γ = γ := by
    rw [← conjAct_apply, hFγ]
  have hfix : kappa (coordinateQuadPlus m K) g
      (QuotientGroup.mk (matrixDerivedEquiv (coordinateQuadPlus m K) γ)) =
      QuotientGroup.mk (matrixDerivedEquiv (coordinateQuadPlus m K) γ) :=
    kappa_mk_eq_of_matrixDerivedConjugation_eq (coordinateQuadPlus m K) g hconjγ
  have hxp : ((matrixDerivedEquiv (coordinateQuadPlus m K) γ : orthDerived
      (coordinateQuadPlus m K)) : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) ^ p = 1 :=
    matrixDerivedEquiv_coe_pow_eq_one hγp
  have hQ0 : ∃ v : Fin (2 * m) → K, coordinateQuadPlus m K v ≠ 0 :=
    ⟨OmegaPilot.plusUnitVector hm1, AutOm.plusUnitVector_form_ne_zero hm1⟩
  have hpair : ∀ v : Fin (2 * m) → K,
      pairMap (coordinateQuadPlus m K) g (matrixLinearEquiv γ.val v) =
        matrixLinearEquiv γ.val (pairMap (coordinateQuadPlus m K) g v) := by
    intro v
    have h := pairMap_comm_of_fixes (Q := coordinateQuadPlus m K)
      (hp := hp.odd_of_ne_two hp2) hxp hQ0 g hfix v
    simpa [coe_matrixDerivedEquiv] using h
  have hgright : g.val.right = σ :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_right
      (coordinateQuadPlus m K) σ (E7Pilot.coordinateQuadPlus_fieldMap m σ)
  have hgdef : g = CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
      (coordinateQuadPlus m K) σ (E7Pilot.coordinateQuadPlus_fieldMap m σ) := rfl
  exact ⟨σ, ⟨γ, g, hγp, hS, hσord, hpair⟩, hγ, hσF, hgdef, hFg, hgright⟩

theorem exists_minus_semilinear_representatives
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n e p : ℕ} (hn4 : 4 ≤ n) (hn1 : 1 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2)
    {f h : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))}
    (hf : f ∈ LargeEvenPhiQ (n - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))))
    (hford : orderOf f = p)
    (hh : h ∈ LargeEvenInnSet
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))))
    (hhp : h ^ p = 1) (hcomm : h * f = f * h) :
    ∃ (k : ℕ)
      (data : SemilinearRepresentative (coordinateQuadMinus n K hn1 b c) p),
      MulAut.congr (minusEquiv hn4 b c) h = MulAut.conj data.gamma ∧
      MulAut.congr (minusEquiv hn4 b c) f = AutOm.frobAut hn4 hirr ^ k ∧
      data.g = (frobPair n hn1 b c
        (ne_zero_of_irreducible_tail b c hirr)) ^ k ∧
      MulAut.congr (minusEquiv hn4 b c) f = conjAct (coordinateQuadMinus n K hn1 b c) data.g ∧
      data.g.val.right = frobeniusEquiv K 2 ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hb : b ≠ 0 := ne_zero_of_irreducible_tail b c hirr
  let Θ : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)) ≃*
      matrixDerived (coordinateQuadMinus n K hn1 b c) := minusEquiv hn4 b c
  obtain ⟨k, hF⟩ := congr_minusEquiv_of_mem_phi hn4 hirr hf
  have hnd : (coordinateQuadMinus n K hn1 b c).polarBilin.Nondegenerate :=
    (regular_coordinateQuadMinus n K b c hn4 hirr).1
  have hT3 : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadMinus n K hn1 b c x = 0 :=
    (regular_coordinateQuadMinus n K b c hn4 hirr).2
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  have hZ : Subgroup.center (matrixDerived (coordinateQuadMinus n K hn1 b c)) = ⊥ :=
    OrthRestOdd.center_matrixDerived_eq_bot hnd (by omega : 8 ≤ 2 * n)
  obtain ⟨γ, hγ, hγp⟩ :=
    exists_conj_pow_eq_one_of_mem_innSet Θ hh hZ hhp
  let g : similarityPairs (coordinateQuadMinus n K hn1 b c) :=
    (frobPair n hn1 b c hb) ^ k
  have hτS : AutOm.frobAut hn4 hirr ^ k = conjAct (coordinateQuadMinus n K hn1 b c) g := by
    change (conjAct (coordinateQuadMinus n K hn1 b c)
      (frobPair n hn1 b c hb)) ^ k =
      conjAct (coordinateQuadMinus n K hn1 b c) ((frobPair n hn1 b c hb) ^ k)
    rw [map_pow]
  have hFg : MulAut.congr Θ f = conjAct (coordinateQuadMinus n K hn1 b c) g := hF.trans hτS
  have hS : IsIsoPair (coordinateQuadMinus n K hn1 b c) g.val := by
    rw [SubmonoidClass.coe_pow]
    exact (isIsoPair_frobPair hn1 hb).pow k
  have hσeq : g.val.right = frobeniusEquiv K 2 ^ k :=
    frobPair_pow_right hn1 hb k
  have hFp : (MulAut.congr Θ f) ^ p = 1 := by
    have hordF : orderOf (MulAut.congr Θ f) = p := by
      rw [(MulAut.congr Θ).orderOf_eq f, hford]
    rw [← hordF]
    exact pow_orderOf_eq_one (MulAut.congr Θ f)
  have hconj_pow : (conjAct (coordinateQuadMinus n K hn1 b c) g) ^ p = 1 := by
    rw [← hFg]
    exact hFp
  have hgp : g ^ p = 1 := by
    have hSp : IsIsoPair (coordinateQuadMinus n K hn1 b c) (g ^ p).val := by
      rw [SubmonoidClass.coe_pow]
      exact hS.pow p
    refine eq_one_of_conjAct_eq_one hnd hT3 hAP
      ⟨AutOm.tailVec n hn1, AutOm.tailVec_form_ne_zero n hn1 b c⟩ hSp ?_
    rw [map_pow]
    exact hconj_pow
  have hσp : g.val.right ^ p = 1 := by
    rw [← fieldProjection_apply (coordinateQuadMinus n K hn1 b c) g, ← map_pow, hgp, map_one]
  have hσ1 : g.val.right ≠ 1 := by
    intro h1
    have hφk : (frobeniusEquiv K 2) ^ k = 1 := hσeq.symm.trans h1
    have hfk : e ∣ k := dvd_of_frobeniusEquiv_pow_eq_one he hK hφk
    obtain ⟨m, rfl⟩ := hfk
    have hτ2 : (AutOm.frobAut hn4 hirr ^ e) ^ 2 = 1 :=
      AutOm.frobAut_pow_f_sq (n := n) (hn4 := hn4) (hirr := hirr) (b := b) (c := c)
        (f := e) hK
    have hτk2 : (AutOm.frobAut hn4 hirr ^ (e * m)) ^ 2 = 1 := by
      calc
        (AutOm.frobAut hn4 hirr ^ (e * m)) ^ 2 =
            ((AutOm.frobAut hn4 hirr ^ e) ^ m) ^ 2 := by
          congr 1
          rw [← pow_mul]
        _ = ((AutOm.frobAut hn4 hirr ^ e) ^ 2) ^ m := pow_right_comm _ _ _
        _ = 1 := by rw [hτ2, one_pow]
    have hF2 : (MulAut.congr Θ f) ^ 2 = 1 := by
      rw [hF, hτk2]
    have hordF : orderOf (MulAut.congr Θ f) = p := by
      rw [(MulAut.congr Θ).orderOf_eq f, hford]
    have hp_dvd_two : p ∣ 2 := by
      rw [← hordF]
      exact orderOf_dvd_of_pow_eq_one hF2
    have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_two
    have hp_ge_two : 2 ≤ p := hp.two_le
    exact hp2 (by omega : p = 2)
  have hσord : orderOf g.val.right = p := orderOf_eq_prime hσp hσ1
  have hcomm' : MulAut.conj γ * conjAct (coordinateQuadMinus n K hn1 b c) g =
      conjAct (coordinateQuadMinus n K hn1 b c) g * MulAut.conj γ := by
    rw [← hγ, ← hFg, ← map_mul, ← map_mul, hcomm]
  have hFγ : conjAct (coordinateQuadMinus n K hn1 b c) g γ = γ :=
    conj_eq_self_of_commute_conj hcomm' hZ
  have hconjγ : matrixDerivedConjugation (coordinateQuadMinus n K hn1 b c) g γ = γ := by
    rw [← conjAct_apply]
    exact hFγ
  have hfix : kappa (coordinateQuadMinus n K hn1 b c) g
      (QuotientGroup.mk (matrixDerivedEquiv (coordinateQuadMinus n K hn1 b c) γ)) =
      QuotientGroup.mk (matrixDerivedEquiv (coordinateQuadMinus n K hn1 b c) γ) :=
    kappa_mk_eq_of_matrixDerivedConjugation_eq
      (coordinateQuadMinus n K hn1 b c) g hconjγ
  have hxp : ((matrixDerivedEquiv (coordinateQuadMinus n K hn1 b c) γ : orthDerived
      (coordinateQuadMinus n K hn1 b c)) : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ^ p = 1 :=
    matrixDerivedEquiv_coe_pow_eq_one hγp
  have hpair : ∀ v : Fin (2 * n) → K,
      pairMap (coordinateQuadMinus n K hn1 b c) g (matrixLinearEquiv γ.val v) =
        matrixLinearEquiv γ.val (pairMap (coordinateQuadMinus n K hn1 b c) g v) := by
    intro v
    have h := pairMap_comm_of_fixes (Q := coordinateQuadMinus n K hn1 b c)
      (hp := hp.odd_of_ne_two hp2) hxp
      ⟨AutOm.tailVec n hn1, AutOm.tailVec_form_ne_zero n hn1 b c⟩ g hfix v
    simpa [coe_matrixDerivedEquiv] using h
  exact ⟨k, ⟨γ, g, hγp, hS, hσord, hpair⟩, hγ, hF, rfl, hFg, hσeq⟩

theorem primaryFactors_map_right_eq_self
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (data : SemilinearRepresentative Q p) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ a ∈ primaryFactors (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K)),
      a.map (data.g.val.right : K →+* K) = a := by
  classical
  have hpK : (p : K) ≠ 0 := OrthRestOdd.natCast_ne_zero_of_odd hp hp2
  have hσp : data.g.val.right ^ p = 1 := by
    simpa [data.field_order] using pow_orderOf_eq_one data.g.val.right
  have hxp : (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K)) ^ p = 1 := by
    have hx : (matrixDerivedEquiv Q data.gamma) ^ p = 1 := by
      rw [← map_pow, data.gamma_pow, map_one]
    have hcoe : ((matrixDerivedEquiv Q data.gamma : orthDerived Q) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hx]
      rfl
    have hcoeLin : ((matrixLinearEquiv data.gamma.val :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ p) = 1 := by
      simpa [coe_matrixDerivedEquiv] using hcoe
    have hpow := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := K) (M := Fin d → K)) (matrixLinearEquiv data.gamma.val) p
    rw [hcoeLin] at hpow
    simpa [Module.End.one_eq_id] using hpow.symm
  have hsq : Squarefree (minpoly K
      (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K))) :=
    CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one hpK hxp
  have hmin : (minpoly K
      (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K))).map
      (data.g.val.right : K →+* K) =
      minpoly K (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K)) := by
    refine CFSG.RankThree.PartOne.KCOrthComm.map_minpoly_eq
      (F := pairMap Q data.g) (σ := data.g.val.right) ?_ ?_
    · intro c v
      exact pairMap_smul Q data.g c v
    · intro v
      exact data.pair_comm v
  intro a ha
  exact CFSG.RankThree.PartOne.KCOrthComm.map_eq_self_of_pow_eq_one (x :=
    (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K))) hp hsq hxp
    (j := 1) (by simpa using hσp) hmin ha

end RecipeFieldOmega

end CFSG.StandardType

end
