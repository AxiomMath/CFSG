module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusOmegaMinus8
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusTorus
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusOTwo
import CFSG.GroupTheory.SylowAutConj
import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.RankThree.PartOne.AUTSL
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private noncomputable def minusDerivedEquiv :
    StatedOmega (StatedQuadMinus 4 K b c) ≃*
      matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c) :=
  statedDerivedReindexEquiv (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 K b c)
    (coe_quadMinus 4 K b c)

private theorem frobPair_semilinear_commutes_diagonal (hb : b ≠ 0)
    (d : Fin 3 → Kˣ) (v : Fin 8 → K) :
    coordinateSemilinearMap (frobPair 4 (by norm_num) b c hb).val
      ((reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num))
        (diagGL (torusEntMinus 3 K d))).val *ᵥ v) =
      (reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num))
        (diagGL (torusEntMinus 3 K (fun i => d i ^ 2)))).val *ᵥ
          coordinateSemilinearMap (frobPair 4 (by norm_num) b c hb).val v := by
  have hdiag : ∀ d : Fin 3 → Kˣ, ∀ v : Fin 8 → K, ∀ i : Fin 8,
      ((reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num))
        (diagGL (torusEntMinus 3 K d))).val *ᵥ v) i =
        (torusEntMinus 3 K d ((minusIndexEquiv 4 (by norm_num)).symm i) : K) * v i := by
    intro d v i
    rw [reindexMatrixEquiv_val, coe_diagGL]
    have hd : Matrix.reindex (minusIndexEquiv 4 (by norm_num)) (minusIndexEquiv 4 (by norm_num))
        (Matrix.diagonal (fun j => (torusEntMinus 3 K d j : K))) =
        Matrix.diagonal (fun j =>
          (torusEntMinus 3 K d ((minusIndexEquiv 4 (by norm_num)).symm j) : K)) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp [Matrix.reindex_apply]
      · simp [Matrix.reindex_apply, h, (minusIndexEquiv 4 (by norm_num)).symm.injective.ne h]
    rw [hd]
    rw [Matrix.mulVec_diagonal]
  funext i
  have hF : ∀ w : Fin 8 → K, coordinateSemilinearMap (frobPair 4 (by norm_num) b c hb).val w =
      tailLin 4 (by norm_num) b c (fun k => w k ^ 2) := fun w =>
    frobElt_apply 4 (by norm_num) b c hb w
  rw [hF, hF]
  rw [hdiag]
  have hv0 : ∀ k, ((reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num))
      (diagGL (torusEntMinus 3 K d))).val *ᵥ v) k =
      (torusEntMinus 3 K d ((minusIndexEquiv 4 (by norm_num)).symm k) : K) * v k :=
    hdiag d v
  obtain ⟨j, rfl⟩ := (minusIndexEquiv 4 (by norm_num)).surjective i
  rcases j with j | j | j
  · rw [tailLin_other 4 (by norm_num) b c _
      (tailZero_ne_inl 4 (by norm_num) j) (tailOne_ne_inl 4 (by norm_num) j),
      tailLin_other 4 (by norm_num) b c _
      (tailZero_ne_inl 4 (by norm_num) j) (tailOne_ne_inl 4 (by norm_num) j), hdiag]
    simp [torusEntMinus, mul_pow]
  · rw [tailLin_other 4 (by norm_num) b c _
      (tailZero_ne_inr 4 (by norm_num) j) (tailOne_ne_inr 4 (by norm_num) j),
      tailLin_other 4 (by norm_num) b c _
      (tailZero_ne_inr 4 (by norm_num) j) (tailOne_ne_inr 4 (by norm_num) j), hdiag]
    simp [torusEntMinus, mul_pow]
  · fin_cases j
    · simp only [Equiv.symm_apply_apply]
      change tailLin 4 (by norm_num) b c _ (tailZero 4 (by norm_num)) =
        (1 : K) * tailLin 4 (by norm_num) b c (fun k => v k ^ 2) (tailZero 4 (by norm_num))
      rw [tailLin_zero, tailLin_zero, hv0, hv0]
      simp [torusEntMinus, tailZero, tailOne]
    · simp only [Equiv.symm_apply_apply]
      change tailLin 4 (by norm_num) b c _ (tailOne 4 (by norm_num)) =
        (1 : K) * tailLin 4 (by norm_num) b c (fun k => v k ^ 2) (tailOne 4 (by norm_num))
      rw [tailLin_one, tailLin_one, hv0]
      simp [torusEntMinus, tailOne]

private noncomputable def minusTorusHom : (Fin 3 → Kˣ) →*
    matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c) :=
  minusDerivedEquiv.toMonoidHom.comp
    ((CFSG.SeitzReduction.F4Pilot.diagOmegaMinus K).codRestrict
      (StatedOmega (StatedQuadMinus 4 K b c))
      (CFSG.SeitzReduction.F4Pilot.diagOmegaMinus_mem b c))

private theorem minusTorusHom_val (d : Fin 3 → Kˣ) :
    (minusTorusHom (b := b) (c := c) d).val =
      reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num)) (diagGL (torusEntMinus 3 K d)) := by
  change (minusDerivedEquiv (b := b) (c := c)
    ⟨CFSG.SeitzReduction.F4Pilot.diagOmegaMinus K d, _⟩).val = _
  have h := statedDerivedReindexEquiv_val (minusIndexEquiv 4 (by norm_num))
    (quadMinus 4 K b c) (coe_quadMinus 4 K b c)
    ⟨CFSG.SeitzReduction.F4Pilot.diagOmegaMinus K d,
      CFSG.SeitzReduction.F4Pilot.diagOmegaMinus_mem b c d⟩
  convert h using 1
  · rfl
  · apply congrArg (reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num)))
    apply Units.ext
    rw [CFSG.SeitzReduction.F4Pilot.diagOmegaMinus_coe, coe_diagGL]
    congr 1
    funext i
    rcases i with i | i | i <;> rfl

private theorem minusTorusHom_injective :
    Function.Injective (minusTorusHom (b := b) (c := c)) := by
  intro s t h
  have h' := congrArg Subtype.val h
  rw [minusTorusHom_val, minusTorusHom_val] at h'
  have hd := (reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num))).injective h'
  have ht : torusEntMinus 3 K s = torusEntMinus 3 K t := by
    funext j
    apply Units.ext
    have hj := congrArg (fun g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K => g.val j j) hd
    simpa only [coe_diagGL, Matrix.diagonal_apply_eq] using hj
  funext i
  have hi := congrFun ht (Sum.inl i)
  simpa [torusEntMinus] using hi

private theorem frobAut_minusTorusHom
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (d : Fin 3 → Kˣ) :
    CFSG.StandardType.AutOm.frobAut (by norm_num : 4 ≤ 4) hirr
      (minusTorusHom d) = minusTorusHom (fun i => d i ^ 2) := by
  apply CFSG.StandardType.AutOm.conjAct_apply_eq_of
  intro v
  rw [minusTorusHom_val, minusTorusHom_val]
  exact frobPair_semilinear_commutes_diagonal
    (ne_zero_of_irreducible_tail b c hirr) d v

private theorem frobAut_pow_minusTorusHom
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (j : ℕ) (d : Fin 3 → Kˣ) :
    (CFSG.StandardType.AutOm.frobAut (by norm_num : 4 ≤ 4) hirr ^ j)
      (minusTorusHom d) = minusTorusHom (d ^ (2 ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih, frobAut_minusTorusHom]
    congr 1
    funext i
    change (d i ^ (2 ^ j)) ^ 2 = d i ^ (2 ^ (j + 1))
    rw [← pow_mul, pow_succ]

theorem sylow_torsion_fixed_statedOmegaMinus_four
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hr : r.Prime) (hr7 : 7 ≤ r)
    (hrq : r ∣ 2 ^ f - 1)
    (R : Sylow r (StatedOmega (StatedQuadMinus 4 K b c)))
    (α : MulAut (StatedOmega (StatedQuadMinus 4 K b c)))
    (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαR : ∀ x ∈ (R : Subgroup (StatedOmega (StatedQuadMinus 4 K b c))),
      α x ∈ (R : Subgroup (StatedOmega (StatedQuadMinus 4 K b c)))) :
    ∀ x ∈ (R : Subgroup (StatedOmega (StatedQuadMinus 4 K b c))),
      x ^ r = 1 → α x = x := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  let X := matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c)
  let T : (Fin 3 → Kˣ) →* X := minusTorusHom (b := b) (c := c)
  have hTi : Function.Injective T := minusTorusHom_injective
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hrqK : r ∣ Nat.card K - 1 := by rwa [hK]
  let a := (Nat.card K - 1).factorization r
  have hra : r ^ a ∣ Nat.card K - 1 :=
    (hr.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have huord : orderOf u = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]
  let ζ : Kˣ := u ^ (orderOf u / r ^ a)
  have hζ : orderOf ζ = r ^ a :=
    orderOf_pow_orderOf_div (orderOf_pos u).ne' (by rw [huord]; exact hra)
  let H : Subgroup (Fin 3 → Kˣ) := Subgroup.pi Set.univ (fun _ => zpowers ζ)
  let S₀ : Subgroup X := H.map T
  have hS₀card : Nat.card S₀ = r ^ (3 * a) := by
    rw [Subgroup.card_map_of_injective hTi]
    have hc := card_pi_ite_zpowers (k := K) 3 ζ Finset.univ
    have hc' : Nat.card H = orderOf ζ ^ 3 := by simpa [H] using hc
    rw [hc', hζ, ← pow_mul, mul_comm]
  have hS₀ : IsPGroup r S₀ := IsPGroup.of_card hS₀card
  have hcardX : Nat.card X = Nat.card (StatedOmega (StatedQuadMinus 4 K b c)) :=
    (Nat.card_congr (minusDerivedEquiv (b := b) (c := c)).toEquiv).symm
  have hS₀i : ¬ r ∣ S₀.index := by
    apply CFSG.HardMathSupport.Timmesfeld.LinearRank.not_dvd_index_of_card_eq hr
    rw [hcardX,
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.factorization_card_statedOmega_quadMinus_four
        hirr hr (by omega) hrqK,
      hS₀card, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      hr.factorization_self, mul_one]
  have hS₀c : ∀ s ∈ S₀, ∀ t ∈ S₀, s * t = t * s := by
    rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩
    exact (map_mul T s t).symm.trans ((congrArg T (mul_comm s t)).trans (map_mul T t s))
  let Φ : MulAut X := CFSG.StandardType.AutOm.frobAut (by norm_num : 4 ≤ 4) hirr
  have hΦ : ∀ β : MulAut X, ∃ y : X, ∃ j : ℕ, β = MulAut.conj y * Φ ^ j := by
    intro β
    obtain ⟨ι, hι, j, hj⟩ :=
      CFSG.StandardType.AutOm.exists_inner_mul_frobAut_pow (by norm_num : 4 ≤ 4) hirr hK β
    obtain ⟨y, hy⟩ := hι
    exact ⟨y, j, by rw [← hy] at hj; exact hj⟩
  have hf : 2 * f ≠ 0 := by
    intro h
    have hf : f = 0 := by omega
    simp [hf] at hK
    omega
  obtain ⟨e, m, hm, hfm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hf r hr.ne_one
  have hφ : ∃ k : ℕ, (Φ ^ m) ^ (r ^ k) = 1 := by
    refine ⟨e, ?_⟩
    rw [← pow_mul, mul_comm m (r ^ e), ← hfm]
    exact CFSG.StandardType.AutOm.frobAut_pow_two_mul (by norm_num : 4 ≤ 4) hirr hK
  have hφi : ¬ r ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).index :=
    fun h => hm (h.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  have hfrob : frobeniusEquiv K 2 ^ (2 * f) = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have hff : frobeniusEquiv K 2 ^ f = 1 := by
      apply RingEquiv.ext
      intro x
      rw [frobeniusEquiv_pow_apply, ← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card x
    rw [pow_mul', hff, one_pow]
  have hσ : (frobeniusEquiv K 2 ^ m) ^ (r ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hfm, hfrob]
  have hφfix : ∀ x ∈ S₀, x ^ r = 1 → (Φ ^ m) x = x := by
    rintro _ ⟨t, -, rfl⟩ htr
    have ht : t ^ r = 1 := hTi (by rwa [map_pow, map_one])
    change (CFSG.StandardType.AutOm.frobAut (by norm_num : 4 ≤ 4) hirr ^ m)
      (minusTorusHom t) = minusTorusHom t
    rw [frobAut_pow_minusTorusHom]
    congr 1
    funext i
    apply Units.ext
    have hti : (t i : K) ^ r = 1 := by
      simpa using congrArg (fun s : Fin 3 → Kˣ => (s i : K)) ht
    simpa only [Pi.pow_apply, Units.val_pow_eq_pow_val, frobeniusEquiv_pow_apply] using
      CFSG.StandardType.fieldAut_fixes_pow_eq_one hr hσ hti
  have hφS : ∀ s ∈ S₀, (Φ ^ m) s ∈ S₀ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [show (Φ ^ m) (T t) = T (t ^ (2 ^ m)) from frobAut_pow_minusTorusHom hirr m t]
    exact mem_map_of_mem _ (H.pow_mem ht _)
  let eX := minusDerivedEquiv (b := b) (c := c)
  let R' : Sylow r X := R.mapSurjective (f := eX.toMonoidHom) eX.surjective
  have hR' : (R' : Subgroup X) = (R : Subgroup _).map eX.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eX.toMonoidHom) eX.surjective R
  have hα' : ∃ k : ℕ, (MulAut.congr eX α) ^ (r ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hαR' : ∀ y ∈ (R' : Subgroup X), MulAut.congr eX α y ∈ (R' : Subgroup X) := by
    intro y hy
    rw [hR'] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using mem_map_of_mem eX.toMonoidHom (hαR x hx)
  intro x hx hxr
  apply eX.injective
  simpa using CFSG.apply_eq_self_of_pow_eq_one hS₀ hS₀i hS₀c hφ hφS hφi hφfix
    R'.isPGroup' R'.not_dvd_index hα' hαR'
    (eX x) (by rw [hR']; exact mem_map_of_mem _ hx) (by rw [← map_pow, hxr, map_one])

theorem sylow_torsion_fixed_of_isOmega8m
    {X : Type} [Group X] [Finite X] {f r : ℕ}
    (hX : IsOmega8m X f) (hr : r.Prime) (hr7 : 7 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) (R : Sylow r X) (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαR : ∀ x ∈ (R : Subgroup X), α x ∈ (R : Subgroup X)) :
    ∀ x ∈ (R : Subgroup X), x ^ r = 1 → α x = x := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, K, hF, hFin, hK, b, c, hirr, ⟨e⟩⟩ :=
    hX.statedClassicalModel (by decide)
  let := hF
  let := hFin
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hbot : (StatedScalars (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus 4 K b c) (coe_quadMinus 4 K b c)
      ⟨_, by rw [quadMinus_minusFlipVec (n := 4) ⟨0, by norm_num⟩]; exact one_ne_zero⟩
  let eProj : StatedOmega (StatedQuadMinus 4 K b c) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) :=
    CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot
  let eX : X ≃* StatedOmega (StatedQuadMinus 4 K b c) := e.trans eProj.symm
  let R' : Sylow r (StatedOmega (StatedQuadMinus 4 K b c)) :=
    R.mapSurjective (f := eX.toMonoidHom) eX.surjective
  have hR' : (R' : Subgroup _) = (R : Subgroup X).map eX.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eX.toMonoidHom) eX.surjective R
  have hα' : ∃ k : ℕ, (MulAut.congr eX α) ^ (r ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hαR' : ∀ y ∈ (R' : Subgroup _), MulAut.congr eX α y ∈ (R' : Subgroup _) := by
    intro y hy
    rw [hR'] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using mem_map_of_mem eX.toMonoidHom (hαR x hx)
  intro x hx hxr
  apply eX.injective
  simpa using sylow_torsion_fixed_statedOmegaMinus_four hirr hK hr hr7 hrq R'
    (MulAut.congr eX α) hα' hαR' (eX x)
    (by rw [hR']; exact mem_map_of_mem _ hx) (by rw [← map_pow, hxr, map_one])

end CFSG.LocalAnalysis.UniquenessCase.UC22
