module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusOTwo
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.LieType.Universal.Spin.Twisted.Datum

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms QuadraticMap

namespace OrdPGraphOmega

section Coords

variable {K : Type} [Field K] {n : ℕ} {b c : K}

noncomputable abbrev mvec (hn : 1 ≤ n) (k : Fin (n - 1)) (r : Bool) : Fin (2 * n) → K :=
  reindexVectorEquiv (minusIndexEquiv n hn) (minusVec n k r)

noncomputable abbrev mplane (hn : 1 ≤ n) (p : Fin 2 → K) : Fin (2 * n) → K :=
  reindexVectorEquiv (minusIndexEquiv n hn) (planeVec n p)

theorem reindex_apply_equiv {ι : Type} {d : ℕ} (e : ι ≃ Fin d) (v : ι → K) (y : ι) :
    reindexVectorEquiv (K := K) e v (e y) = v y := by
  rw [reindexVectorEquiv_apply, Equiv.symm_apply_apply]

theorem form_reindex_minus (hn : 1 ≤ n) (y : Vm n K) :
    coordinateQuadMinus n K hn b c (reindexVectorEquiv (minusIndexEquiv n hn) y) =
      quadMinus n K b c y :=
  reindexQuadraticForm_map _ _ _

theorem polar_reindex_minus (hn : 1 ≤ n) (y z : Vm n K) :
    polar (coordinateQuadMinus n K hn b c) (reindexVectorEquiv (minusIndexEquiv n hn) y)
        (reindexVectorEquiv (minusIndexEquiv n hn) z) = polar (quadMinus n K b c) y z := by
  simp only [polar, ← map_add, form_reindex_minus]

theorem eichlerC_reindex_minus (hn : 1 ≤ n) (u w y : Vm n K) :
    AutOm.eichlerC (coordinateQuadMinus n K hn b c) (reindexVectorEquiv (minusIndexEquiv n hn) u)
        (reindexVectorEquiv (minusIndexEquiv n hn) w)
        (reindexVectorEquiv (minusIndexEquiv n hn) y) =
      reindexVectorEquiv (minusIndexEquiv n hn)
        (y + polar (quadMinus n K b c) y u • w - polar (quadMinus n K b c) y w • u -
          (quadMinus n K b c w * polar (quadMinus n K b c) y u) • u) := by
  rw [AutOm.eichlerC, polar_reindex_minus, polar_reindex_minus, form_reindex_minus, map_sub,
    map_sub, map_add, LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul]

variable [Finite K]

theorem spinModelMinus_longRoot_eichler (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K) (y : Fin (2 * n) → K) :
    Matrix.mulVec ((AutOm.spinModelMinus hn4 hirr ((minusFrame n b c).longRoot hij s t (.ofAdd a)) :
        GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) y =
      AutOm.eichlerC (coordinateQuadMinus n K (by omega) b c) (mvec (by omega) j t)
        (a • mvec (by omega) i s) y := by
  obtain ⟨y', rfl⟩ := (reindexVectorEquiv (K := K) (minusIndexEquiv n (by omega))).surjective y
  rw [AutOm.spinModelMinus_mulVec, HypFrame.spinAction_longRoot, ← LinearEquiv.map_smul,
    eichlerC_reindex_minus]
  congr 1
  rw [minusFrame_vec, polar_smul_right, QuadraticMap.map_smul, quadMinus_minusVec]
  simp only [smul_eq_mul, mul_zero, zero_mul, zero_smul, sub_zero]
  module

theorem spinModelMinus_shortRoot_eichler (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) (y : Fin (2 * n) → K) :
    Matrix.mulVec ((AutOm.spinModelMinus hn4 hirr (twShortRoot n hirr i s (.ofAdd p)) :
        GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) y =
      AutOm.eichlerC (coordinateQuadMinus n K (by omega) b c) (mvec (by omega) i s)
        (mplane (by omega) p) y := by
  obtain ⟨y', rfl⟩ := (reindexVectorEquiv (K := K) (minusIndexEquiv n (by omega))).surjective y
  rw [AutOm.spinModelMinus_mulVec, spinAction_twShortRoot, eichlerC_reindex_minus,
    quadMinus_planeVec']

end Coords

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

theorem frobPair_form (hn : 1 ≤ n) (hb : b ≠ 0) (y : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c (coordinateSemilinearMap (frobPair n hn b c hb).val y) =
      (frobPair n hn b c hb).val.right (coordinateQuadMinus n K hn b c y) := by
  change coordinateQuadMinus n K hn b c (coordinateSemilinearMap (frobElt n hn b c hb) y) =
    frobeniusEquiv K 2 (coordinateQuadMinus n K hn b c y)
  rw [frobElt_apply, form_tailLin_sq]
  rfl

theorem frob_single (hn : 1 ≤ n) (hb : b ≠ 0) {x : Fin (2 * n)} (h0 : x ≠ tailZero n hn)
    (h1 : x ≠ tailOne n hn) :
    coordinateSemilinearMap (frobPair n hn b c hb).val (Pi.single x 1) = Pi.single x 1 := by
  change coordinateSemilinearMap (frobElt n hn b c hb) _ = _
  rw [frobElt_apply]
  have hsq : (fun i => (Pi.single x (1 : K) : Fin (2 * n) → K) i ^ 2) = Pi.single x 1 := by
    funext i
    by_cases hi : i = x
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  rw [hsq]
  funext k
  by_cases hk0 : k = tailZero n hn
  · subst hk0
    rw [tailLin_zero, Pi.single_eq_of_ne (Ne.symm h0), Pi.single_eq_of_ne (Ne.symm h1), mul_zero,
      add_zero]
  · by_cases hk1 : k = tailOne n hn
    · subst hk1
      rw [tailLin_one, Pi.single_eq_of_ne (Ne.symm h1), mul_zero]
    · rw [tailLin_other n hn b c _ hk0 hk1]

theorem frob_mvec (hn : 1 ≤ n) (hb : b ≠ 0) (k : Fin (n - 1)) (r : Bool) :
    coordinateSemilinearMap (frobPair n hn b c hb).val (mvec hn k r) = mvec hn k r := by
  cases r
  · rw [mvec, minusVec_false, fVec, AutOm.reindex_single]
    exact frob_single hn hb (tailZero_ne_inr n hn k) (tailOne_ne_inr n hn k)
  · rw [mvec, minusVec_true, eVec, AutOm.reindex_single]
    exact frob_single hn hb (tailZero_ne_inl n hn k) (tailOne_ne_inl n hn k)

@[expose] def frobPlane (b c : K) (p : Fin 2 → K) : Fin 2 → K :=
  ![p 0 ^ 2 + c * p 1 ^ 2, b * p 1 ^ 2]

theorem frob_mplane (hn : 1 ≤ n) (hb : b ≠ 0) (p : Fin 2 → K) :
    coordinateSemilinearMap (frobPair n hn b c hb).val (mplane hn p) =
      mplane hn (frobPlane b c p) := by
  change coordinateSemilinearMap (frobElt n hn b c hb) _ = _
  rw [frobElt_apply]
  have h0 : ∀ (q : Fin 2 → K), mplane hn q (tailZero n hn) = q 0 := fun q => by
    rw [mplane, tailZero, reindex_apply_equiv]
    rfl
  have h1 : ∀ (q : Fin 2 → K), mplane hn q (tailOne n hn) = q 1 := fun q => by
    rw [mplane, tailOne, reindex_apply_equiv]
    rfl
  funext k
  by_cases hk0 : k = tailZero n hn
  · subst hk0
    rw [tailLin_zero, h0, h1, h0]
    rfl
  · by_cases hk1 : k = tailOne n hn
    · subst hk1
      rw [tailLin_one, h1, h1]
      rfl
    · rw [tailLin_other n hn b c _ hk0 hk1]
      obtain ⟨y, rfl⟩ := (minusIndexEquiv n hn).surjective k
      have hz : ∀ (q : Fin 2 → K), mplane hn q (minusIndexEquiv n hn y) = 0 := fun q => by
        rw [mplane, reindex_apply_equiv]
        rcases y with y | y | y
        · rfl
        · rfl
        · exfalso
          fin_cases y
          · exact hk0 rfl
          · exact hk1 rfl
      change mplane hn p (minusIndexEquiv n hn y) ^ 2 = _
      rw [hz, hz]
      simp

variable (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem frobAut_longRoot {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K) :
    AutOm.frobAut hn4 hirr
        (AutOm.spinModelMinus hn4 hirr ((minusFrame n b c).longRoot hij s t (.ofAdd a))) =
      AutOm.spinModelMinus hn4 hirr ((minusFrame n b c).longRoot hij s t (.ofAdd (a ^ 2))) := by
  have hb := ne_zero_of_irreducible_tail b c hirr
  refine AutOm.conjAct_eichler_eq _ (frobPair_form (by omega) hb) _ _
    (spinModelMinus_longRoot_eichler hn4 hirr hij s t a)
    (spinModelMinus_longRoot_eichler hn4 hirr hij s t (a ^ 2)) (frob_mvec (by omega) hb j t) ?_
  rw [coordinateSemilinearMap_smul, frob_mvec (by omega) hb i s]
  rfl

include hirr in
theorem frobAut_shortRoot (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    AutOm.frobAut hn4 hirr (AutOm.spinModelMinus hn4 hirr (twShortRoot n hirr i s (.ofAdd p))) =
      AutOm.spinModelMinus hn4 hirr (twShortRoot n hirr i s (.ofAdd (frobPlane b c p))) := by
  have hb := ne_zero_of_irreducible_tail b c hirr
  exact AutOm.conjAct_eichler_eq _ (frobPair_form (by omega) hb) _ _
    (spinModelMinus_shortRoot_eichler hn4 hirr i s p)
    (spinModelMinus_shortRoot_eichler hn4 hirr i s (frobPlane b c p)) (frob_mvec (by omega) hb i s)
    (frob_mplane (by omega) hb p)

include hirr in
theorem frobAut_mem_rootGroup {γ : Fin (minusDatum n hirr).rank → ℤ}
    (hγ : γ ∈ (minusDatum n hirr).roots) {x : spinGroup (quadMinus n K b c)}
    (hx : x ∈ (minusDatum n hirr).rootGroup γ) :
    ∃ x' ∈ (minusDatum n hirr).rootGroup γ,
      AutOm.frobAut hn4 hirr (AutOm.spinModelMinus hn4 hirr x) =
        AutOm.spinModelMinus hn4 hirr x' := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hst⟩ | ⟨i, s, hs⟩
  · obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hx
    exact ⟨_, longRoot_mem_minusRootGroup n hirr hij s t hst (a ^ 2),
      frobAut_longRoot hn4 hirr hij s t a⟩
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hs).mp hx
    exact ⟨_, twShortRoot_mem_minusRootGroup n hirr i s hs (frobPlane b c p),
      frobAut_shortRoot hn4 hirr i s p⟩

include hirr in
theorem frobAut_pow_mem_rootGroup {γ : Fin (minusDatum n hirr).rank → ℤ}
    (hγ : γ ∈ (minusDatum n hirr).roots) (k : ℕ) {x : spinGroup (quadMinus n K b c)}
    (hx : x ∈ (minusDatum n hirr).rootGroup γ) :
    ∃ x' ∈ (minusDatum n hirr).rootGroup γ,
      (AutOm.frobAut hn4 hirr ^ k) (AutOm.spinModelMinus hn4 hirr x) =
        AutOm.spinModelMinus hn4 hirr x' := by
  induction k with
  | zero => exact ⟨x, hx, rfl⟩
  | succ k ih =>
    obtain ⟨x', hx', e⟩ := ih
    obtain ⟨x'', hx'', e'⟩ := frobAut_mem_rootGroup hn4 hirr hγ hx'
    exact ⟨x'', hx'', by rw [pow_succ', MulAut.mul_apply, e, e']⟩

include hirr in
theorem modelDiagField_minus {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (β : MulAut (matrixDerived (coordinateQuadMinus n K (by omega) b c))) :
    OrdPGraph.ModelDiagField (minusDatum n hirr) (AutOm.spinModelMinus hn4 hirr) β := by
  obtain ⟨_, ⟨h, rfl⟩, k, rfl⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf β
  refine ⟨h, fun γ hγ z hz => ?_⟩
  obtain ⟨z', hz', e⟩ := frobAut_pow_mem_rootGroup hn4 hirr hγ k hz
  refine ⟨z', hz', ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, e]
  group

end Frob

end OrdPGraphOmega

section Family

theorem ggOrdPGraphModelAt_POmegaMinus : GGOrdPGraphModelAt .POmegaMinus := by
  intro n f hadm _
  obtain ⟨-, hf, hn4⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hirr := minusCoeffs_irr 2 f
  exact ⟨matrixDerived (Qm n hn4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2), inferInstance,
    AutOm.spinModelMinus hn4 hirr, AutOm.spinModelMinus_surjective hn4 hirr,
    AutOm.ker_spinModelMinus hn4 hirr,
    fun _ _ _ _ β _ => OrdPGraphOmega.modelDiagField_minus hn4 hirr hK β⟩

theorem ggOrdPGraphAt_POmegaMinus : GGOrdPGraphAt .POmegaMinus :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_POmegaMinus

end Family

end CFSG.StandardType
