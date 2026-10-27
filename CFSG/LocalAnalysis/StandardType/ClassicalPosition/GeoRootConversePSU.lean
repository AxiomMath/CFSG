module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.Timmesfeld.Transvection.PresSUModel
public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.LieEmbed.UnitaryIsometry
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.ClassicalInvolution.ModelFacts.MF15Skew
import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.ClassicalInvolution.ModelFacts.MF15Basic
public import CFSG.ClassicalInvolution.ModelFacts.MF15Lin
public import CFSG.ClassicalInvolution.ModelFacts.MF15One
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.Pres
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open Matrix

private theorem grcPSU_vecMul_single_rev {F : Type} [Field F] {n : ℕ} (a : Fin n) :
    Matrix.vecMul (Pi.single (Fin.rev a) (1 : F)) (Unitary.antidiag n) = Pi.single a 1 := by
  funext i
  simp only [CFSG.Timmesfeld.LieEmbed.vecMul_antidiag, Pi.single_apply, Fin.rev_inj]

private theorem grcPSU_pairGen_suElt {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    {A B : Fin (n / 2) ⊕ Fin (n / 2)} (hAB : idx A ≠ idx B) (c : F) :
    1 + c • Matrix.vecMulVec (Pi.single (crd A) (1 : F))
          (Matrix.vecMul (fun i => σ.toRingHom (((Pi.single (crd B) (1 : F)) : Fin n → F) i))
            (Unitary.antidiag n)) -
      σ.toRingHom c • Matrix.vecMulVec (Pi.single (crd B) (1 : F))
          (Matrix.vecMul (fun i => σ.toRingHom (((Pi.single (crd A) (1 : F)) : Fin n → F) i))
            (Unitary.antidiag n)) =
      mat σ n (suElt σ hσ A B c) := by
  have hσsingle : ∀ p : Fin n,
      (fun i => σ.toRingHom (((Pi.single p (1 : F)) : Fin n → F) i)) =
        ((Pi.single p (1 : F)) : Fin n → F) := by
    intro p
    funext i
    by_cases h : i = p
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hRv : ∀ p : Fin n, Matrix.vecMul (Pi.single p (1 : F)) (Unitary.antidiag n) =
      Pi.single (Fin.rev p) 1 := by
    intro p
    have h := grcPSU_vecMul_single_rev (F := F) (n := n) (Fin.rev p)
    simpa only [Fin.rev_rev] using h
  rw [hσsingle (crd B), hσsingle (crd A),
    show Matrix.vecMul (Pi.single (crd B) (1 : F)) (Unitary.antidiag n) =
      Pi.single (Fin.rev (crd B)) 1 from hRv (crd B),
    show Matrix.vecMul (Pi.single (crd A) (1 : F)) (Unitary.antidiag n) =
      Pi.single (Fin.rev (crd A)) 1 from hRv (crd A),
    ← crd_swap B, ← crd_swap A]
  have hvs : ∀ p q : Fin n,
      Matrix.vecMulVec (Pi.single p (1 : F)) (Pi.single q (1 : F)) =
        (Matrix.single p q (1 : F) : Matrix (Fin n) (Fin n) F) :=
    fun p q => (single_eq_single_vecMulVec_single p q).symm
  rw [hvs (crd A) (crd (Sum.swap B)), hvs (crd B) (crd (Sum.swap A))]
  rw [show c • (Matrix.single (crd A) (crd (Sum.swap B)) (1 : F) :
        Matrix (Fin n) (Fin n) F) = Matrix.single (crd A) (crd (Sum.swap B)) c from by
    ext x y; by_cases hx : x = crd A <;> by_cases hy : y = crd (Sum.swap B) <;>
      simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, hx, hy, eq_comm]]
  rw [show σ.toRingHom c • (Matrix.single (crd B) (crd (Sum.swap A)) (1 : F) :
        Matrix (Fin n) (Fin n) F) = Matrix.single (crd B) (crd (Sum.swap A)) (σ c) from by
    ext x y; by_cases hx : x = crd B <;> by_cases hy : y = crd (Sum.swap A) <;>
      simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, hx, hy, eq_comm]]
  rw [mat_suElt hσ hAB c]

private theorem grcPSU_rootGroup_map_subtype_short {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    {A B : Fin (n / 2) ⊕ Fin (n / 2)} (hAB : idx A ≠ idx B) {γ : Fin (n / 2) → ℤ}
    (hγ : toStd n γ = rt A B) :
    (rootGroup σ hσ n γ).map (SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) (Pi.single (crd A) (1 : F))
        (Pi.single (crd B) (1 : F)) := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    have hx' : ∃ c : F, suElt σ hσ A B c = x := by
      by_cases he : Even n
      · exact (mem_rootGroup_iff_suElt hσ he hAB hγ x).1 hx
      · exact (mem_rootGroup_iff_suElt_odd hσ hAB hγ x).1 hx
    obtain ⟨c, hc⟩ := hx'
    refine Subgroup.subset_closure ⟨c, ?_⟩
    have hxmat : (((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
        mat σ n (suElt σ hσ A B c) := by rw [hc]; exact (mat_apply x).symm
    show ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
    rw [hxmat, ← grcPSU_pairGen_suElt σ hσ hAB c]
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_map.2 ⟨suElt σ hσ A B c, ?_, ?_⟩
    · by_cases he : Even n
      · exact (mem_rootGroup_iff_suElt hσ he hAB hγ _).2 ⟨c, rfl⟩
      · exact (mem_rootGroup_iff_suElt_odd hσ hAB hγ _).2 ⟨c, rfl⟩
    · apply Units.ext
      change mat σ n (suElt σ hσ A B c) = (g : Matrix (Fin n) (Fin n) F)
      rw [← grcPSU_pairGen_suElt σ hσ hAB c]
      exact hg.symm

private theorem grcPSU_map_conj_subtype {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F) (u : SU σ n)
    (H : Subgroup (SU σ n)) :
    (H.map (MulAut.conj u).toMonoidHom).map (SU σ n).subtype =
      (H.map (SU σ n).subtype).map
        (MulAut.conj ((u : GL (Fin n) F)) : MulAut (GL (Fin n) F)).toMonoidHom := by
  apply le_antisymm
  · rintro g ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine Subgroup.mem_map.2 ⟨(x : GL (Fin n) F),
      Subgroup.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    change MulAut.conj ((u : GL (Fin n) F)) ((x : GL (Fin n) F)) =
      (SU σ n).subtype ((MulAut.conj u) x)
    simp [MulAut.conj_apply, Units.val_mul]
  · rintro g ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine Subgroup.mem_map.2 ⟨(MulAut.conj u) x, ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    · change (SU σ n).subtype ((MulAut.conj u) x) =
        MulAut.conj ((u : GL (Fin n) F)) ((x : GL (Fin n) F))
      simp [MulAut.conj_apply, Units.val_mul]

private theorem grcPSU_pairGen_conj {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (u : SU σ n) (x y : Fin n → F) (c : F) :
    (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        (1 + c • Matrix.vecMulVec x
              (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) -
          σ.toRingHom c • Matrix.vecMulVec y
              (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n))) *
        ((((u : GL (Fin n) F))⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + c • Matrix.vecMulVec
            (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
            (Matrix.vecMul (fun i =>
              σ.toRingHom (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y i))
              (Unitary.antidiag n)) -
        σ.toRingHom c • Matrix.vecMulVec
            (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y)
            (Matrix.vecMul (fun i =>
              σ.toRingHom (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x i))
              (Unitary.antidiag n)) := by
  let U : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let V : Matrix (Fin n) (Fin n) F :=
    ((((u : GL (Fin n) F))⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  change U * (1 + c • Matrix.vecMulVec x
            (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) -
        σ.toRingHom c • Matrix.vecMulVec y
            (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n))) * V =
      1 + c • Matrix.vecMulVec (Matrix.mulVec U x)
            (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U y i)) (Unitary.antidiag n)) -
        σ.toRingHom c • Matrix.vecMulVec (Matrix.mulVec U y)
            (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U x i)) (Unitary.antidiag n))
  have hUV : U * V = 1 := by
    change (((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      ((((u : GL (Fin n) F))⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiso : conjTr σ U * Unitary.antidiag n * U = Unitary.antidiag n := by
    have h := CFSG.Timmesfeld.LieEmbed.suMat_isometry σ u
    rwa [CFSG.Timmesfeld.LieEmbed.suMat_apply] at h
  have hrow : ∀ v : Fin n → F,
      Matrix.vecMul (Timmesfeld.LieEmbed.uRow σ v) V =
        Timmesfeld.LieEmbed.uRow σ (Matrix.mulVec U v) := by
    intro v
    have h := CFSG.Timmesfeld.LieEmbed.uRow_mulVec_vecMul_of_isometry hiso v
    rw [← h, Matrix.vecMul_vecMul, hUV, Matrix.vecMul_one]
  have hN1 : U * Matrix.vecMulVec x
        (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) * V =
      Matrix.vecMulVec (Matrix.mulVec U x)
        (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U y i)) (Unitary.antidiag n)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [show Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n) =
        Timmesfeld.LieEmbed.uRow σ y from rfl]
    rw [hrow y]
    rfl
  have hN2 : U * Matrix.vecMulVec y
        (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n)) * V =
      Matrix.vecMulVec (Matrix.mulVec U y)
        (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U x i)) (Unitary.antidiag n)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [show Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n) =
        Timmesfeld.LieEmbed.uRow σ x from rfl]
    rw [hrow x]
    rfl
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul,
    Matrix.sub_mul, Matrix.smul_mul, hUV, Matrix.one_mul, hN1, hN2]

private theorem grcPSU_unitPairGroup_conj {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (u : SU σ n) (x y : Fin n → F) :
    (unitPairGroup σ.toRingHom (Unitary.antidiag n) x y).map
        (MulAut.conj ((u : GL (Fin n) F)) : MulAut (GL (Fin n) F)).toMonoidHom =
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) := by
  apply le_antisymm
  · show (unitPairGroup σ.toRingHom (Unitary.antidiag n) x y).map
        (MulAut.conj ((u : GL (Fin n) F)) : MulAut (GL (Fin n) F)).toMonoidHom ≤
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y)
    rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨c, ?_⟩)
    change ((MulAut.conj ((u : GL (Fin n) F)) g : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = _
    rw [MulAut.conj_apply]
    simp only [Units.val_mul]
    rw [show ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        1 + c • Matrix.vecMulVec x
              (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) -
          σ.toRingHom c • Matrix.vecMulVec y
              (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n)) from hg]
    exact grcPSU_pairGen_conj σ u x y c
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_map.2 ⟨(MulAut.conj (((u : GL (Fin n) F))⁻¹)) g, ?_, ?_⟩
    · refine Subgroup.subset_closure ⟨c, ?_⟩
      show (((MulAut.conj (((u : GL (Fin n) F))⁻¹)) (g : GL (Fin n) F) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
      rw [MulAut.conj_apply]
      simp only [Units.val_mul]
      rw [show ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          1 + c • Matrix.vecMulVec
                (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
                (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec
                    (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y i))
                  (Unitary.antidiag n)) -
            σ.toRingHom c • Matrix.vecMulVec
                (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y)
                (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec
                    (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x i))
                  (Unitary.antidiag n)) from hg]
      have hux : ((((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F))⁻¹ *
          (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = 1 := by
        have h : ((u : GL (Fin n) F))⁻¹ * (u : GL (Fin n) F) = 1 := inv_mul_cancel _
        simpa [Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val] using
          congrArg (fun w : GL (Fin n) F => ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
      have hx : Matrix.mulVec ((((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F))⁻¹
          (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x) = x := by
        rw [Matrix.mulVec_mulVec, hux, Matrix.one_mulVec]
      have hy : Matrix.mulVec ((((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F))⁻¹
          (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) = y := by
        rw [Matrix.mulVec_mulVec, hux, Matrix.one_mulVec]
      simpa [hx, hy, CFSG.Timmesfeld.LieEmbed.uRow] using
        grcPSU_pairGen_conj σ u⁻¹
          (x := Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
          (y := Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) c
    · change ((MulAut.conj ((u : GL (Fin n) F))) *
          (MulAut.conj (((u : GL (Fin n) F))⁻¹))) g = g
      rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem grcPSU_mulVec_single_ne_zero {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (u : SU σ n) (a : Fin n) :
    mat σ n u *ᵥ Pi.single a (1 : F) ≠ 0 := by
  intro h
  have h' := congrArg (fun v => mat σ n u⁻¹ *ᵥ v) h
  rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
    Matrix.one_mulVec] at h'
  have := congrFun h' a
  rw [Pi.single_eq_same, Pi.zero_apply] at this
  exact one_ne_zero this

private theorem grcPSU_mulVec_single_not_smul {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (u : SU σ n)
    {a b : Fin n} (hab : a ≠ b) :
    ¬ ∃ c : F, mat σ n u *ᵥ Pi.single b (1 : F) =
      c • (mat σ n u *ᵥ Pi.single a (1 : F)) := by
  rintro ⟨c, hc⟩
  have h' := congrArg (fun v => mat σ n u⁻¹ *ᵥ v) hc
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul,
    inv_mul_cancel, map_one, Matrix.one_mulVec, Matrix.one_mulVec] at h'
  have ha : (Pi.single b (1 : F)) b = (c • Pi.single a (1 : F)) b := congrFun h' b
  rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hab), smul_eq_mul,
    mul_zero] at ha
  exact one_ne_zero ha

private theorem grcPSU_herm_mat {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (u : SU σ n) (a b : Fin n) :
    Matrix.vecMul (fun i => σ ((mat σ n u *ᵥ Pi.single a (1 : F)) i)) (Unitary.antidiag n) ⬝ᵥ
        (mat σ n u *ᵥ Pi.single b (1 : F)) = if b = Fin.rev a then 1 else 0 := by
  have h := sum_mat_mul_mat u a b
  rw [← h]
  simp only [dotProduct, CFSG.Timmesfeld.LieEmbed.vecMul_antidiag]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem grcPSU_two_le_of_ne_rev {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) : 2 ≤ n := by
  by_contra h
  have hn : n ≤ 1 := by omega
  interval_cases n
  · exact Fin.elim0 i
  · exact hi (Subsingleton.elim i (Fin.rev i))

private def grcPSU_OrbLast (n : ℕ) (e : Fin (n / 2) → ℤ) : Prop :=
  ∃ (w : (coxeterMatrix (isFiniteType_cartan n)).Group) (l : Fin (n / 2)),
    ¬ l.val + 1 < n / 2 ∧
      toStd n (weylAction (isFiniteType_cartan n) w (Pi.single l (1 : ℤ))) = e

private theorem grcPSU_OrbLast_neg {n : ℕ} {e : Fin (n / 2) → ℤ} (h : grcPSU_OrbLast n e) :
    grcPSU_OrbLast n (-e) := by
  obtain ⟨w, l, hl, hw⟩ := h
  exact ⟨w * (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple l, l, hl, by
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, toStd_neg, hw]⟩

private theorem grcPSU_OrbLast_two_smul_single {n : ℕ} (he : Even n) (b : Fin (n / 2)) :
    grcPSU_OrbLast n (2 • Pi.single b (1 : ℤ)) := by
  refine reach_smul_single (grcPSU_OrbLast n) ?_ 2 ?_ (n / 2 - b.val - 1) b (by omega)
  · rintro k e ⟨w, l, hl, hw⟩
    exact ⟨(coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple k * w, l, hl, by
      rw [weylAction_mul_apply, weylAction_simple, toStd_reflection, hw]⟩
  · intro k hk
    exact ⟨1, k, hk, by rw [map_one, Module.End.one_apply, toStd_single_of_even he hk]⟩

private theorem grcPSU_OrbLast_of_two_weight {n : ℕ} (he : Even n)
    {i : Fin n} (hi : i ≠ Fin.rev i) : grcPSU_OrbLast n (2 • weight n i) := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · rw [weight_lowIdx]
    exact grcPSU_OrbLast_two_smul_single he a
  · rw [weight_rev_lowIdx, smul_neg]
    exact grcPSU_OrbLast_neg (grcPSU_OrbLast_two_smul_single he a)

private theorem grcPSU_exists_weyl_long_even {n : ℕ} (he : Even n)
    {γ : Fin (n / 2) → ℤ} {i : Fin n} (hi : i ≠ Fin.rev i)
    (h : toStd n γ = 2 • weight n i) :
    ∃ w : (coxeterMatrix (isFiniteType_cartan n)).Group,
      weylAction (isFiniteType_cartan n) w
        (Pi.single (⟨n / 2 - 1, by omega⟩ : Fin (n / 2)) (1 : ℤ)) = γ := by
  have hn : 2 ≤ n := grcPSU_two_le_of_ne_rev hi
  obtain ⟨w, l, hl, hw⟩ := grcPSU_OrbLast_of_two_weight he hi
  have hw' : weylAction (isFiniteType_cartan n) w (Pi.single l (1 : ℤ)) = γ :=
    toStd_injective n (hw.trans h.symm)
  have hl' : l = ⟨n / 2 - 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_mk]
    have := l.isLt
    have := hl
    omega
  rw [hl'] at hw'
  exact ⟨w, hw'⟩

private theorem grcPSU_exists_weyl_long_odd {n : ℕ} (he : ¬Even n)
    {γ : Fin (n / 2) → ℤ} {i : Fin n} (hi : i ≠ Fin.rev i)
    (h : toStd n γ = 2 • weight n i) :
    ∃ w : (coxeterMatrix (isFiniteType_cartan n)).Group,
      weylAction (isFiniteType_cartan n) w
        (2 • Pi.single (⟨n / 2 - 1, by omega⟩ : Fin (n / 2)) (1 : ℤ)) = γ := by
  have hn : 2 ≤ n := grcPSU_two_le_of_ne_rev hi
  obtain ⟨w, l, hl, hw⟩ := orbL_weight he hi
  have hl' : l = ⟨n / 2 - 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_mk]
    have := l.isLt
    have := hl
    omega
  have hwe : weylAction (isFiniteType_cartan n) w (2 • Pi.single l (1 : ℤ)) = γ := by
    apply toStd_injective
    rw [map_nsmul, toStd_nsmul, hw]
    exact h.symm
  rw [← hl']
  exact ⟨w, hwe⟩

private theorem grcPSU_form_of_maxHeight {n : ℕ} (hn2 : 2 ≤ n) {θ : Fin (n / 2) → ℤ}
    (hθ : θ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hmax : ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n),
      LieType.Steinberg.ht δ ≤ LieType.Steinberg.ht θ) :
    ∃ i : Fin n, i ≠ Fin.rev i ∧ toStd n θ = 2 • weight n i := by
  have hle : LieType.Steinberg.ht (ggTopRoot n) ≤ LieType.Steinberg.ht θ :=
    hmax _ (ggTopRoot_mem_roots hn2)
  have hθ2 : LieType.Steinberg.ht (ggTopRoot n) = (n : ℤ) - 1 := ht_ggTopRoot hn2
  have h2 := two_mul_ht θ
  rw [roots_eq] at hθ
  rcases hθ with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exfalso
    rw [h, map_sub, lv_weight, lv_weight] at h2
    have hi' := i.isLt
    have hj' := j.isLt
    exact hji (Fin.ext (by rw [Fin.val_rev]; omega))
  · exact ⟨i, hi, h⟩
  · exfalso
    rw [h, lv_weight] at h2
    have hi' := i.isLt
    omega

private theorem grcPSU_ggLongRoot_of_toStd_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {γ : Fin (n / 2) → ℤ}
    {i : Fin n} (hi : i ≠ Fin.rev i) (h : toStd n γ = 2 • weight n i) :
    GGLongRoot (Unitary.rootDatum hc n) γ := by
  have hn : 2 ≤ n := grcPSU_two_le_of_ne_rev hi
  have hm : 0 < n / 2 := by omega
  obtain ⟨θ, hθ_mem, hθ_max⟩ := CFSG.StandardType.exists_maxHeight
    (D := Unitary.rootDatum hc n) hm
  let θ' : Fin (n / 2) → ℤ := θ
  have hθ'_mem : θ' ∈ roots (isFiniteType_cartan n) (divisible n) := hθ_mem
  have hθ'_max : ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n),
      LieType.Steinberg.ht δ ≤ LieType.Steinberg.ht θ' := hθ_max
  obtain ⟨i₀, hi₀, hθ_form⟩ := grcPSU_form_of_maxHeight hn hθ'_mem hθ'_max
  by_cases he : Even n
  · obtain ⟨w₁, hw₁⟩ := grcPSU_exists_weyl_long_even he hi h
    obtain ⟨w₂, hw₂⟩ := grcPSU_exists_weyl_long_even he hi₀ hθ_form
    refine ⟨w₁ * w₂⁻¹, θ', hθ'_mem, ?_, ?_⟩
    · exact hθ'_max
    · have heq : γ = weylAction (isFiniteType_cartan n) (w₁ * w₂⁻¹) θ' := by
        rw [weylAction_mul_apply, ← hw₂, weylAction_inv_apply_apply, hw₁]
      exact heq
  · obtain ⟨w₁, hw₁⟩ := grcPSU_exists_weyl_long_odd he hi h
    obtain ⟨w₂, hw₂⟩ := grcPSU_exists_weyl_long_odd he hi₀ hθ_form
    refine ⟨w₁ * w₂⁻¹, θ', hθ'_mem, ?_, ?_⟩
    · exact hθ'_max
    · have heq : γ = weylAction (isFiniteType_cartan n) (w₁ * w₂⁻¹) θ' := by
        rw [weylAction_mul_apply, ← hw₂, weylAction_inv_apply_apply, hw₁]
      exact heq
private theorem grcPSU_wt_inl {n : ℕ} (a : Fin (n / 2)) :
    CFSG.LieType.Universal.Symplectic.SpExtras.wt (Sum.inl a : Fin (n / 2) ⊕ Fin (n / 2)) =
      Pi.single a (1 : ℤ) := by
  rw [← weight_crd (Sum.inl a), crd_inl, weight_lowIdx]

private theorem grcPSU_wt_inr {n : ℕ} (a : Fin (n / 2)) :
    CFSG.LieType.Universal.Symplectic.SpExtras.wt (Sum.inr a : Fin (n / 2) ⊕ Fin (n / 2)) =
      -Pi.single a (1 : ℤ) := by
  rw [← weight_crd (Sum.inr a), crd_inr, weight_rev_lowIdx]

private theorem grcPSU_short_classification {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hl : ¬ GGLongRoot (Unitary.rootDatum hc n) γ)
    (h2 : 2 • γ ∉ roots (isFiniteType_cartan n) (divisible n)) :
    ∃ A B : Fin (n / 2) ⊕ Fin (n / 2), idx A ≠ idx B ∧ toStd n γ = rt A B := by
  rw [roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, hi, hj, hji, hstd⟩ | ⟨i, hi, hstd⟩ | ⟨hodd, i, hi, hstd⟩
  · obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
    · obtain ⟨b, rfl | rfl⟩ := exists_lowIdx hj
      · refine ⟨Sum.inl a, Sum.inr b, ?_, ?_⟩
        · simp only [idx_inl, idx_inr]
          exact fun h => hij (by rw [h])
        · rw [hstd, rt, grcPSU_wt_inl a, grcPSU_wt_inr b, weight_lowIdx, weight_lowIdx]
          abel
      · refine ⟨Sum.inl a, Sum.inl b, ?_, ?_⟩
        · simp only [idx_inl]
          exact fun h => hji (by rw [h])
        · rw [hstd, rt, grcPSU_wt_inl a, grcPSU_wt_inl b, weight_lowIdx, weight_rev_lowIdx]
          abel
    · obtain ⟨b, rfl | rfl⟩ := exists_lowIdx hj
      · refine ⟨Sum.inr a, Sum.inr b, ?_, ?_⟩
        · simp only [idx_inr]
          exact fun h => hji (by rw [h, Fin.rev_rev])
        · rw [hstd, rt, grcPSU_wt_inr a, grcPSU_wt_inr b, weight_rev_lowIdx, weight_lowIdx]
          abel
      · refine ⟨Sum.inr a, Sum.inl b, ?_, ?_⟩
        · simp only [idx_inr, idx_inl]
          exact fun h => hij (by rw [h])
        · rw [hstd, rt, grcPSU_wt_inr a, grcPSU_wt_inl b, weight_rev_lowIdx,
            weight_rev_lowIdx]
          abel
  · exfalso
    exact hl (grcPSU_ggLongRoot_of_toStd_two hc hi hstd)
  · exfalso
    apply h2
    rw [roots_eq]
    refine Or.inr (Or.inl ⟨i, hi, ?_⟩)
    rw [toStd_nsmul, hstd]


private theorem grcPSU_short_rootGroup_conj {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    {A B : Fin (n / 2) ⊕ Fin (n / 2)} (hAB : idx A ≠ idx B) {γ : Fin (n / 2) → ℤ}
    (hγ : toStd n γ = rt A B) (u : SU σ n) :
    (((rootGroup σ hσ n γ).map (MulAut.conj u).toMonoidHom).map (SU σ n).subtype) =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) (mat σ n u *ᵥ Pi.single (crd A) (1 : F))
        (mat σ n u *ᵥ Pi.single (crd B) (1 : F)) := by
  rw [grcPSU_map_conj_subtype σ u (rootGroup σ hσ n γ),
    grcPSU_rootGroup_map_subtype_short σ hσ hAB hγ,
    grcPSU_unitPairGroup_conj σ u (Pi.single (crd A) (1 : F)) (Pi.single (crd B) (1 : F)),
    mat_apply]

private theorem grcPSU_short_pair_side_conditions {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) {A B : Fin (n / 2) ⊕ Fin (n / 2)} (hAB : idx A ≠ idx B) (u : SU σ n) :
    (mat σ n u *ᵥ Pi.single (crd A) (1 : F)) ≠ 0 ∧
      (mat σ n u *ᵥ Pi.single (crd B) (1 : F)) ≠ 0 ∧
      LinearIndependent F ![(mat σ n u *ᵥ Pi.single (crd A) (1 : F)),
        (mat σ n u *ᵥ Pi.single (crd B) (1 : F))] ∧
      Matrix.vecMul (fun i => σ ((mat σ n u *ᵥ Pi.single (crd A) (1 : F)) i))
        (Unitary.antidiag n) ⬝ᵥ (mat σ n u *ᵥ Pi.single (crd A) (1 : F)) = 0 ∧
      Matrix.vecMul (fun i => σ ((mat σ n u *ᵥ Pi.single (crd B) (1 : F)) i))
        (Unitary.antidiag n) ⬝ᵥ (mat σ n u *ᵥ Pi.single (crd B) (1 : F)) = 0 ∧
      Matrix.vecMul (fun i => σ ((mat σ n u *ᵥ Pi.single (crd A) (1 : F)) i))
        (Unitary.antidiag n) ⬝ᵥ (mat σ n u *ᵥ Pi.single (crd B) (1 : F)) = 0 := by
  have hcrd : crd A ≠ crd B := fun h => hAB (by rw [crd_injective h])
  have hneB : crd B ≠ Fin.rev (crd A) := by
    intro h
    have h' : B = Sum.swap A := crd_injective (by rw [h, ← crd_swap])
    exact hAB (by rw [h', idx_swap])
  refine ⟨grcPSU_mulVec_single_ne_zero σ u (crd A),
    grcPSU_mulVec_single_ne_zero σ u (crd B), ?_, ?_, ?_, ?_⟩
  · refine CFSG.ClassicalInvolution.ModelFacts.MF15.linearIndependent_pair_of_not_eigen
      (grcPSU_mulVec_single_ne_zero σ u (crd A)) ?_
    exact grcPSU_mulVec_single_not_smul σ u hcrd
  · rw [grcPSU_herm_mat, if_neg (crd_ne_rev A)]
  · rw [grcPSU_herm_mat, if_neg (crd_ne_rev B)]
  · rw [grcPSU_herm_mat, if_neg hneB]

private theorem grcPSU_short_core {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hl : ¬ GGLongRoot (Unitary.rootDatum hc n) γ)
    (h2 : 2 • γ ∉ roots (isFiniteType_cartan n) (divisible n))
    (u : ↥(SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
    ∃ v w : Fin n → F, v ≠ 0 ∧ w ≠ 0 ∧ LinearIndependent F ![v, w] ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
        (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w i))
        (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
        (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      (((rootGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc) n γ).map
          (MulAut.conj u).toMonoidHom).map
          (SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype) =
        unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) v w := by
  let σ := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
  have hσ : ∀ c, σ (σ c) = c := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  obtain ⟨A, B, hAB, hrt⟩ := grcPSU_short_classification hc hγ hl h2
  obtain ⟨hv, hw, hli, hvv, hww, hvw⟩ := grcPSU_short_pair_side_conditions σ hAB u
  refine ⟨mat σ n u *ᵥ Pi.single (crd A) (1 : F),
    mat σ n u *ᵥ Pi.single (crd B) (1 : F), hv, hw, hli, hvv, hww, hvw, ?_⟩
  exact grcPSU_short_rootGroup_conj σ hσ hAB hrt u

private theorem grcPSU_long_core {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hl : GGLongRoot (Unitary.rootDatum hc n) γ)
    (u : ↥(SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
    ∃ v : Fin n → F, v ≠ 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
        (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      (((rootGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc) n γ).map
          (MulAut.conj u).toMonoidHom).map
          (SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) v := by
  obtain ⟨v, w, hvv, hww, hvw, h1, h2⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitTransvGroup_eq_conj_rootGroup_SU hc n hγ hl u
  refine ⟨v, ?_, hvv, h1⟩
  intro hv
  rw [hv] at hvw
  simp [Matrix.vecMul, dotProduct] at hvw

theorem exists_unitTransvGroup_eq_rootGroup_PSU
    (n g
        : ℕ)
    {γ : Fin (ggU .PSU n (g + 1)).D.rank → ℤ} (hγ : γ ∈ (ggU .PSU n (g + 1)).D.roots)
    (hl : GGLongRoot (ggU .PSU n (g + 1)).D γ) (u : (ggU .PSU n (g + 1)).K) :
    ∃ v : Fin n → GaloisField 2 (2 * (g + 1)), v ≠ 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      (((ggU .PSU n (g + 1)).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) v := by
  exact grcPSU_long_core (F := GaloisField 2 (2 * (g + 1))) (f := g + 1)
    (CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)) hγ hl u

theorem exists_unitPairGroup_eq_rootGroup_PSU
    (n g
        : ℕ)
    {γ : Fin (ggU .PSU n (g + 1)).D.rank → ℤ} (hγ : γ ∈ (ggU .PSU n (g + 1)).D.roots)
    (hl : ¬ GGLongRoot (ggU .PSU n (g + 1)).D γ) (h2 : 2 • γ ∉ (ggU .PSU n (g + 1)).D.roots)
    (u : (ggU .PSU n (g + 1)).K) :
    ∃ v w : Fin n → GaloisField 2 (2 * (g + 1)), v ≠ 0 ∧ w ≠ 0 ∧
      LinearIndependent (GaloisField 2 (2 * (g + 1))) ![v, w] ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      (((ggU .PSU n (g + 1)).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype =
        unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) v w := by
  exact grcPSU_short_core (F := GaloisField 2 (2 * (g + 1))) (f := g + 1)
    (CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)) hγ hl h2 u

end CFSG.StandardType.ClassicalPosition
