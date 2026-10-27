module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpCentreMap
import CFSG.OddTranspositions.PartThree.Twelve.SevenForm
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.ClassicalGroups.Symplectic.PointRadicalNormal
import CFSG.RankThree.Classical.SpIsometry
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpElt
import CFSG.RankThree.PartOne.S11d.OddAlt

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.OddTranspositions.PartFour
  CFSG.Open
open CFSG.ClassicalInvolution.Models.SymplecticPairs (fixing mem_fixing)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.RankThree.PartOne.KCSpComm (eq_of_spEnd_eq spEnd_fieldSp)
open CFSG.RankThree.PartOne.CTP
  (spEnd_isometry spTransvection_conj spTransvection_smul spTransvection_zero)
open CFSG.LocalAnalysis.WeakClosure81 (spConf_transvection_mul)

variable {k : ℕ} {F : Type} [Field F]

abbrev SpMarkedGroup (k : ℕ) (F : Type) [Field F] : Type :=
  ↥(StatedSp k F) × Multiplicative (ZMod 2)

@[expose] def spMarkedStab (y : Fin k ⊕ Fin k → F) : Subgroup (SpMarkedGroup k F) :=
  (fixing {y}).comap (MonoidHom.fst (↥(StatedSp k F)) (Multiplicative (ZMod 2)))

@[expose] def spMarkedSet : Set (SpMarkedGroup k F) :=
  {p | ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ p = (spTransvection a 1, Multiplicative.ofAdd 1)}

private theorem spForm_sub_smul_self {y z : Fin k ⊕ Fin k → F} (hz : spForm k F z y = 1)
    (v : Fin k ⊕ Fin k → F) : spForm k F (v - (spForm k F v y) • z) y = 0 := by
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hz, mul_one,
    sub_self]

private theorem eq_smul_of_forall_spForm_eq_zero [CharP F 2] {y z : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1) {w : Fin k ⊕ Fin k → F}
    (hw : ∀ e, spForm k F e y = 0 → spForm k F w e = 0) :
    w = (spForm k F w z) • y := by
  have hspan : w ∈ Submodule.span F (Set.range (fun _ : Unit => y)) := by
    refine CFSG.ClassicalGroups.Alternating.mem_span_of_forall_orthogonal
      (B := spForm k F) spForm_nondegenerate (fun _ : Unit => y) w ?_
    intro e he
    exact hw e ((CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt e y).trans (he ()))
  rw [Set.range_const, Submodule.mem_span_singleton] at hspan
  obtain ⟨c, hc⟩ := hspan
  rw [← hc, LinearMap.BilinForm.smul_left,
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt y z, hz, mul_one]

private theorem map_zero_of_spForm_eq_zero {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {y : Fin k ⊕ Fin k → F}
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w) :
    f 0 = 0 := by
  have h := hadd 0 0 (by simp) (by simp)
  rw [zero_add] at h
  exact (add_left_cancel ((add_zero (f 0)).trans h)).symm

private theorem map_sub_of_spForm_eq_zero {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {y : Fin k ⊕ Fin k → F}
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w) :
    ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x - w) = f x - f w := by
  have h0 : f 0 = 0 := map_zero_of_spForm_eq_zero hadd
  intro x w hx hw
  have hneg : f (-w) = -f w := by
    have h := hadd w (-w) hw (by rw [map_neg, LinearMap.neg_apply, hw, neg_zero])
    rw [add_neg_cancel, h0] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)
  rw [sub_eq_add_neg, hadd x (-w) hx (by rw [map_neg, LinearMap.neg_apply, hw, neg_zero]),
    hneg, sub_eq_add_neg]

private theorem eq_of_map_eq_of_spForm_eq_zero [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y y' z : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w)
    (hsmul : ∀ (c : F) x, spForm k F x y = 0 → f (c • x) = σ c • f x)
    (hiso : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 →
      spForm k F (f x) (f w) = σ (spForm k F x w))
    (hy : f y = y') (hy' : y' ≠ 0) :
    ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f x = f w → x = w := by
  intro x w hx hw hxw
  have horth : ∀ e, spForm k F e y = 0 → spForm k F (x - w) e = 0 := by
    intro e he
    have h1 : spForm k F (f x) (f e) = spForm k F (f w) (f e) := by rw [hxw]
    rw [hiso x e hx he, hiso w e hw he] at h1
    have h2 : spForm k F x e = spForm k F w e := σ.injective h1
    rw [map_sub, LinearMap.sub_apply, h2, sub_self]
  have hspan := eq_smul_of_forall_spForm_eq_zero hz horth
  have hfw : f (x - w) = 0 := by
    rw [map_sub_of_spForm_eq_zero hadd x w hx hw, hxw, sub_self]
  have hself : spForm k F y y = 0 := spForm_isAlt.self_eq_zero y
  have hzero : σ (spForm k F (x - w) z) • y' = 0 := by
    have h1 : f (x - w) = σ (spForm k F (x - w) z) • f y := by
      conv_lhs => rw [hspan]
      exact hsmul (spForm k F (x - w) z) y hself
    rw [← hy, ← h1, hfw]
  have hc : spForm k F (x - w) z = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact σ.injective (by rw [h, map_zero])
    · exact absurd h hy'
  exact sub_eq_zero.mp (by rw [hspan, hc, zero_smul])

private theorem exists_semilinear_preimage [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y y' z : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w)
    (hsmul : ∀ (c : F) x, spForm k F x y = 0 → f (c • x) = σ c • f x)
    (hiso : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 →
      spForm k F (f x) (f w) = σ (spForm k F x w))
    (hsurj : ∀ x', spForm k F x' y' = 0 → ∃ x, spForm k F x y = 0 ∧ f x = x')
    (hy : f y = y') (hy' : y' ≠ 0) :
    ∃ ginv : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F),
      (∀ x', spForm k F x' y' = 0 → spForm k F (ginv x') y = 0 ∧ f (ginv x') = x') ∧
      (∀ x' w', spForm k F x' y' = 0 → spForm k F w' y' = 0 →
        ginv (x' + w') = ginv x' + ginv w') ∧
      (∀ (c : F) x', spForm k F x' y' = 0 → ginv (c • x') = σ.symm c • ginv x') := by
  classical
  have hinj := eq_of_map_eq_of_spForm_eq_zero hz hadd hsmul hiso hy hy'
  have hex : ∀ x' : Fin k ⊕ Fin k → F,
      ∃ x : Fin k ⊕ Fin k → F, spForm k F x' y' = 0 → spForm k F x y = 0 ∧ f x = x' := by
    intro x'
    by_cases h : spForm k F x' y' = 0
    · obtain ⟨x, hx, hfx⟩ := hsurj x' h
      exact ⟨x, fun _ => ⟨hx, hfx⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  refine ⟨fun x' => (hex x').choose, fun x' h => (hex x').choose_spec h, ?_, ?_⟩
  · intro x' w' hx' hw'
    have h1 : spForm k F (x' + w') y' = 0 := by
      rw [map_add, LinearMap.add_apply, hx', hw', add_zero]
    have hsum : spForm k F ((hex x').choose + (hex w').choose) y = 0 := by
      rw [map_add, LinearMap.add_apply, ((hex x').choose_spec hx').1,
        ((hex w').choose_spec hw').1, add_zero]
    exact hinj _ _ ((hex _).choose_spec h1).1 hsum (by
      rw [((hex _).choose_spec h1).2,
        hadd _ _ ((hex x').choose_spec hx').1 ((hex w').choose_spec hw').1,
        ((hex x').choose_spec hx').2, ((hex w').choose_spec hw').2])
  · intro c x' hx'
    have hc : spForm k F (c • x') y' = 0 := by
      rw [map_smul, LinearMap.smul_apply, hx', smul_zero]
    have hcs : spForm k F (σ.symm c • (hex x').choose) y = 0 := by
      rw [map_smul, LinearMap.smul_apply, ((hex x').choose_spec hx').1, smul_zero]
    exact hinj _ _ ((hex _).choose_spec hc).1 hcs (by
      rw [((hex _).choose_spec hc).2,
        hsmul (σ.symm c) _ ((hex x').choose_spec hx').1, ((hex x').choose_spec hx').2,
        σ.apply_symm_apply])

private theorem exists_spForm_comp_eq [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y y' z : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w)
    (hsmul : ∀ (c : F) x, spForm k F x y = 0 → f (c • x) = σ c • f x)
    (hiso : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 →
      spForm k F (f x) (f w) = σ (spForm k F x w))
    (hmaps : ∀ x, spForm k F x y = 0 → spForm k F (f x) y' = 0)
    (hsurj : ∀ x', spForm k F x' y' = 0 → ∃ x, spForm k F x y = 0 ∧ f x = x')
    (hy : f y = y') (hy' : y' ≠ 0) :
    ∃ z' : Fin k ⊕ Fin k → F, ∀ x, spForm k F x y = 0 →
      spForm k F (f x) z' = σ (spForm k F x z) := by
  classical
  obtain ⟨ginv, hmem, hadd', hsmul'⟩ :=
    exists_semilinear_preimage hz hadd hsmul hiso hsurj hy hy'
  have hinj := eq_of_map_eq_of_spForm_eq_zero hz hadd hsmul hiso hy hy'
  let φ : ↥(LinearMap.ker ((spForm k F).flip y')) →ₗ[F] F :=
    { toFun := fun x' => σ (spForm k F (ginv x'.1) z)
      map_add' := fun x' w' => by
        show σ (spForm k F (ginv (x'.1 + w'.1)) z) =
          σ (spForm k F (ginv x'.1) z) + σ (spForm k F (ginv w'.1) z)
        rw [hadd' x'.1 w'.1 x'.2 w'.2, map_add, LinearMap.add_apply, map_add]
      map_smul' := fun c x' => by
        show σ (spForm k F (ginv (c • x'.1)) z) = c • σ (spForm k F (ginv x'.1) z)
        rw [hsmul' c x'.1 x'.2, LinearMap.BilinForm.smul_left, map_mul,
          σ.apply_symm_apply, smul_eq_mul] }
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  refine ⟨((spForm k F).toDual spForm_nondegenerate).symm ψ, fun x hx => ?_⟩
  rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt (f x) _,
    LinearMap.BilinForm.apply_toDual_symm_apply]
  have hfx : spForm k F (f x) y' = 0 := hmaps x hx
  have hcongr : ψ (f x) = φ ⟨f x, hfx⟩ := by
    have h := LinearMap.congr_fun hψ ⟨f x, hfx⟩
    simpa using h
  rw [hcongr]
  have hginv : ginv (f x) = x :=
    hinj _ _ (hmem _ hfx).1 hx (by rw [(hmem _ hfx).2])
  show σ (spForm k F (ginv (f x)) z) = σ (spForm k F x z)
  rw [hginv]

private noncomputable def semilinearExtend (σ : F ≃+* F)
    (f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F))
    (y z z' : Fin k ⊕ Fin k → F) (v : Fin k ⊕ Fin k → F) : Fin k ⊕ Fin k → F :=
  f (v - (spForm k F v y) • z) + σ (spForm k F v y) • z'

private theorem semilinearExtend_of_mem {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    {x : Fin k ⊕ Fin k → F} (hx : spForm k F x y = 0) :
    semilinearExtend σ f y z z' x = f x := by
  simp [semilinearExtend, hx]

private theorem semilinearExtend_self {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y y' z z' : Fin k ⊕ Fin k → F}
    (hy : f y = y') : semilinearExtend σ f y z z' y = y' := by
  simp [semilinearExtend, spForm_isAlt.self_eq_zero, hy]

private theorem semilinearExtend_add [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w)
    (v w : Fin k ⊕ Fin k → F) :
    semilinearExtend σ f y z z' (v + w) =
      semilinearExtend σ f y z z' v + semilinearExtend σ f y z z' w := by
  have hsum : spForm k F (v + w) y = spForm k F v y + spForm k F w y := by
    rw [map_add, LinearMap.add_apply]
  have hsplit : v + w - (spForm k F v y + spForm k F w y) • z =
      (v - (spForm k F v y) • z) + (w - (spForm k F w y) • z) := by
    rw [add_smul]
    abel
  rw [semilinearExtend, hsum, hsplit,
    hadd _ _ (spForm_sub_smul_self hz v) (spForm_sub_smul_self hz w), map_add, add_smul]
  simp only [semilinearExtend]
  abel

private theorem semilinearExtend_smul [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hsmul : ∀ (c : F) x, spForm k F x y = 0 → f (c • x) = σ c • f x)
    (c : F) (v : Fin k ⊕ Fin k → F) :
    semilinearExtend σ f y z z' (c • v) = σ c • semilinearExtend σ f y z z' v := by
  have hcv : spForm k F (c • v) y = c * spForm k F v y :=
    LinearMap.BilinForm.smul_left c v y
  have he : spForm k F (v - (spForm k F v y) • z) y = 0 := spForm_sub_smul_self hz v
  have hce : spForm k F (c • (v - (spForm k F v y) • z)) y = 0 := by
    rw [LinearMap.BilinForm.smul_left, he, mul_zero]
  have hsplit : c • v - (c * spForm k F v y) • z = c • (v - (spForm k F v y) • z) := by
    rw [smul_sub, smul_smul, mul_comm]
  rw [semilinearExtend, hcv, hsplit, hsmul c _ he, map_mul, semilinearExtend, smul_add,
    mul_smul]

private theorem spForm_semilinearExtend_z' [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hz' : ∀ x, spForm k F x y = 0 → spForm k F (f x) z' = σ (spForm k F x z))
    (hzz : spForm k F z' z' = 0) :
    ∀ w, spForm k F z' (semilinearExtend σ f y z z' w) = σ (spForm k F z w) := by
  intro w
  have hw : spForm k F (w - (spForm k F w y) • z) y = 0 := spForm_sub_smul_self hz w
  have hAw : semilinearExtend σ f y z z' w =
      f (w - (spForm k F w y) • z) + σ (spForm k F w y) • z' := rfl
  rw [hAw, map_add, LinearMap.BilinForm.smul_right, hzz, mul_zero, add_zero,
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt z'
      (f (w - (spForm k F w y) • z)), hz' _ hw,
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt z w]
  congr 1
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
    spForm_isAlt.self_eq_zero, mul_zero, sub_zero]

private theorem spForm_semilinearExtend_mem [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hiso : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 →
      spForm k F (f x) (f w) = σ (spForm k F x w))
    (hz' : ∀ x, spForm k F x y = 0 → spForm k F (f x) z' = σ (spForm k F x z))
    {v : Fin k ⊕ Fin k → F} (hv : spForm k F v y = 0) :
    ∀ w, spForm k F (f v) (semilinearExtend σ f y z z' w) = σ (spForm k F v w) := by
  intro w
  have hw : spForm k F (w - (spForm k F w y) • z) y = 0 := spForm_sub_smul_self hz w
  have hAw : semilinearExtend σ f y z z' w =
      f (w - (spForm k F w y) • z) + σ (spForm k F w y) • z' := rfl
  rw [hAw, map_add, LinearMap.BilinForm.smul_right, hiso v _ hv hw, hz' v hv, ← map_mul,
    ← map_add]
  congr 1
  conv_rhs => rw [show w = (w - (spForm k F w y) • z) + (spForm k F w y) • z from
    (sub_add_cancel _ _).symm]
  rw [map_add, LinearMap.BilinForm.smul_right]

private theorem semilinearExtend_isometry [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hiso : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 →
      spForm k F (f x) (f w) = σ (spForm k F x w))
    (hz' : ∀ x, spForm k F x y = 0 → spForm k F (f x) z' = σ (spForm k F x z))
    (hzz : spForm k F z' z' = 0) (v w : Fin k ⊕ Fin k → F) :
    spForm k F (semilinearExtend σ f y z z' v) (semilinearExtend σ f y z z' w)
      = σ (spForm k F v w) := by
  have hv : spForm k F (v - (spForm k F v y) • z) y = 0 := spForm_sub_smul_self hz v
  have hAv : semilinearExtend σ f y z z' v =
      f (v - (spForm k F v y) • z) + σ (spForm k F v y) • z' := rfl
  rw [hAv, map_add, LinearMap.add_apply, LinearMap.BilinForm.smul_left,
    spForm_semilinearExtend_mem hz hiso hz' hv w, spForm_semilinearExtend_z' hz hz' hzz w,
    ← map_mul, ← map_add]
  congr 1
  conv_rhs => rw [show v = (v - (spForm k F v y) • z) + (spForm k F v y) • z from
    (sub_add_cancel _ _).symm]
  rw [map_add, LinearMap.add_apply, LinearMap.BilinForm.smul_left]

private theorem semilinearExtend_injective [CharP F 2] {σ : F ≃+* F}
    {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {y z z' : Fin k ⊕ Fin k → F}
    (hz : spForm k F z y = 1)
    (hadd : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 → f (x + w) = f x + f w)
    (hiso : ∀ x w, spForm k F x y = 0 → spForm k F w y = 0 →
      spForm k F (f x) (f w) = σ (spForm k F x w))
    (hz' : ∀ x, spForm k F x y = 0 → spForm k F (f x) z' = σ (spForm k F x z))
    (hzz : spForm k F z' z' = 0) :
    Function.Injective (semilinearExtend σ f y z z') := by
  have hiso' := semilinearExtend_isometry hz hiso hz' hzz
  have hsub : ∀ a b, semilinearExtend σ f y z z' (a - b) =
      semilinearExtend σ f y z z' a - semilinearExtend σ f y z z' b := by
    intro a b
    have h := semilinearExtend_add (σ := σ) (f := f) (z' := z') hz hadd (a - b) b
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  intro v w hvw
  have hzero : semilinearExtend σ f y z z' (v - w) = 0 := by
    rw [hsub v w, hvw, sub_self]
  have hfin : v - w = 0 := by
    refine spForm_nondegenerate.1 (v - w) fun x => ?_
    have h := hiso' (v - w) x
    rw [hzero, map_zero, LinearMap.zero_apply] at h
    exact σ.injective (h.symm.trans (map_zero σ).symm)
  exact sub_eq_zero.mp hfin

private def coordTwist (σ : F ≃+* F) (v : Fin k ⊕ Fin k → F) : Fin k ⊕ Fin k → F :=
  fun i => σ (v i)

private theorem coordTwist_eq_comp (σ : F ≃+* F) (v : Fin k ⊕ Fin k → F) :
    coordTwist σ v = σ ∘ v := rfl

private theorem coordTwist_add (σ : F ≃+* F) (v w : Fin k ⊕ Fin k → F) :
    coordTwist σ (v + w) = coordTwist σ v + coordTwist σ w := by
  funext i
  exact map_add σ (v i) (w i)

private theorem coordTwist_smul (σ : F ≃+* F) (c : F) (v : Fin k ⊕ Fin k → F) :
    coordTwist σ (c • v) = σ c • coordTwist σ v := by
  funext i
  exact map_mul σ c (v i)

private theorem spForm_coordTwist (σ : F ≃+* F) (v w : Fin k ⊕ Fin k → F) :
    spForm k F (coordTwist σ v) (coordTwist σ w) = σ (spForm k F v w) :=
  spForm_comp_ringEquiv σ v w

private theorem spEnd_fieldSp_conj [CharP F 2] {σ : F ≃+* F}
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {m : ↥(StatedSp k F)} (hAm : ∀ x, A x = spEnd m (coordTwist σ x))
    (g : ↥(StatedSp k F)) (x : Fin k ⊕ Fin k → F) :
    spEnd ((fieldSp k F σ).trans (MulAut.conj m) g) (A x) = A (spEnd g x) := by
  have hinv : spEnd m⁻¹ (spEnd m (coordTwist σ x)) = coordTwist σ x := by
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
  have hβ : (fieldSp k F σ).trans (MulAut.conj m) g = m * fieldSp k F σ g * m⁻¹ := rfl
  rw [hβ, hAm x, hAm (spEnd g x), spEnd_mul, spEnd_mul]
  simp only [Module.End.mul_apply]
  change spEnd m (spEnd (fieldSp k F σ g) (spEnd m⁻¹ (spEnd m (coordTwist σ x)))) =
    spEnd m (coordTwist σ (spEnd g x))
  rw [hinv, coordTwist_eq_comp, spEnd_fieldSp]
  rfl

private theorem spTransvection_mem_fixing_of_spForm_eq_zero [CharP F 2]
    {y a : Fin k ⊕ Fin k → F} (ha : spForm k F a y = 0) :
    spTransvection a 1 ∈ fixing {y} :=
  (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr ha

private theorem conj_fieldSp_spTransvection [CharP F 2] {σ : F ≃+* F}
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {m : ↥(StatedSp k F)}
    (hAm : ∀ x, A x = spEnd m (coordTwist σ x))
    (hAdd : ∀ x w, A (x + w) = A x + A w) (hSmul : ∀ (c : F) x, A (c • x) = σ c • A x)
    (hIso : ∀ x w, spForm k F (A x) (A w) = σ (spForm k F x w))
    (hSurj : Function.Surjective A) (a : Fin k ⊕ Fin k → F) :
    (fieldSp k F σ).trans (MulAut.conj m) (spTransvection a 1) = spTransvection (A a) 1 := by
  refine eq_of_spEnd_eq fun z => ?_
  obtain ⟨x, rfl⟩ := hSurj z
  rw [spEnd_fieldSp_conj hAm, spEnd_spTransvection, spEnd_spTransvection, hAdd, hSmul, hIso]
  simp only [one_mul]

private theorem fixing_hom_ext {M : Type} [Group M] [Finite F] [CharP F 2]
    {y : Fin k ⊕ Fin k → F} {Φ Ψ : ↥(fixing {y}) →* M}
    (hgen : ∀ (a : Fin k ⊕ Fin k → F), a ≠ 0 → ∀ (hay : spForm k F a y = 0),
      Φ ⟨spTransvection a 1, spTransvection_mem_fixing_of_spForm_eq_zero hay⟩ =
        Ψ ⟨spTransvection a 1, spTransvection_mem_fixing_of_spForm_eq_zero hay⟩) :
    Φ = Ψ := by
  refine MonoidHom.ext fun g => ?_
  have hgy : spEnd g.1 y = y := by
    rw [spEnd_apply]
    exact mem_fixing.mp g.2 y (Set.mem_singleton y)
  have hcl := mem_closure_spTransvection_of_spEnd_apply_eq (k := k) hgy
  set s : Set (↥(StatedSp k F)) := (fun b => spTransvection b 1) '' {b | b ≠ 0 ∧ spForm k F y b = 0}
  have hsub : Subgroup.closure s ≤ fixing {y} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, rfl⟩
    exact (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (by
      rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt b y]
      exact hb.2)
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ hg : g ∈ fixing {y}, Φ ⟨g, hg⟩ = Ψ ⟨g, hg⟩) ?_ ?_ ?_ ?_ hcl g.2
  · rintro x ⟨b, hb, rfl⟩ hx
    have hby : spForm k F b y = 0 := by
      rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt b y]
      exact hb.2
    have h2 : (⟨spTransvection b 1, hx⟩ : ↥(fixing {y})) =
        ⟨spTransvection b 1, spTransvection_mem_fixing_of_spForm_eq_zero hby⟩ := Subtype.ext rfl
    rw [h2]
    exact hgen b hb.1 hby
  · intro hx
    have h1 : (⟨1, hx⟩ : ↥(fixing {y})) = 1 := Subtype.ext rfl
    rw [h1, map_one, map_one]
  · intro a b ha hb hpa hpb hab
    have h1 : (⟨a * b, hab⟩ : ↥(fixing {y})) = ⟨a, hsub ha⟩ * ⟨b, hsub hb⟩ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, hpa (hsub ha), hpb (hsub hb)]
  · intro a ha hpa ha'
    have h1 : (⟨a⁻¹, ha'⟩ : ↥(fixing {y})) = ⟨a, hsub ha⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_inv, map_inv, hpa (hsub ha)]

private theorem spTransvection_image_iff {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {β : ↥(StatedSp k F) ≃* ↥(StatedSp k F)} (hA0 : A 0 = 0)
    (hAinj : Function.Injective A) (hAsurj : Function.Surjective A)
    (hβT : ∀ a : Fin k ⊕ Fin k → F, β (spTransvection a 1) = spTransvection (A a) 1) :
    ∀ g : ↥(StatedSp k F),
      (∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ g = spTransvection a 1) ↔
        ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ β g = spTransvection a 1 := by
  intro g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨A a, fun h => ha (hAinj (h.trans hA0.symm)), hβT a⟩
  · rintro ⟨b, hb, hbT⟩
    obtain ⟨a, rfl⟩ := hAsurj b
    refine ⟨a, fun ha => hb (by rw [ha, hA0]), ?_⟩
    have h1 : β g = β (spTransvection a 1) := by rw [hbT, hβT]
    exact β.injective h1

private theorem exists_semilinear_isometry_extend [Finite F] [CharP F 2]
    {σ : F ≃+* F} {f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (hf_add : ∀ x z, spForm k F x y = 0 → spForm k F z y = 0 → f (x + z) = f x + f z)
    (hf_smul : ∀ (c : F) x, spForm k F x y = 0 → f (c • x) = σ c • f x)
    (hf_iso : ∀ x z, spForm k F x y = 0 → spForm k F z y = 0 →
      spForm k F (f x) (f z) = σ (spForm k F x z))
    (hf_maps : ∀ x, spForm k F x y = 0 → spForm k F (f x) y' = 0)
    (hf_surj : ∀ x', spForm k F x' y' = 0 → ∃ x, spForm k F x y = 0 ∧ f x = x')
    (hf_y : f y = y') :
    ∃ A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F),
      (∀ x, spForm k F x y = 0 → A x = f x) ∧ Function.Bijective A ∧
      (∀ x z, A (x + z) = A x + A z) ∧
      (∀ (c : F) x, A (c • x) = σ c • A x) ∧
      (∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)) ∧ A y = y' := by
  obtain ⟨z₀, hz₀⟩ := exists_spForm_ne_zero hy
  let z : Fin k ⊕ Fin k → F := (spForm k F z₀ y)⁻¹ • z₀
  have hz : spForm k F z y = 1 := by
    show spForm k F ((spForm k F z₀ y)⁻¹ • z₀) y = 1
    rw [LinearMap.BilinForm.smul_left, inv_mul_cancel₀ hz₀]
  obtain ⟨z', hz'⟩ := exists_spForm_comp_eq hz hf_add hf_smul hf_iso hf_maps hf_surj hf_y hy'
  have hzz : spForm k F z' z' = 0 := spForm_isAlt.self_eq_zero z'
  let A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F) := semilinearExtend σ f y z z'
  have hA_add : ∀ x w, A (x + w) = A x + A w :=
    fun x w => semilinearExtend_add hz hf_add x w
  have hA_smul : ∀ (c : F) x, A (c • x) = σ c • A x :=
    fun c x => semilinearExtend_smul hz hf_smul c x
  have hA_iso : ∀ x w, spForm k F (A x) (A w) = σ (spForm k F x w) :=
    fun x w => semilinearExtend_isometry hz hf_iso hz' hzz x w
  have hA_mem : ∀ x, spForm k F x y = 0 → A x = f x :=
    fun x hx => semilinearExtend_of_mem (σ := σ) (f := f) hx
  have hA_bij : Function.Bijective A :=
    Finite.injective_iff_bijective.mp (semilinearExtend_injective hz hf_add hf_iso hz' hzz)
  exact ⟨A, hA_mem, hA_bij, hA_add, hA_smul, hA_iso,
    semilinearExtend_self (σ := σ) (f := f) hf_y⟩

private theorem exists_spEnd_coordTwist_of_semilinear {σ : F ≃+* F}
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    (hA_add : ∀ x w, A (x + w) = A x + A w)
    (hA_smul : ∀ (c : F) x, A (c • x) = σ c • A x)
    (hA_iso : ∀ x w, spForm k F (A x) (A w) = σ (spForm k F x w)) :
    ∃ m : ↥(StatedSp k F), ∀ x, A x = spEnd m (coordTwist σ x) := by
  have htwist : ∀ x : Fin k ⊕ Fin k → F, coordTwist σ.symm (coordTwist σ x) = x :=
    fun x => by funext i; exact σ.symm_apply_apply (x i)
  let L : (Fin k ⊕ Fin k → F) →ₗ[F] (Fin k ⊕ Fin k → F) :=
    { toFun := fun w => A (coordTwist σ.symm w)
      map_add' := fun w w' => by rw [coordTwist_add, hA_add]
      map_smul' := fun c w => by
        rw [coordTwist_smul, hA_smul, σ.apply_symm_apply]
        rfl }
  have hL_apply : ∀ w, L w = A (coordTwist σ.symm w) := fun _ => rfl
  have hL_iso : ∀ x w, spForm k F (L x) (L w) = spForm k F x w := by
    intro x w
    rw [hL_apply, hL_apply, hA_iso, spForm_coordTwist, σ.apply_symm_apply]
  obtain ⟨m, hm⟩ := exists_sp_of_isometry (u := L) hL_iso
  refine ⟨m, fun x => ?_⟩
  rw [LinearMap.congr_fun hm (coordTwist σ x), hL_apply, htwist]

theorem exists_semilinear_of_fixing_equiv [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : ∀ p : ↥(fixing {y}),
      (∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (p : ↥(StatedSp k F)) = spTransvection a 1) ↔
        ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (α p : ↥(StatedSp k F)) = spTransvection a 1)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) :
    ∃ (σ : F ≃+* F) (A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F))
      (β : ↥(StatedSp k F) ≃* ↥(StatedSp k F)),
      Function.Bijective A ∧ (∀ x z, A (x + z) = A x + A z) ∧
      (∀ (c : F) x, A (c • x) = σ c • A x) ∧
      (∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)) ∧ A y = y' ∧
      (∀ g x, spEnd (β g) (A x) = A (spEnd g x)) ∧
      (∀ g, (∃ a, a ≠ 0 ∧ g = spTransvection a 1) ↔ ∃ a, a ≠ 0 ∧ β g = spTransvection a 1) ∧
      ∀ p : ↥(fixing {y}), β p = α p := by
  obtain ⟨σ, f, hf_add, hf_smul, hf_iso, hf_maps, hf_surj, hf_y, hf_alpha⟩ :=
    exists_semilinear_centreMap hk hF hy α hα hαy
  have hy' : y' ≠ 0 := ne_zero_of_mulEquiv_fixing hy α hαy
  obtain ⟨A, hA_mem, hA_bij, hA_add, hA_smul, hA_iso, hA_y⟩ :=
    exists_semilinear_isometry_extend hy hy' hf_add hf_smul hf_iso hf_maps hf_surj hf_y
  obtain ⟨m, hAm⟩ := exists_spEnd_coordTwist_of_semilinear hA_add hA_smul hA_iso
  let β : ↥(StatedSp k F) ≃* ↥(StatedSp k F) := (fieldSp k F σ).trans (MulAut.conj m)
  have hA_zero : A 0 = 0 := (AddMonoidHom.mk' A hA_add).map_zero
  refine ⟨σ, A, β, hA_bij, hA_add, hA_smul, hA_iso, hA_y, ?_, ?_, ?_⟩
  · exact fun g x => spEnd_fieldSp_conj hAm g x
  · exact spTransvection_image_iff hA_zero hA_bij.1 hA_bij.2
      (fun a => conj_fieldSp_spTransvection hAm hA_add hA_smul hA_iso hA_bij.2 a)
  · intro p
    have h := fixing_hom_ext
      (Φ := β.toMonoidHom.comp (fixing {y}).subtype)
      (Ψ := (fixing {y'}).subtype.comp α.toMonoidHom) (fun a ha hay => by
        change β (spTransvection a 1) =
          (α ⟨spTransvection a 1,
            spTransvection_mem_fixing_of_spForm_eq_zero hay⟩ : ↥(StatedSp k F))
        rw [show β (spTransvection a 1) = spTransvection (A a) 1 from
          conj_fieldSp_spTransvection hAm hA_add hA_smul hA_iso hA_bij.2 a, hA_mem a hay]
        exact (hf_alpha a ⟨spTransvection a 1, spTransvection_mem_fixing_of_spForm_eq_zero hay⟩
          hay rfl).symm)
    exact DFunLike.congr_fun h p

private def markedCenter : SpMarkedGroup k F := (1, Multiplicative.ofAdd 1)

private theorem markedCenter_mem (y : Fin k ⊕ Fin k → F) : markedCenter ∈ spMarkedStab y :=
  Subgroup.mem_comap.mpr (Subgroup.one_mem _)

private theorem markedCenter_comm (q : SpMarkedGroup k F) :
    markedCenter * q = q * markedCenter := by
  obtain ⟨g, ε⟩ := q
  simp only [markedCenter, Prod.mk_mul_mk, one_mul, mul_one, mul_comm]

private theorem spTransvection_one_ne_one [CharP F 2] {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) :
    spTransvection a 1 ≠ 1 := fun h =>
  ha ((eq_of_spTransvection_eq one_ne_zero ha ((spTransvection_zero 1).trans h.symm)).symm)

private theorem snd_mul_three_of_mem_spMarkedSet {p₁ p₂ p₃ : SpMarkedGroup k F}
    (h₁ : p₁ ∈ spMarkedSet) (h₂ : p₂ ∈ spMarkedSet) (h₃ : p₃ ∈ spMarkedSet) :
    (p₁ * p₂ * p₃).2 = Multiplicative.ofAdd 1 := by
  obtain ⟨a₁, -, rfl⟩ := h₁
  obtain ⟨a₂, -, rfl⟩ := h₂
  obtain ⟨a₃, -, rfl⟩ := h₃
  show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 :
    Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1
  decide

private theorem spTransvection_smul_mem_fixing [CharP F 2] {y : Fin k ⊕ Fin k → F} (c : F) :
    spTransvection (c • y) 1 ∈ fixing {y} := by
  refine spTransvection_mem_fixing_of_spForm_eq_zero ?_
  rw [LinearMap.BilinForm.smul_left, spForm_isAlt.self_eq_zero, mul_zero]

private theorem exists_markedCenter_eq_mul_three [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) :
    ∃ p₁ p₂ p₃ : ↥(spMarkedStab y),
      (p₁ : SpMarkedGroup k F) ∈ spMarkedSet ∧ (p₂ : SpMarkedGroup k F) ∈ spMarkedSet ∧
      (p₃ : SpMarkedGroup k F) ∈ spMarkedSet ∧
      p₁ * p₂ * p₃ = ⟨markedCenter, markedCenter_mem y⟩ := by
  classical
  have hcard : ({0, 1} : Finset F).card < Fintype.card F := by
    have h4 : 4 ≤ Fintype.card F := hF
    have h2 : ({0, 1} : Finset F).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    omega
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hb1 : (1 : F) + b ≠ 0 := by
    intro h
    apply hb.2
    have h2 : (1 : F) + (1 + b) = 1 + 0 := by rw [h]
    rwa [← add_assoc, CharTwo.add_self_eq_zero, zero_add, add_zero] at h2
  have h3 : 1 + b * b + (1 + b) * (1 + b) = 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (b * b + b + 1) * h2
  have hT : spTransvection y 1 * spTransvection (b • y) 1 *
      spTransvection ((1 + b) • y) 1 = 1 := by
    rw [spTransvection_smul b y 1, spTransvection_smul (1 + b) y 1,
      spConf_transvection_mul, spConf_transvection_mul]
    refine eq_of_spEnd_eq fun z => ?_
    rw [spEnd_spTransvection, spEnd_one, Module.End.one_apply]
    simp only [mul_one, h3, zero_mul, zero_smul, add_zero]
  have hε : (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 :
      Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1 := by decide
  have hmain : ((spTransvection y 1, Multiplicative.ofAdd 1) *
      (spTransvection (b • y) 1, Multiplicative.ofAdd 1) *
      (spTransvection ((1 + b) • y) 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) =
      markedCenter := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, hT, hε]
    rfl
  refine ⟨⟨(spTransvection y 1, Multiplicative.ofAdd 1),
      Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton y 1)⟩,
    ⟨(spTransvection (b • y) 1, Multiplicative.ofAdd 1),
      Subgroup.mem_comap.mpr (spTransvection_smul_mem_fixing b)⟩,
    ⟨(spTransvection ((1 + b) • y) 1, Multiplicative.ofAdd 1),
      Subgroup.mem_comap.mpr (spTransvection_smul_mem_fixing (1 + b))⟩,
    ⟨y, hy, rfl⟩, ⟨b • y, smul_ne_zero hb.1 hy, rfl⟩, ⟨(1 + b) • y, smul_ne_zero hb1 hy, rfl⟩,
    Subtype.ext hmain⟩

private theorem exists_spTransvection_of_commute [CharP F 2]
    {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) {w : ↥(StatedSp k F)}
    (hcomm : ∀ a : Fin k ⊕ Fin k → F, a ≠ 0 → spForm k F a y = 0 →
      w * spTransvection a 1 = spTransvection a 1 * w) :
    ∃ c : F, w = spTransvection y c := by
  have hfix : ∀ a : Fin k ⊕ Fin k → F, spForm k F a y = 0 → spEnd w a = a := by
    intro a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero]
    · exact (commute_spTransvection_one_iff ha0).mp (hcomm a ha0 ha)
  obtain ⟨z₀, hz₀⟩ := exists_spForm_ne_zero hy
  have hz : spForm k F ((spForm k F z₀ y)⁻¹ • z₀) y = 1 := by
    rw [LinearMap.BilinForm.smul_left, inv_mul_cancel₀ hz₀]
  refine exists_eq_spTransvection_of_sub_mem_span w fun x => ?_
  have hu : ∀ e, spForm k F e y = 0 → spForm k F (spEnd w x - x) e = 0 := by
    intro e he
    have h1 : spEnd w e = e := hfix e he
    have h2 : spForm k F (spEnd w x) e = spForm k F x e := by
      conv_lhs => rw [← h1]
      exact spEnd_isometry w x e
    rw [map_sub, LinearMap.sub_apply, h2, sub_self]
  have hspan := eq_smul_of_forall_spForm_eq_zero hz hu
  exact Submodule.mem_span_singleton.mpr ⟨spForm k F (spEnd w x - x) ((spForm k F z₀ y)⁻¹ • z₀),
    hspan.symm⟩

private theorem snd_markedCenter_apply_eq [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet) :
    (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F).2 =
      Multiplicative.ofAdd 1 := by
  obtain ⟨p₁, p₂, p₃, hm₁, hm₂, hm₃, hprod⟩ := exists_markedCenter_eq_mul_three hF hy
  rw [← hprod]
  have hmem := snd_mul_three_of_mem_spMarkedSet (hα p₁ |>.mp hm₁) (hα p₂ |>.mp hm₂)
    (hα p₃ |>.mp hm₃)
  simpa [map_mul] using hmem

private theorem commute_spTransvection_of_central [CharP F 2] {y : Fin k ⊕ Fin k → F}
    {P : ↥(spMarkedStab y)} (hcentral : ∀ q : ↥(spMarkedStab y), P * q = q * P) :
    ∀ a : Fin k ⊕ Fin k → F, spForm k F a y = 0 →
      P.1.1 * spTransvection a 1 = spTransvection a 1 * P.1.1 := by
  intro a hay
  have hthis := hcentral ⟨(spTransvection a 1, 1),
    Subgroup.mem_comap.mpr (spTransvection_mem_fixing_of_spForm_eq_zero hay)⟩
  exact congrArg (fun r : ↥(spMarkedStab y) => r.1.1) hthis

private theorem markedCenter_apply_eq [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet) :
    (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter := by
  let Z : ↥(spMarkedStab y) := ⟨markedCenter, markedCenter_mem y⟩
  set P : ↥(spMarkedStab y') := α Z with hP
  have h2 : P.1.2 = Multiplicative.ofAdd 1 :=
    snd_markedCenter_apply_eq hF hy α hα
  have hZc : Z ∈ Set.center ↥(spMarkedStab y) := Semigroup.mem_center_iff.mpr fun q =>
    Subtype.ext (markedCenter_comm (q : SpMarkedGroup k F)).symm
  have hcentral : ∀ q : ↥(spMarkedStab y'), P * q = q * P := fun q =>
    (Semigroup.mem_center_iff.mp (MulEquivClass.apply_mem_center α hZc) q).symm
  obtain ⟨c, hcT⟩ := exists_spTransvection_of_commute hy'
    (fun a _ hay => commute_spTransvection_of_central hcentral a hay)
  have hc0 : c = 0 := by
    rcases eq_or_ne c 0 with hc | hc
    · exact hc
    · exfalso
      obtain ⟨d, hd⟩ := isSquare_of_charTwo' c
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hd
        exact hc hd
      have hPc : (P : SpMarkedGroup k F) =
          (spTransvection (d • y') 1, Multiplicative.ofAdd 1) := by
        refine Prod.ext ?_ ?_
        · show P.1.1 = spTransvection (d • y') 1
          rw [hcT, spTransvection_smul d y' 1, ← hd, mul_one]
        · show P.1.2 = Multiplicative.ofAdd 1
          exact h2
      have hzmark : markedCenter ∈ spMarkedSet :=
        (hα Z).mpr (by
          rw [← hP]
          exact ⟨d • y', smul_ne_zero hd0 hy', hPc⟩)
      obtain ⟨a, ha, hza⟩ := hzmark
      exact spTransvection_one_ne_one ha (congrArg Prod.fst hza).symm
  have hP1 : P.1.1 = 1 := by
    have h0 := spTransvection_smul (0 : F) y' 1
    rw [zero_smul, spTransvection_zero, zero_mul, zero_mul] at h0
    rw [hcT, hc0, ← h0]
  refine Prod.ext ?_ ?_
  · show P.1.1 = markedCenter.1
    rw [hP1]
    rfl
  · show P.1.2 = markedCenter.2
    rw [h2]
    rfl

private def markedStabOf {y : Fin k ⊕ Fin k → F} (g : ↥(fixing {y})) : ↥(spMarkedStab y) :=
  ⟨(g.1, 1), Subgroup.mem_comap.mpr g.2⟩

private def fixingOfMarked {y : Fin k ⊕ Fin k → F} (p : ↥(spMarkedStab y)) : ↥(fixing {y}) :=
  ⟨p.1.1, Subgroup.mem_comap.mp p.2⟩

private theorem markedStabOf_mul {y : Fin k ⊕ Fin k → F} (g h : ↥(fixing {y})) :
    markedStabOf (g * h) = markedStabOf g * markedStabOf h := Subtype.ext rfl

private theorem markedStabOf_one {y : Fin k ⊕ Fin k → F} :
    markedStabOf (1 : ↥(fixing {y})) = 1 := Subtype.ext rfl

private theorem fixingOfMarked_markedStabOf {y : Fin k ⊕ Fin k → F} (g : ↥(fixing {y})) :
    fixingOfMarked (markedStabOf g) = g := Subtype.ext rfl

private theorem markedStabOf_fixingOfMarked {y : Fin k ⊕ Fin k → F} (p : ↥(spMarkedStab y))
    (hp : p.1.2 = 1) : markedStabOf (fixingOfMarked p) = p := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · rfl
  · show (1 : Multiplicative (ZMod 2)) = p.1.2
    rw [hp]

private def chiOfMarked {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y')) :
    ↥(fixing {y}) →* Multiplicative (ZMod 2) where
  toFun g := (α (markedStabOf g)).1.2
  map_one' := by rw [markedStabOf_one, map_one]; rfl
  map_mul' g h := by rw [markedStabOf_mul, map_mul]; rfl

private def markedStabEquivHom {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y')) :
    ↥(fixing {y}) →* ↥(fixing {y'}) where
  toFun g := fixingOfMarked (α (markedStabOf g))
  map_one' := by
    rw [markedStabOf_one, map_one]
    exact Subtype.ext rfl
  map_mul' g h := by
    rw [markedStabOf_mul, map_mul]
    exact Subtype.ext rfl

private theorem markedStabEquivHom_injective {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hsnd : ∀ g : ↥(fixing {y}), (α (markedStabOf g)).1.2 = 1) :
    Function.Injective (markedStabEquivHom α) := by
  intro g h hgh
  have h1 : α (markedStabOf g) = α (markedStabOf h) := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · have h2 := congrArg (fun x : ↥(fixing {y'}) => x.1) hgh
      simpa [markedStabEquivHom, fixingOfMarked] using h2
    · rw [hsnd g, hsnd h]
  have h2 : markedStabOf g = markedStabOf h := α.injective h1
  exact Subtype.ext (congrArg (fun x : ↥(spMarkedStab y) => x.1.1) h2)

private theorem markedStabEquivHom_surjective {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hsndsym : ∀ g : ↥(fixing {y'}), (α.symm (markedStabOf g)).1.2 = 1) :
    Function.Surjective (markedStabEquivHom α) := by
  intro h
  refine ⟨fixingOfMarked (α.symm (markedStabOf h)), ?_⟩
  have h1 : markedStabOf (fixingOfMarked (α.symm (markedStabOf h))) = α.symm (markedStabOf h) :=
    markedStabOf_fixingOfMarked _ (hsndsym h)
  show fixingOfMarked (α (markedStabOf (fixingOfMarked (α.symm (markedStabOf h))))) = h
  rw [h1, α.apply_symm_apply]
  exact fixingOfMarked_markedStabOf h

private theorem markedCenter_fixes_centralZ2 [Fintype F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter) :
    ∀ ε : Multiplicative (ZMod 2),
      (α ⟨(1, ε), Subgroup.mem_comap.mpr (Subgroup.one_mem _)⟩ : SpMarkedGroup k F) = (1, ε) := by
  intro ε
  have h2 : ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by revert ε; decide
  rcases h2 with h | h
  · rw [h]
    have h1 : (⟨(1, (1 : Multiplicative (ZMod 2))),
        Subgroup.mem_comap.mpr (Subgroup.one_mem _)⟩ : ↥(spMarkedStab y)) = 1 := Subtype.ext rfl
    rw [h1, map_one]
    rfl
  · rw [h]
    exact hZ

private theorem markedStabOf_mul_center {y : Fin k ⊕ Fin k → F} (p : ↥(fixing {y})) :
    markedStabOf p * (⟨markedCenter, markedCenter_mem y⟩ : ↥(spMarkedStab y)) =
      ⟨((p.1, Multiplicative.ofAdd 1) : SpMarkedGroup k F), Subgroup.mem_comap.mpr p.2⟩ := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show p.1 * 1 = p.1
    rw [mul_one]
  · show (1 : Multiplicative (ZMod 2)) * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 1
    rw [one_mul]

private theorem markedStabEquivHom_mul_center {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter)
    (p : ↥(fixing {y})) :
    α (markedStabOf p) * (⟨markedCenter, markedCenter_mem y'⟩ : ↥(spMarkedStab y')) =
      α ⟨((p.1, Multiplicative.ofAdd 1) : SpMarkedGroup k F),
        Subgroup.mem_comap.mpr p.2⟩ := by
  have hZ' : α ⟨markedCenter, markedCenter_mem y⟩ = ⟨markedCenter, markedCenter_mem y'⟩ :=
    Subtype.ext hZ
  rw [← hZ', ← map_mul, markedStabOf_mul_center]

private theorem markedStabEquivHom_transvection_mpr [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter)
    (hsnd : ∀ g : ↥(fixing {y}), (α (markedStabOf g)).1.2 = 1)
    (p : ↥(fixing {y})) (b : Fin k ⊕ Fin k → F) (hb : b ≠ 0)
    (hbT : (markedStabEquivHom α p).1 = spTransvection b 1) :
    ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ p.1 = spTransvection a 1 := by
  have hsndp : (α (markedStabOf p)).1.2 = 1 := hsnd p
  have h2 := markedStabEquivHom_mul_center α hZ p
  have h3 := congrArg (fun x : ↥(spMarkedStab y') => x.1) h2
  have hmark : (α ⟨((p.1, Multiplicative.ofAdd 1) : SpMarkedGroup k F),
      Subgroup.mem_comap.mpr p.2⟩ : ↥(spMarkedStab y')).1 =
      ((spTransvection b 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) := by
    rw [← h3]
    refine Prod.ext ?_ ?_
    · show (α (markedStabOf p)).1.1 * 1 = spTransvection b 1
      rw [mul_one]
      exact hbT
    · show (α (markedStabOf p)).1.2 * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 1
      rw [hsndp, one_mul]
  have hmarkmem : ((p.1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) ∈ spMarkedSet := by
    refine (hα ⟨((p.1, Multiplicative.ofAdd 1) : SpMarkedGroup k F),
      Subgroup.mem_comap.mpr p.2⟩).mpr ?_
    rw [hmark]
    exact ⟨b, hb, rfl⟩
  obtain ⟨a, ha, ham⟩ := hmarkmem
  exact ⟨a, ha, congrArg Prod.fst ham⟩

private theorem markedStabEquivHom_snd_of_mark [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter)
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) (hay : spForm k F a y = 0) :
    (α (markedStabOf ⟨spTransvection a 1,
      spTransvection_mem_fixing_of_spForm_eq_zero hay⟩)).1.2 = 1 := by
  have hmem : spTransvection a 1 ∈ fixing {y} := spTransvection_mem_fixing_of_spForm_eq_zero hay
  have hmarkmem : ((spTransvection a 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) ∈
      spMarkedStab y := Subgroup.mem_comap.mpr hmem
  have h2 := markedStabEquivHom_mul_center α hZ ⟨spTransvection a 1, hmem⟩
  obtain ⟨b, hb, hbm⟩ := (hα ⟨(spTransvection a 1, Multiplicative.ofAdd 1), hmarkmem⟩).mp
    (show ((spTransvection a 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) ∈ spMarkedSet from
      ⟨a, ha, rfl⟩)
  have hmark2 : (α ⟨(spTransvection a 1, Multiplicative.ofAdd 1), hmarkmem⟩ :
      ↥(spMarkedStab y')).1.2 = Multiplicative.ofAdd 1 := by
    have h4 := congrArg Prod.snd hbm
    simpa using h4
  have h3 := congrArg (fun x : ↥(spMarkedStab y') => x.1.2) h2
  have h3' : (α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.2 * Multiplicative.ofAdd 1 =
      Multiplicative.ofAdd 1 := by
    simpa [markedCenter, hmark2] using h3
  have h4 : (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 :
      Multiplicative (ZMod 2)) = 1 := by decide
  show (α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.2 = 1
  calc (α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.2
      = (α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.2 *
          (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1) := by rw [h4, mul_one]
    _ = ((α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.2 * Multiplicative.ofAdd 1) *
          Multiplicative.ofAdd 1 := by rw [mul_assoc]
    _ = Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 := by rw [h3']
    _ = 1 := h4

private theorem markedStabEquivHom_snd_eq_one [Finite F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter) :
    ∀ g : ↥(fixing {y}), (α (markedStabOf g)).1.2 = 1 := by
  have h := fixing_hom_ext (Φ := chiOfMarked α) (Ψ := 1)
    (fun a ha hay => markedStabEquivHom_snd_of_mark α hα hZ ha hay)
  intro g
  exact DFunLike.congr_fun h g

private theorem markedStabEquivHom_snd_eq_one_symm [Fintype F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F} (hF : 4 ≤ Fintype.card F) (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet) :
    ∀ g : ↥(fixing {y'}), (α.symm (markedStabOf g)).1.2 = 1 := by
  have hαsym : ∀ p : ↥(spMarkedStab y'),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α.symm p : SpMarkedGroup k F) ∈ spMarkedSet := by
    intro p
    have h := (hα (α.symm p)).symm
    rwa [α.apply_symm_apply] at h
  have hZsym : (α.symm ⟨markedCenter, markedCenter_mem y'⟩ : SpMarkedGroup k F) = markedCenter :=
    markedCenter_apply_eq hF hy' hy α.symm hαsym
  exact markedStabEquivHom_snd_eq_one α.symm hαsym hZsym

private theorem markedStabEquivHom_spTransvection_y [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter)
    (hαy : (α ⟨(spTransvection y 1, Multiplicative.ofAdd 1),
        Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton y 1)⟩ : SpMarkedGroup k F) =
      (spTransvection y' 1, Multiplicative.ofAdd 1)) :
    ((markedStabEquivHom α ⟨spTransvection y 1,
      spTransvection_mem_fixing_singleton y 1⟩ : ↥(fixing {y'})) : ↥(StatedSp k F)) =
      spTransvection y' 1 := by
  have hmem : spTransvection y 1 ∈ fixing {y} := spTransvection_mem_fixing_singleton y 1
  have hmarkmem : ((spTransvection y 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) ∈
      spMarkedStab y := Subgroup.mem_comap.mpr hmem
  have h2 := markedStabEquivHom_mul_center α hZ ⟨spTransvection y 1, hmem⟩
  have hmark : (α ⟨(spTransvection y 1, Multiplicative.ofAdd 1), hmarkmem⟩ :
      ↥(spMarkedStab y')).1.1 = spTransvection y' 1 := by
    have h4 : (α ⟨(spTransvection y 1, Multiplicative.ofAdd 1), hmarkmem⟩ :
        SpMarkedGroup k F) = (spTransvection y' 1, Multiplicative.ofAdd 1) := hαy
    have h5 := congrArg Prod.fst h4
    simpa using h5
  have h3 := congrArg (fun x : ↥(spMarkedStab y') => x.1.1) h2
  have h3' : (α (markedStabOf ⟨spTransvection y 1, hmem⟩)).1.1 = spTransvection y' 1 := by
    have h6 : (α (markedStabOf ⟨spTransvection y 1, hmem⟩)).1.1 =
        (α ⟨(spTransvection y 1, Multiplicative.ofAdd 1), hmarkmem⟩).1.1 := by
      simpa [markedCenter] using h3
    rw [h6, hmark]
  show (α (markedStabOf ⟨spTransvection y 1, hmem⟩)).1.1 = spTransvection y' 1
  exact h3'

private theorem markedStabEquivHom_eq_marked [Fintype F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter)
    (hsnd : ∀ g : ↥(fixing {y}), (α (markedStabOf g)).1.2 = 1)
    (β : ↥(StatedSp k F) ≃* ↥(StatedSp k F))
    (hβeq : ∀ g : ↥(fixing {y}), β g = markedStabEquivHom α g) :
    ∀ p : ↥(spMarkedStab y),
      ((β.prodCongr (MulEquiv.refl (Multiplicative (ZMod 2)))) p : SpMarkedGroup k F) =
        (α p : SpMarkedGroup k F) := by
  have hfixZ2 := markedCenter_fixes_centralZ2 α hZ
  intro p
  have hmem1 : p.1.1 ∈ fixing {y} := Subgroup.mem_comap.mp p.2
  have hdecomp : markedStabOf ⟨p.1.1, hmem1⟩ *
      (⟨(1, p.1.2), Subgroup.mem_comap.mpr (Subgroup.one_mem _)⟩ : ↥(spMarkedStab y)) = p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show p.1.1 * 1 = p.1.1
      rw [mul_one]
    · show (1 : Multiplicative (ZMod 2)) * p.1.2 = p.1.2
      rw [one_mul]
  have hβp : (β.prodCongr (MulEquiv.refl (Multiplicative (ZMod 2)))) p =
      ((α (markedStabOf ⟨p.1.1, hmem1⟩)).1.1, p.1.2) := by
    refine Prod.ext ?_ ?_
    · show β p.1.1 = (α (markedStabOf ⟨p.1.1, hmem1⟩)).1.1
      rw [hβeq ⟨p.1.1, hmem1⟩]
      rfl
    · rfl
  have hαp : (α p : SpMarkedGroup k F) =
      ((α (markedStabOf ⟨p.1.1, hmem1⟩)).1.1, p.1.2) := by
    have h1 : (α p : SpMarkedGroup k F) =
        (↑(α (markedStabOf ⟨p.1.1, hmem1⟩)) : SpMarkedGroup k F) *
          (↑(α ⟨(1, p.1.2), Subgroup.mem_comap.mpr (Subgroup.one_mem _)⟩) :
            SpMarkedGroup k F) := by
      conv_lhs => rw [← hdecomp]
      rw [map_mul]
      rfl
    rw [h1, hfixZ2 p.1.2]
    refine Prod.ext ?_ ?_
    · show ((↑(α (markedStabOf ⟨p.1.1, hmem1⟩)) : SpMarkedGroup k F)).1 * 1 =
        ((↑(α (markedStabOf ⟨p.1.1, hmem1⟩)) : SpMarkedGroup k F)).1
      rw [mul_one]
    · show ((↑(α (markedStabOf ⟨p.1.1, hmem1⟩)) : SpMarkedGroup k F)).2 * p.1.2 = p.1.2
      rw [hsnd ⟨p.1.1, hmem1⟩, one_mul]
  rw [hβp, ← hαp]

private theorem markedStabEquivHom_transvection_iff [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter)
    (hsnd : ∀ g : ↥(fixing {y}), (α (markedStabOf g)).1.2 = 1) :
    ∀ p : ↥(fixing {y}),
      (∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ p.1 = spTransvection a 1) ↔
        ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (markedStabEquivHom α p).1 = spTransvection a 1 := by
  intro p
  constructor
  · rintro ⟨a, ha, haT⟩
    have hmem : spTransvection a 1 ∈ fixing {y} := by
      rw [← haT]
      exact p.2
    have hmarkmem : ((spTransvection a 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) ∈
        spMarkedStab y := Subgroup.mem_comap.mpr hmem
    have h2 := markedStabEquivHom_mul_center α hZ ⟨spTransvection a 1, hmem⟩
    obtain ⟨b, hb, hbm⟩ := (hα ⟨(spTransvection a 1, Multiplicative.ofAdd 1), hmarkmem⟩).mp
      (show ((spTransvection a 1, Multiplicative.ofAdd 1) : SpMarkedGroup k F) ∈ spMarkedSet from
        ⟨a, ha, rfl⟩)
    have hbm1 : (α ⟨(spTransvection a 1, Multiplicative.ofAdd 1), hmarkmem⟩ :
        ↥(spMarkedStab y')).1.1 = spTransvection b 1 := by
      have h3 := congrArg Prod.fst hbm
      simpa using h3
    refine ⟨b, hb, ?_⟩
    have hfirst : (α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.1 =
        (α ⟨(spTransvection a 1, Multiplicative.ofAdd 1), hmarkmem⟩).1.1 := by
      have h3 := congrArg (fun x : ↥(spMarkedStab y') => x.1.1) h2
      simpa [markedCenter] using h3
    rw [show p = ⟨spTransvection a 1, hmem⟩ from Subtype.ext haT]
    change (α (markedStabOf ⟨spTransvection a 1, hmem⟩)).1.1 = spTransvection b 1
    rw [hfirst, hbm1]
  · rintro ⟨b, hb, hbT⟩
    exact markedStabEquivHom_transvection_mpr α hα hZ hsnd p b hb hbT

private theorem ne_zero_of_mulEquiv_spMarkedStab [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (hy : y ≠ 0) (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hαy : (α ⟨(spTransvection y 1, Multiplicative.ofAdd 1),
        Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton y 1)⟩ : SpMarkedGroup k F) =
      (spTransvection y' 1, Multiplicative.ofAdd 1)) :
    y' ≠ 0 := by
  intro hy'0
  obtain ⟨a, ha, haeq⟩ :=
    (hα ⟨(spTransvection y 1, Multiplicative.ofAdd 1),
      Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton y 1)⟩).mp
      ⟨y, hy, rfl⟩
  have hTa : spTransvection y' 1 = spTransvection a 1 :=
    congrArg Prod.fst (hαy.symm.trans haeq)
  rw [hy'0, spTransvection_zero] at hTa
  exact spTransvection_one_ne_one ha hTa.symm

theorem exists_spMarked_extension [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(spMarkedStab y) ≃* ↥(spMarkedStab y'))
    (hα : ∀ p : ↥(spMarkedStab y),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hαy : (α ⟨(spTransvection y 1, Multiplicative.ofAdd 1),
        Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton y 1)⟩ : SpMarkedGroup k F) =
      (spTransvection y' 1, Multiplicative.ofAdd 1)) :
    ∃ (σ : F ≃+* F) (A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F))
      (β : SpMarkedGroup k F ≃* SpMarkedGroup k F),
      Function.Bijective A ∧ (∀ x z, A (x + z) = A x + A z) ∧
      (∀ (c : F) x, A (c • x) = σ c • A x) ∧
      (∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)) ∧ A y = y' ∧
      (∀ p x, spEnd (β p).1 (A x) = A (spEnd p.1 x)) ∧ (∀ p, (β p).2 = p.2) ∧
      ∀ p : ↥(spMarkedStab y), β p = α p := by
  classical
  have hy' : y' ≠ 0 := ne_zero_of_mulEquiv_spMarkedStab hy α hα hαy
  have hZ : (α ⟨markedCenter, markedCenter_mem y⟩ : SpMarkedGroup k F) = markedCenter :=
    markedCenter_apply_eq hF hy hy' α hα
  have hsnd : ∀ g : ↥(fixing {y}), (α (markedStabOf g)).1.2 = 1 :=
    markedStabEquivHom_snd_eq_one α hα hZ
  have hsndsym : ∀ g : ↥(fixing {y'}), (α.symm (markedStabOf g)).1.2 = 1 :=
    markedStabEquivHom_snd_eq_one_symm hF hy hy' α hα
  have hα₁_bij : Function.Bijective (markedStabEquivHom α) :=
    ⟨markedStabEquivHom_injective α hsnd, markedStabEquivHom_surjective α hsndsym⟩
  let α₁ : ↥(fixing {y}) ≃* ↥(fixing {y'}) := MulEquiv.ofBijective (markedStabEquivHom α) hα₁_bij
  have hα₁_apply : ∀ g, α₁ g = markedStabEquivHom α g := fun g => rfl
  have htrans : ∀ p : ↥(fixing {y}),
      (∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ p.1 = spTransvection a 1) ↔
        ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (α₁ p : ↥(StatedSp k F)) = spTransvection a 1 := by
    intro p
    rw [hα₁_apply]
    exact markedStabEquivHom_transvection_iff α hα hZ hsnd p
  have hα₁y : (α₁ ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1 := by
    rw [hα₁_apply]
    exact markedStabEquivHom_spTransvection_y α hZ hαy
  obtain ⟨σ, A, β, hA_bij, hA_add, hA_smul, hA_iso, hA_y, hβconj, hβT, hβeq⟩ :=
    exists_semilinear_of_fixing_equiv hk hF hy α₁ htrans hα₁y
  refine ⟨σ, A, β.prodCongr (MulEquiv.refl _), hA_bij, hA_add, hA_smul, hA_iso, hA_y, ?_, ?_, ?_⟩
  · intro p x
    exact hβconj p.1 x
  · intro p
    rfl
  · exact markedStabEquivHom_eq_marked α hZ hsnd β hβeq

end CFSG.OddTranspositions.PartThree.ElevenSp

end
