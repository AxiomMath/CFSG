module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Orbit
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Mat
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Refl
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Pair
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthRefl
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Witt
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K]

@[expose] def oPhiMat : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of ![![1, 0, 0, 0], ![0, -1, 1, -1], ![0, 1, -1, -1], ![0, 1, 1, 0]]

@[expose] def oPhiOneMats : Set (Matrix (Fin 4) (Fin 4) K) :=
  {diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1, oPhiMat}

end Matrices

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private def w : Fin 4 → ZMod 3 := fun i => if i = 3 then -1 else 1

private def FormPreserving (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Prop :=
  ∀ x : Fin 4 → ZMod 3,
    (∑ i : Fin 4, w i • ((M.mulVec x) i * (M.mulVec x) i)) =
    (∑ i : Fin 4, w i • ((x i) * (x i)))

private lemma FormPreserving.diagSignMat_zero : FormPreserving (diagSignMat 0) := by
  unfold FormPreserving
  decide +kernel

private lemma FormPreserving.pijMat_0_1_1 : FormPreserving (pijMat 0 1 1) := by
  unfold FormPreserving
  decide +kernel

private lemma FormPreserving.pijMat_1_2_1 : FormPreserving (pijMat 1 2 1) := by
  unfold FormPreserving
  decide +kernel

private lemma FormPreserving.oPhiMat : FormPreserving (oPhiMat) := by
  unfold FormPreserving
  decide +kernel

private lemma isIsom_of_toMatrix_eq {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {f : Module.Basis (Fin 4) (ZMod 3) U}
    {g : U ≃ₗ[ZMod 3] U} {M : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (hg : LinearMap.toMatrix f f g.toLinearMap = M)
    (hM : FormPreserving M) :
    IsIsom 3 (phiForm f) g := by
  intro v
  dsimp [phiForm]
  rw [QuadraticMap.weightedSumSquares_apply, QuadraticMap.weightedSumSquares_apply]
  have hrepr : f.repr (g v) = M.mulVec (f.repr v) := by
    rw [← hg]
    rw [LinearMap.toMatrix_mulVec_repr]
    simp
  rw [hrepr]
  exact hM (f.repr v)

theorem isIsom_phiForm_of_mem_oPhiOne (hp : p = 3) (f : Module.Basis (Fin 4) (ZMod p) U)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ basisClosure f oPhiOneMats) : IsIsom p (phiForm f) g := by
  subst hp
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq] at hx
    simp only [oPhiOneMats, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hM | hM | hM | hM
    · exact isIsom_of_toMatrix_eq (f := f) (hg := hM) FormPreserving.diagSignMat_zero
    · exact isIsom_of_toMatrix_eq (f := f) (hg := hM) FormPreserving.pijMat_0_1_1
    · exact isIsom_of_toMatrix_eq (f := f) (hg := hM) FormPreserving.pijMat_1_2_1
    · exact isIsom_of_toMatrix_eq (f := f) (hg := hM) FormPreserving.oPhiMat
  | one =>
    intro v
    simp
  | mul x y hx hy IHa IHb =>
    intro v
    calc (phiForm f) ((x * y) v) = (phiForm f) (x (y v)) := by rw [LinearEquiv.mul_apply]
    _ = (phiForm f) (y v) := IHa (y v)
    _ = (phiForm f) v := IHb v
  | inv x hx IH =>
    intro v
    have h : (phiForm f) (x ((x⁻¹) v)) = (phiForm f) ((x⁻¹) v) := IH ((x⁻¹) v)
    have h_inv : x ((x⁻¹) v) = v := by simp
    rw [h_inv] at h
    exact h.symm

section MemOPhiOne

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U]

private lemma oPhiOrbitLevels_mem_basisClosure (f : Module.Basis (Fin 4) (ZMod 3) U) (n : ℕ)
    (v : Fin 4 → ZMod 3) (hv : v ∈ oPhiOrbitLevels n) :
    ∃ w ∈ basisClosure f (oPhiOneMats : Set (Matrix (Fin 4) (Fin 4) (ZMod 3))),
      v = (LinearMap.toMatrix f f w.toLinearMap).mulVec (Pi.single 3 1) := by
  induction n generalizing v with
  | zero =>
    simp only [oPhiOrbitLevels, Finset.mem_singleton] at hv
    subst hv
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    ext i
    fin_cases i <;> simp
  | succ n ih =>
    simp only [oPhiOrbitLevels, oPhiOrbitStep, Finset.mem_union, Finset.mem_biUnion,
      List.mem_toFinset, List.mem_map] at hv
    rcases hv with hv | hv | hv
    · exact ih v hv
    · exact ih v hv
    · obtain ⟨v0, hv0, M, hM, hv_eq⟩ := hv
      obtain ⟨w0, hw0, hw0v⟩ := ih v0 hv0
      have hMmem : M ∈ (oPhiOneMats : Set (Matrix (Fin 4) (Fin 4) (ZMod 3))) := by
        have hM' := hM
        simp only [oPhiOrbitGens, List.mem_cons, List.not_mem_nil, or_false] at hM'
        rcases hM' with rfl | rfl | rfl | rfl <;> simp [oPhiOneMats, oPhiMatZ, oPhiMat]
      have hMdet : IsUnit M.det := by
        have hM' := hM
        simp only [oPhiOrbitGens, List.mem_cons, List.not_mem_nil, or_false] at hM'
        rcases hM' with rfl | rfl | rfl | rfl
        · exact Matrix.isUnit_det_of_right_inverse (diagSignMat_mul_self 0)
        · exact Matrix.isUnit_det_of_right_inverse
            (pijMat_mul_self (by decide +kernel : (0 : Fin 4) ≠ 1)
              (by norm_num : (1 : ZMod 3) ≠ 0))
        · exact Matrix.isUnit_det_of_right_inverse
            (pijMat_mul_self (by decide +kernel : (1 : Fin 4) ≠ 2)
              (by norm_num : (1 : ZMod 3) ≠ 0))
        · decide +kernel
      obtain ⟨g, hg, hgM⟩ := exists_mem_basisClosure_toMatrix_eq f hMmem hMdet
      refine ⟨g * w0, Subgroup.mul_mem _ hg hw0, ?_⟩
      rw [← hv_eq, hw0v, ← hgM, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.toMatrix_mul, Matrix.mulVec_mulVec]

private lemma phiForm_eq_oPhiQ (f : Module.Basis (Fin 4) (ZMod 3) U) (x : U) :
    phiForm f x = oPhiQ (f.repr x) := by
  rw [phiForm_apply]
  simp only [oPhiQ, Fin.sum_univ_four]
  simp
  ring

private lemma polar_comp_of_isIsom {f : Module.Basis (Fin 4) (ZMod 3) U}
    {h : U ≃ₗ[ZMod 3] U} (hh : IsIsom 3 (phiForm f) h) (x y : U) :
    QuadraticMap.polar (phiForm f) (h x) (h y) = QuadraticMap.polar (phiForm f) x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hh, hh, hh]

private lemma castSucc_ne_three (i : Fin 3) : i.castSucc ≠ (3 : Fin 4) := by
  intro h
  have hv := congrArg Fin.val h
  simp [Fin.castSucc] at hv
  omega

private lemma phiForm_basis_of_ne_three (f : Module.Basis (Fin 4) (ZMod 3) U)
    {j : Fin 4} (hj : j ≠ 3) : phiForm f (f j) = 1 := by
  rw [phiForm_apply, Fin.sum_univ_four]
  fin_cases j <;> simp_all [Module.Basis.repr_self]

private lemma coord_three_eq_zero {f : Module.Basis (Fin 4) (ZMod 3) U}
    {h : U ≃ₗ[ZMod 3] U} (hh : IsIsom 3 (phiForm f) h) (hfix : h (f 3) = f 3)
    (i : Fin 3) : f.repr (h (f i.castSucc)) 3 = 0 := by
  have hp1 := phiForm_polar_basis f (h (f i.castSucc)) 3
  have hp2 := phiForm_polar_basis f (f i.castSucc) 3
  have hpres := polar_comp_of_isIsom hh (f i.castSucc) (f 3)
  rw [hfix] at hpres
  rw [hp1, hp2] at hpres
  have hzero : f.repr (f i.castSucc) 3 = 0 := by
    rw [Module.Basis.repr_self]
    exact Finsupp.single_eq_of_ne (castSucc_ne_three i).symm
  rw [hzero, mul_zero] at hpres
  have hcoef : (2 : ZMod 3) * (if (3 : Fin 4) = 3 then (-1 : ZMod 3) else 1) ≠ 0 := by
    decide +kernel
  exact (mul_eq_zero.mp hpres).resolve_left hcoef

private lemma norm_one {f : Module.Basis (Fin 4) (ZMod 3) U}
    {h : U ≃ₗ[ZMod 3] U} (hh : IsIsom 3 (phiForm f) h) (hfix : h (f 3) = f 3)
    (i : Fin 3) :
    (f.repr (h (f i.castSucc)) 0) ^ 2 + (f.repr (h (f i.castSucc)) 1) ^ 2 +
      (f.repr (h (f i.castSucc)) 2) ^ 2 = 1 := by
  have h3 : f.repr (h (f i.castSucc)) 3 = 0 := coord_three_eq_zero hh hfix i
  have hphi : phiForm f (h (f i.castSucc)) = phiForm f (f i.castSucc) := hh _
  have hf : phiForm f (f i.castSucc) = 1 := phiForm_basis_of_ne_three f (castSucc_ne_three i)
  rw [hf, phiForm_eq_oPhiQ, oPhiQ] at hphi
  rw [h3] at hphi
  simpa using hphi

private lemma sum_weighted_single_single (k k' : Fin 4) (a b : ZMod 3) :
    (∑ j : Fin 4, (if j = 3 then (-1 : ZMod 3) else 1) *
      (a * (if j = k then 1 else 0)) * (b * (if j = k' then 1 else 0))) =
    (if k = k' then (if k = 3 then (-1 : ZMod 3) else 1) * a * b else 0) := by
  fin_cases k <;> fin_cases k' <;> simp

private lemma injective_of_repr_single {f : Module.Basis (Fin 4) (ZMod 3) U}
    {h : U ≃ₗ[ZMod 3] U} (hh : IsIsom 3 (phiForm f) h)
    {k : Fin 3 → Fin 4} {s : Fin 3 → Bool} (hk3 : ∀ i, k i ≠ 3)
    (hrepr : ∀ i, (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) =
      (if s i then (-1 : ZMod 3) else 1) • Pi.single (k i) 1) :
    Function.Injective k := by
  intro i i' hkk
  by_contra hii
  have hpol := polar_comp_of_isIsom hh (f i.castSucc) (f i'.castSucc)
  have hR : QuadraticMap.polar (phiForm f) (f i.castSucc) (f i'.castSucc) = 0 := by
    rw [phiForm_polar_basis]
    have hz : f.repr (f i.castSucc) i'.castSucc = 0 := by
      rw [Module.Basis.repr_self]
      exact Finsupp.single_eq_of_ne (fun h => hii (Fin.ext
        (by simpa [Fin.castSucc] using congrArg Fin.val h)).symm)
    rw [hz, mul_zero]
  have hL : QuadraticMap.polar (phiForm f) (h (f i.castSucc)) (h (f i'.castSucc)) =
      2 * (if s i then (-1 : ZMod 3) else 1) *
        (if s i' then (-1 : ZMod 3) else 1) := by
    rw [phiForm_polarBilin_apply, hrepr i, hrepr i']
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [sum_weighted_single_single, if_pos hkk]
    simp only [if_neg (hk3 i), one_mul]
    ring
  rw [hL, hR] at hpol
  have ha : (if s i then (-1 : ZMod 3) else 1) ≠ 0 := by split <;> decide +kernel
  have hb : (if s i' then (-1 : ZMod 3) else 1) ≠ 0 := by split <;> decide +kernel
  exact (mul_ne_zero (mul_ne_zero (by decide +kernel : (2 : ZMod 3) ≠ 0) ha) hb) hpol

private lemma toMatrix_eq_oPhiColsMat {f : Module.Basis (Fin 4) (ZMod 3) U}
    {h : U ≃ₗ[ZMod 3] U} (hfix : h (f 3) = f 3)
    {k : Fin 3 → Fin 4} {s : Fin 3 → Bool}
    (hrepr : ∀ i, (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) =
      (if s i then (-1 : ZMod 3) else 1) • Pi.single (k i) 1) :
    LinearMap.toMatrix f f h.toLinearMap = oPhiColsMat k s := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  refine Fin.lastCases ?_ ?_ j
  · change (f.repr (h (f (Fin.last 3))) : Fin 4 → ZMod 3) i = oPhiColsMat k s i (Fin.last 3)
    rw [show h (f (Fin.last 3)) = f 3 from hfix, Module.Basis.repr_self]
    simp only [oPhiColsMat, Fin.lastCases_last, Pi.single_apply]
    by_cases hi : i = 3
    · subst hi; simp
    · rw [Finsupp.single_eq_of_ne hi, if_neg hi]
  · intro j'
    change (f.repr (h (f j'.castSucc)) : Fin 4 → ZMod 3) i = oPhiColsMat k s i j'.castSucc
    rw [hrepr j']
    simp [oPhiColsMat, Pi.single_apply, smul_eq_mul]

private lemma toMatrix_mem_oPhiSignedPerms_of_fix {f : Module.Basis (Fin 4) (ZMod 3) U}
    {h : U ≃ₗ[ZMod 3] U} (hh : IsIsom 3 (phiForm f) h) (hfix : h (f 3) = f 3) :
    LinearMap.toMatrix f f h.toLinearMap ∈ oPhiSignedPerms := by
  classical
  have hex : ∀ i : Fin 3, ∃ k : Fin 4,
      (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) = Pi.single k 1 ∨
        (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) = -Pi.single k 1 :=
    fun i => oPhiNormOneVectors _ (coord_three_eq_zero hh hfix i) (norm_one hh hfix i)
  let k : Fin 3 → Fin 4 := fun i => Classical.choose (hex i)
  have hk : ∀ i : Fin 3,
      (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) = Pi.single (k i) 1 ∨
      (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) = -Pi.single (k i) 1 :=
    fun i => Classical.choose_spec (hex i)
  have hk3 : ∀ i, k i ≠ 3 := by
    intro i h3
    have h0 := coord_three_eq_zero hh hfix i
    rcases hk i with h | h <;> rw [h] at h0 <;> simp [h3] at h0
  let s : Fin 3 → Bool := fun i =>
    decide ((f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) = -Pi.single (k i) 1)
  have hrepr : ∀ i, (f.repr (h (f i.castSucc)) : Fin 4 → ZMod 3) =
      (if s i then (-1 : ZMod 3) else 1) • Pi.single (k i) 1 := by
    intro i
    rcases hk i with h | h
    · have hs : s i = false := by
        apply decide_eq_false
        intro hneg
        rw [h] at hneg
        have := congrFun hneg (k i)
        simp only [Pi.single_eq_same, Pi.neg_apply] at this
        exact (by decide +kernel : (1 : ZMod 3) ≠ -1) this
      rw [hs, h]
      simp
    · have hs : s i = true := by exact decide_eq_true h
      rw [hs, h]
      simp
  have hkinj : Function.Injective k := injective_of_repr_single hh hk3 hrepr
  have hmat : LinearMap.toMatrix f f h.toLinearMap = oPhiColsMat k s :=
    toMatrix_eq_oPhiColsMat hfix hrepr
  rw [hmat]
  exact oPhiColsMat_mem_signedPerms k hk3 hkinj s

private lemma oPhiStabLevels_mem_basisClosure (f : Module.Basis (Fin 4) (ZMod 3) U) (n : ℕ)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hM : M ∈ oPhiStabLevels n) :
    ∃ w ∈ basisClosure f (oPhiOneMats : Set (Matrix (Fin 4) (Fin 4) (ZMod 3))),
      LinearMap.toMatrix f f w.toLinearMap = M := by
  induction n generalizing M with
  | zero =>
    simp only [oPhiStabLevels, Finset.mem_singleton] at hM
    subst hM
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ n ih =>
    simp only [oPhiStabLevels, oPhiStabStep, Finset.mem_union, Finset.mem_biUnion,
      List.mem_toFinset, List.mem_map] at hM
    rcases hM with hM | hM | hM
    · exact ih M hM
    · exact ih M hM
    · obtain ⟨M0, hM0, N, hN, hMN⟩ := hM
      obtain ⟨w0, hw0, hw0M⟩ := ih M0 hM0
      have hNmem : N ∈ (oPhiOneMats : Set (Matrix (Fin 4) (Fin 4) (ZMod 3))) := by
        have hN' := hN
        simp only [oPhiStabGens, List.mem_cons, List.not_mem_nil, or_false] at hN'
        rcases hN' with rfl | rfl | rfl <;> simp [oPhiOneMats]
      have hNdet : IsUnit N.det := by
        have hN' := hN
        simp only [oPhiStabGens, List.mem_cons, List.not_mem_nil, or_false] at hN'
        rcases hN' with rfl | rfl | rfl
        · exact Matrix.isUnit_det_of_right_inverse (diagSignMat_mul_self 0)
        · exact Matrix.isUnit_det_of_right_inverse
            (pijMat_mul_self (by decide +kernel : (0 : Fin 4) ≠ 1)
              (by norm_num : (1 : ZMod 3) ≠ 0))
        · exact Matrix.isUnit_det_of_right_inverse
            (pijMat_mul_self (by decide +kernel : (1 : Fin 4) ≠ 2)
              (by norm_num : (1 : ZMod 3) ≠ 0))
      obtain ⟨gN, hgN, hgNM⟩ := exists_mem_basisClosure_toMatrix_eq f hNmem hNdet
      refine ⟨w0 * gN, Subgroup.mul_mem _ hw0 hgN, ?_⟩
      rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hw0M, hgNM, hMN]

private lemma mem_oPhiOne_of_isIsom (f : Module.Basis (Fin 4) (ZMod 3) U)
    {g : U ≃ₗ[ZMod 3] U} (hg : IsIsom 3 (phiForm f) g) :
    g ∈ basisClosure f (oPhiOneMats : Set (Matrix (Fin 4) (Fin 4) (ZMod 3))) := by
  have hf3 : phiForm f (f 3) = -1 := phiForm_apply_f3 f
  have hg3 : phiForm f (g (f 3)) = -1 := by rw [hg, hf3]
  have hQ : oPhiQ ((f.repr (g (f 3)) : Fin 4 → ZMod 3)) = -1 := by
    rw [← phiForm_eq_oPhiQ]; exact hg3
  have hmem : (f.repr (g (f 3)) : Fin 4 → ZMod 3) ∈ oPhiOrbitLevels 10 := by
    rw [oPhiOrbitLevels_ten]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩
  obtain ⟨w, hw, hwv⟩ := oPhiOrbitLevels_mem_basisClosure f 10 _ hmem
  have hcol : (LinearMap.toMatrix f f w.toLinearMap).mulVec (Pi.single 3 1) =
      (f.repr (w (f 3)) : Fin 4 → ZMod 3) := by
    rw [show (Pi.single 3 1 : Fin 4 → ZMod 3) = (f.repr (f 3) : Fin 4 → ZMod 3) by
      funext j
      by_cases hj : j = 3
      · subst hj; simp [Module.Basis.repr_self]
      · simp [Module.Basis.repr_self, hj]]
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  have hgw : g (f 3) = w (f 3) := by
    apply f.repr.injective
    exact Finsupp.ext (fun i => congrFun (hwv.trans hcol) i)
  let hh : U ≃ₗ[ZMod 3] U := w⁻¹ * g
  have hw_isom : IsIsom 3 (phiForm f) w := isIsom_phiForm_of_mem_oPhiOne rfl f hw
  have hh_isom : IsIsom 3 (phiForm f) hh := by
    intro v
    have hwinv : IsIsom 3 (phiForm f) w⁻¹ := by
      intro u
      have h := hw_isom ((w⁻¹) u)
      simpa using h.symm
    dsimp [hh]
    change phiForm f (w⁻¹ (g v)) = phiForm f v
    rw [hwinv, hg]
  have hh_fix : hh (f 3) = f 3 := by
    dsimp [hh]
    change w⁻¹ (g (f 3)) = f 3
    rw [hgw]
    simp
  have hmat : LinearMap.toMatrix f f hh.toLinearMap ∈ oPhiSignedPerms :=
    toMatrix_mem_oPhiSignedPerms_of_fix hh_isom hh_fix
  have hstab : LinearMap.toMatrix f f hh.toLinearMap ∈ oPhiStabLevels 10 :=
    oPhiSignedPerms_subset hmat
  obtain ⟨h', hh'mem, hh'mat⟩ := oPhiStabLevels_mem_basisClosure f 10 _ hstab
  have hh_eq : hh = h' := (eq_of_toMatrix_eq f hh'mat).symm
  have hwh : w * hh = g := by
    dsimp [hh]
    group
  rw [← hwh, hh_eq]
  exact Subgroup.mul_mem _ hw hh'mem

end MemOPhiOne

theorem mem_oPhiOne_iff (hp : p = 3) (f : Module.Basis (Fin 4) (ZMod p) U)
    (g : U ≃ₗ[ZMod p] U) : g ∈ basisClosure f oPhiOneMats ↔ IsIsom p (phiForm f) g := by
  subst hp
  exact ⟨fun hg => isIsom_phiForm_of_mem_oPhiOne rfl f hg,
    fun hg => mem_oPhiOne_of_isIsom f hg⟩

section ToMatrixOfCommute

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U]

private lemma toMatrix_unitsSMul_entry {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {n : ℕ} (f : Module.Basis (Fin n) K V) (w : Fin n → Kˣ) (g : V ≃ₗ[K] V) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g.toLinearMap =
      fun i j => ((w i)⁻¹ : K) * (w j : K) * LinearMap.toMatrix f f g.toLinearMap i j := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.unitsSMul_apply,
    Module.Basis.repr_unitsSMul, Units.smul_def, map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_assoc, Units.val_inv_eq_inv_val]
  ring

private lemma entry_eq {n : ℕ} (w : Fin n → (ZMod 3)ˣ) (u κ : Fin n → ZMod 3) :
    (fun i j => ((w i)⁻¹ : ZMod 3) * (w j : ZMod 3) *
      (((1 : Matrix (Fin n) (Fin n) (ZMod 3)) - Matrix.vecMulVec u κ) i j)) =
      ((1 : Matrix (Fin n) (Fin n) (ZMod 3)) -
        Matrix.vecMulVec (fun i => ((w i)⁻¹ : ZMod 3) * u i)
          (fun j => (w j : ZMod 3) * κ j)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, if_true]
    have h : ((w i : ZMod 3))⁻¹ * u i * ((w i : ZMod 3) * κ i) = u i * κ i := by
      rw [show ((w i : ZMod 3))⁻¹ * u i * ((w i : ZMod 3) * κ i) =
          (((w i : ZMod 3))⁻¹ * (w i : ZMod 3)) * (u i * κ i) by ring,
        inv_mul_cancel₀ (Units.ne_zero (w i)), one_mul]
    rw [inv_mul_cancel₀ (Units.ne_zero (w i)), one_mul, h]
  · simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, if_neg hij]
    ring

private lemma oPhiMat_eq_scaled (c : ZMod 3) (hc : c ≠ 0) :
    (1 - Matrix.vecMulVec (c • (![0, 1, 1, 1] : Fin 4 → ZMod 3))
      (c⁻¹ • (![0, -1, -1, 1] : Fin 4 → ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      oPhiMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oPhiMat, Matrix.sub_apply, smul_eq_mul] <;>
    field_simp <;> decide +kernel

private lemma oPhi_relations3 (f : Module.Basis (Fin 4) (ZMod 3) U)
    {a b c y : U ≃ₗ[ZMod 3] U}
    (ha : LinearMap.toMatrix f f a.toLinearMap = diagSignMat 0)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 0 1 1)
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 1 2 1)
    (hy : IsRefl 3 y) (hya : y * a = a * y) (hyc : y * c = c * y)
    (hyb : orderOf (y * b) = 4)
    (hV : ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod 3) (Set.range fun i : Fin 3 => f i.castSucc)) :
    ∃ u κ : Fin 4 → ZMod 3, u 3 ≠ 0 ∧
      LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec u κ ∧
      (∑ i, κ i * u i = 2) ∧ u 0 = 0 ∧ u 1 = u 2 ∧ κ 0 = 0 ∧ κ 1 = κ 2 ∧
      κ 1 * u 1 = 2 ∧ κ 3 * u 3 = 1 := by
  obtain ⟨u, κ, hy_mat, hκu⟩ := FFourCoord.exists_toMatrix_of_isRefl (p := 3)
    (by norm_num) f hy
  have hu3 : u 3 ≠ 0 := fun h3 => hV (FFourCoord.movedSpace_le_span_of_toMatrix f hy_mat h3)
  have hA : LinearMap.toMatrix f f a.toLinearMap =
      (1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod 3)
        (![2, 0, 0, 0] : Fin 4 → ZMod 3)) := by
    rw [ha, FFourCoord.diagSignMat_zero_eq]
  have hB : LinearMap.toMatrix f f b.toLinearMap =
      (1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod 3)
        (![1, -1, 0, 0] : Fin 4 → ZMod 3)) := by
    rw [hb, FFourCoord.pijMat_zero_one_eq]
  have hC : LinearMap.toMatrix f f c.toLinearMap =
      (1 - Matrix.vecMulVec (![0, 1, -1, 0] : Fin 4 → ZMod 3)
        (![0, 1, -1, 0] : Fin 4 → ZMod 3)) := by
    rw [hc, FFourCoord.pijMat_one_two_eq]
  have hneA : y ≠ a := by
    intro h; apply hV; rw [h]
    exact FFourCoord.movedSpace_le_span_of_toMatrix f hA (by decide +kernel)
  have hneC : y ≠ c := by
    intro h; apply hV; rw [h]
    exact FFourCoord.movedSpace_le_span_of_toMatrix f hC (by decide +kernel)
  obtain ⟨hκ0raw, h2u0raw⟩ := FFourCoord.eq_zero_of_commute_of_toMatrix (p := 3)
    (by norm_num) f (x := y) (r := a) (v := u) (w := κ) (ρ := ![1, 0, 0, 0])
    (κ := ![2, 0, 0, 0]) hy_mat hκu hA (by decide +kernel) hya hneA
  obtain ⟨hκc_raw, huc_raw⟩ := FFourCoord.eq_zero_of_commute_of_toMatrix (p := 3)
    (by norm_num) f (x := y) (r := c) (v := u) (w := κ) (ρ := ![0, 1, -1, 0])
    (κ := ![0, 1, -1, 0]) hy_mat hκu hC (by decide +kernel) hyc hneC
  have hbond_raw := FFourCoord.mul_eq_two_of_orderOf_eq_four (p := 3) (by norm_num) f
    (x := y) (r := b) (v := u) (w := κ) (ρ := ![1, -1, 0, 0]) (κ := ![1, -1, 0, 0])
    hy_mat hκu hB (by decide +kernel) hyb
  have hu0 : u 0 = 0 := by
    have h : (2 : ZMod 3) * u 0 = 0 := by simpa [Fin.sum_univ_four] using h2u0raw
    exact (mul_eq_zero.mp h).resolve_left (by decide +kernel)
  have hκ0 : κ 0 = 0 := by simpa [Fin.sum_univ_four] using hκ0raw
  have hu12 : u 1 = u 2 := by
    have h : u 1 + -u 2 = 0 := by simpa [Fin.sum_univ_four] using huc_raw
    rw [add_eq_zero_iff_eq_neg, neg_neg] at h
    exact h
  have hκ12 : κ 1 = κ 2 := by
    have h : κ 1 + -κ 2 = 0 := by simpa [Fin.sum_univ_four] using hκc_raw
    rw [add_eq_zero_iff_eq_neg, neg_neg] at h
    exact h
  have hκ1u1 : κ 1 * u 1 = 2 := by
    have h : (κ 0 + -κ 1) * (u 0 + -u 1) = 2 := by
      simpa [Fin.sum_univ_four] using hbond_raw
    simp only [hκ0, hu0, zero_add, neg_mul_neg] at h
    exact h
  have hκ3u3 : κ 3 * u 3 = 1 := by
    have hsum : κ 0 * u 0 + κ 1 * u 1 + κ 2 * u 2 + κ 3 * u 3 = 2 := by
      simpa [Fin.sum_univ_four] using hκu
    rw [hu0, hκ0, zero_mul, zero_add] at hsum
    rw [← hu12, ← hκ12, hκ1u1] at hsum
    rw [show (2 : ZMod 3) + 2 = 1 by decide +kernel] at hsum
    have h1 : κ 3 * u 3 + (1 : ZMod 3) = 2 := by rw [add_comm]; exact hsum
    have h2 := eq_sub_of_add_eq h1
    rwa [show (2 : ZMod 3) - 1 = 1 by decide +kernel] at h2
  exact ⟨u, κ, hu3, hy_mat, hκu, hu0, hu12, hκ0, hκ12, hκ1u1, hκ3u3⟩

private lemma oPhi_exists_eps (f : Module.Basis (Fin 4) (ZMod 3) U)
    {a b c y : U ≃ₗ[ZMod 3] U} (ha : LinearMap.toMatrix f f a.toLinearMap = diagSignMat 0)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 0 1 1)
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 1 2 1) (hy : IsRefl 3 y)
    (hya : y * a = a * y) (hyc : y * c = c * y) (hyb : orderOf (y * b) = 4)
    (hV : ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod 3) (Set.range fun i : Fin 3 => f i.castSucc)) :
    ∃ ε : (ZMod 3)ˣ, LinearMap.toMatrix (f.unitsSMul ![1, 1, 1, ε])
      (f.unitsSMul ![1, 1, 1, ε]) y.toLinearMap = oPhiMat := by
  obtain ⟨u, κ, hu3, hy_mat, _hκu, hu0, hu12, hκ0, hκ12, hκ1u1, hκ3u3⟩ :=
    oPhi_relations3 f ha hb hc hy hya hyc hyb hV
  have hu1 : u 1 ≠ 0 := by
    intro h
    have h2 := hκ1u1
    rw [h, mul_zero] at h2
    exact (by decide +kernel : (2 : ZMod 3) ≠ 0) h2.symm
  have hε_ne : u 3 / u 1 ≠ 0 := div_ne_zero hu3 hu1
  let ε : (ZMod 3)ˣ := Units.mk0 (u 3 / u 1) hε_ne
  refine ⟨ε, ?_⟩
  have hεval : (ε : ZMod 3) = u 3 / u 1 := Units.val_mk0 hε_ne
  have hεu1 : (ε : ZMod 3) * u 1 = u 3 := by rw [hεval, div_mul_cancel₀ _ hu1]
  have hεinvu3 : ((ε : ZMod 3))⁻¹ * u 3 = u 1 := by
    have h := congrArg (fun x => ((ε : ZMod 3))⁻¹ * x) hεu1
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero ε), one_mul] at h
    exact h.symm
  have hκ1 : κ 1 = -(u 1)⁻¹ := by
    have h : κ 1 * u 1 = -1 := by rw [hκ1u1]; decide +kernel
    calc κ 1 = (κ 1 * u 1) * (u 1)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu1, mul_one]
      _ = (-1) * (u 1)⁻¹ := by rw [h]
      _ = -(u 1)⁻¹ := by ring
  have hεκ3 : (ε : ZMod 3) * κ 3 = (u 1)⁻¹ := by
    rw [hεval, div_mul_eq_mul_div, mul_comm (u 3) (κ 3), hκ3u3, one_div]
  let w : Fin 4 → (ZMod 3)ˣ := ![1, 1, 1, ε]
  change LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) y.toLinearMap = oPhiMat
  rw [toMatrix_unitsSMul_entry f w y, hy_mat, entry_eq w u κ]
  have hu' : (fun i => ((w i)⁻¹ : ZMod 3) * u i) =
      u 1 • (![0, 1, 1, 1] : Fin 4 → ZMod 3) := by
    funext i
    fin_cases i
    · change ((1 : (ZMod 3)ˣ) : ZMod 3)⁻¹ * u 0 = u 1 * 0
      rw [hu0]; ring
    · change ((1 : (ZMod 3)ˣ) : ZMod 3)⁻¹ * u 1 = u 1 * 1
      simp
    · change ((1 : (ZMod 3)ˣ) : ZMod 3)⁻¹ * u 2 = u 1 * 1
      rw [← hu12]; simp
    · change ((ε : ZMod 3))⁻¹ * u 3 = u 1 * 1
      rw [hεinvu3]; ring
  have hκ' : (fun j => (w j : ZMod 3) * κ j) =
      (u 1)⁻¹ • (![0, -1, -1, 1] : Fin 4 → ZMod 3) := by
    funext j
    fin_cases j
    · change ((1 : (ZMod 3)ˣ) : ZMod 3) * κ 0 = (u 1)⁻¹ * 0
      rw [hκ0]; ring
    · change ((1 : (ZMod 3)ˣ) : ZMod 3) * κ 1 = (u 1)⁻¹ * (-1)
      rw [hκ1]; simp
    · change ((1 : (ZMod 3)ˣ) : ZMod 3) * κ 2 = (u 1)⁻¹ * (-1)
      rw [← hκ12, hκ1]; simp
    · change (ε : ZMod 3) * κ 3 = (u 1)⁻¹ * 1
      rw [hεκ3]; ring
  rw [hu', hκ', oPhiMat_eq_scaled (u 1) hu1]
end ToMatrixOfCommute

theorem toMatrix_oPhiMat_of_commute (hp : p = 3) (f : Module.Basis (Fin 4) (ZMod p) U)
    {a b c y : U ≃ₗ[ZMod p] U} (ha : LinearMap.toMatrix f f a.toLinearMap = diagSignMat 0)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 0 1 1)
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 1 2 1) (hy : IsRefl p y)
    (hya : y * a = a * y) (hyc : y * c = c * y) (hyb : orderOf (y * b) = 4)
    (hV : ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)) :
    ∃ ε : (ZMod p)ˣ, LinearMap.toMatrix (f.unitsSMul ![1, 1, 1, ε]) (f.unitsSMul ![1, 1, 1, ε])
      y.toLinearMap = oPhiMat := by
  subst hp
  exact oPhi_exists_eps f ha hb hc hy hya hyc hyb hV

private lemma movedSpace_conj_eq (g x : U ≃ₗ[ZMod p] U) :
    HardMathSupport.Kantor79.movedSpace (g * x * g⁻¹) =
      (HardMathSupport.Kantor79.movedSpace x).map (g : U →ₗ[ZMod p] U) := by
  unfold HardMathSupport.Kantor79.movedSpace
  ext y
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨((x : U →ₗ[ZMod p] U) - 1) (g⁻¹ z), ⟨g⁻¹ z, rfl⟩, ?_⟩
    rw [← hz]
    simp
  · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
    refine ⟨g z, ?_⟩
    simp

private lemma movedSpace_reflection_eq_span (hp : p ≠ 2) {a : U}
    {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2) :
    HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) =
      Submodule.span (ZMod p) {a} := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    change Module.reflection hφ v - v ∈ Submodule.span (ZMod p) {a}
    rw [Module.reflection_apply]
    rw [show v - φ v • a - v = -(φ v • a) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ v)
      (Submodule.subset_span (Set.mem_singleton a)))
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨-((2 : ZMod p)⁻¹) • a, ?_⟩
    change Module.reflection hφ (-((2 : ZMod p)⁻¹) • a) - (-((2 : ZMod p)⁻¹) • a) = a
    rw [Module.reflection_apply]
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have hφa : φ (-((2 : ZMod p)⁻¹) • a) = -1 := by
      rw [map_smul, hφ, smul_eq_mul, neg_mul, inv_mul_cancel₀ h2]
    rw [hφa]
    simp

private lemma isIsom_mul_of_le {f : Module.Basis (Fin 4) (ZMod p) U}
    {g h : U ≃ₗ[ZMod p] U} (hg : IsIsom p (phiForm f) g) (hh : IsIsom p (phiForm f) h) :
    IsIsom p (phiForm f) (g * h) := by
  intro v
  rw [LinearEquiv.mul_apply, hg, hh]

private lemma isIsom_inv_of_le {f : Module.Basis (Fin 4) (ZMod p) U}
    {g : U ≃ₗ[ZMod p] U} (hg : IsIsom p (phiForm f) g) : IsIsom p (phiForm f) g⁻¹ := by
  intro v
  have h : (phiForm f) (g ((g⁻¹) v)) = (phiForm f) ((g⁻¹) v) := hg ((g⁻¹) v)
  simpa using h.symm

theorem isIsom_iff_of_le (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : ReflGen p G)
    (hO : ∀ g, IsIsom p (phiForm f) g → g ∈ G) (hH : ∀ h ∈ H, IsIsom p (phiForm f) h)
    (hinH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H)
    (g : U ≃ₗ[ZMod p] U) : g ∈ G ↔ IsIsom p (phiForm f) g := by
  refine ⟨?_, hO g⟩
  intro hg
  have hG' : G = Subgroup.closure {t | t ∈ G ∧ IsRefl p t} := hG
  rw [hG'] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxG, hxRefl⟩ := hx
    have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
    obtain ⟨a, φ, hφ, rfl⟩ := (isRefl_iff hp x).mp hxRefl
    have hspan := movedSpace_reflection_eq_span hp hφ
    obtain ⟨h, hh, haW⟩ := exists_isIsom_apply_mem_span hp f a
    have hhG : h ∈ G := hO h hh
    have hx'G : h * Module.reflection hφ * h⁻¹ ∈ G :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhG hxG) (Subgroup.inv_mem _ hhG)
    have hx'refl : IsRefl p (h * Module.reflection hφ * h⁻¹) :=
      IsRefl.conj (isRefl_reflection hp hφ) h
    have hle : HardMathSupport.Kantor79.movedSpace (h * Module.reflection hφ * h⁻¹) ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
      rw [movedSpace_conj_eq, hspan, Submodule.map_span, Set.image_singleton]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr haW)
    have hx'H : h * Module.reflection hφ * h⁻¹ ∈ H := hinH _ hx'G hx'refl hle
    have hisom' : IsIsom p (phiForm f) (h * Module.reflection hφ * h⁻¹) := hH _ hx'H
    have hxeq : Module.reflection hφ = h⁻¹ * (h * Module.reflection hφ * h⁻¹) * h := by group
    rw [hxeq]
    exact isIsom_mul_of_le (isIsom_mul_of_le (isIsom_inv_of_le hh) hisom') hh
  | one => intro v; simp
  | mul x y hx hy ihx ihy =>
    intro v
    calc (phiForm f) ((x * y) v) = (phiForm f) (x (y v)) := by rw [LinearEquiv.mul_apply]
    _ = (phiForm f) (y v) := ihx (y v)
    _ = (phiForm f) v := ihy v
  | inv x hx ih =>
    intro v
    have h : (phiForm f) (x ((x⁻¹) v)) = (phiForm f) ((x⁻¹) v) := ih ((x⁻¹) v)
    have h_inv : x ((x⁻¹) v) = v := by simp
    rw [h_inv] at h
    exact h.symm

end CFSG.StandardType.ZS

end
