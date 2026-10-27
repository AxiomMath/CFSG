module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelCoords

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinModel

variable {m : ℕ} {F : Type} [Field F]

theorem mulVec_apply_of_isPermOf {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {π : Equiv.Perm (Fin (m + 1))} (hA : IsPermOf A π) (v : Fin (m + 1) → F)
    (i : Fin (m + 1)) : (A *ᵥ v) (π i) = A (π i) i * v i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · intro k _ hk
    have h0 : A (π i) k = 0 := by
      by_contra h
      exact hk (π.injective ((hA k (π i)).mp h)).symm
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eq_zero_of_mulVec_eq_smul {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {π : Equiv.Perm (Fin (m + 1))} (hA : IsPermOf A π) (hcyc : π.IsCycle)
    (hsupp : π.support = Finset.univ) {c : F} (hc : c ≠ 0) {v : Fin (m + 1) → F}
    (hv : A *ᵥ v = c • v) {i₀ : Fin (m + 1)} (h0 : v i₀ = 0) : v = 0 := by
  have hstep : ∀ i, v i = 0 → v (π i) = 0 := by
    intro i hi
    have h1 := mulVec_apply_of_isPermOf hA v i
    rw [hv, Pi.smul_apply, smul_eq_mul, hi, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  have hpow : ∀ k : ℕ, v ((π ^ k) i₀) = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hstep _ ih
  funext l
  have hi₀ : π i₀ ≠ i₀ := Equiv.Perm.mem_support.mp (by rw [hsupp]; exact Finset.mem_univ _)
  have hl : π l ≠ l := Equiv.Perm.mem_support.mp (by rw [hsupp]; exact Finset.mem_univ _)
  obtain ⟨k, hk⟩ := hcyc.exists_pow_eq hi₀ hl
  rw [Pi.zero_apply, ← hk]
  exact hpow k

theorem diagonal_mulVec_single (e : Fin (m + 1) → F) (l : Fin (m + 1)) :
    diagonal e *ᵥ Pi.single l 1 = e l • Pi.single l 1 := by
  ext i
  by_cases h : i = l
  · subst h
    simp [Matrix.mulVec_diagonal]
  · simp [Matrix.mulVec_diagonal, h]

theorem injective_of_mul_eq_mul_diagonal {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {π : Equiv.Perm (Fin (m + 1))} (hA : IsPermOf A π) (hcyc : π.IsCycle)
    (hsupp : π.support = Finset.univ) (B : GL (Fin (m + 1)) F) {e : Fin (m + 1) → F}
    (he : ∀ i, e i ≠ 0)
    (hAB : A * (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * diagonal e) : Function.Injective e := by
  intro j k hjk
  by_contra hne
  set Bm := (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hBm
  have hBinj : ∀ x : Fin (m + 1) → F, Bm *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h1 := congrArg (fun y => ((B⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ y) hx
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h1
  have heig : ∀ l, A *ᵥ (Bm *ᵥ Pi.single l 1) = e l • (Bm *ᵥ Pi.single l 1) := by
    intro l
    rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, diagonal_mulVec_single,
      Matrix.mulVec_smul]
  set v := Bm *ᵥ Pi.single j 1 with hv
  set w := Bm *ᵥ Pi.single k 1 with hw
  have hvz : v ≠ 0 := by
    intro h
    have := congrFun (hBinj _ h) j
    simp at this
  set u := w 0 • v - v 0 • w with hu
  have hueig : A *ᵥ u = e j • u := by
    rw [hu, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, heig j, heig k, ← hjk,
      smul_sub, smul_comm (e j) (w 0), smul_comm (e j) (v 0)]
  have hu0 : u 0 = 0 := by
    rw [hu, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm,
      sub_self]
  have huz := eq_zero_of_mulVec_eq_smul hA hcyc hsupp (he j) hueig hu0
  have hcomb : Bm *ᵥ (w 0 • Pi.single j 1 - v 0 • Pi.single k 1) = u := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [huz] at hcomb
  have hx := hBinj _ hcomb
  have hxk := congrFun hx k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hne, smul_eq_mul,
    mul_zero, mul_one, zero_sub, Pi.zero_apply, neg_eq_zero] at hxk
  exact hvz (eq_zero_of_mulVec_eq_smul hA hcyc hsupp (he j) (heig j) hxk)

section Conj

variable {G : Type*} [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem coe_map_diagGL (σ : F ≃+* F) (d : Fin (m + 1) → Fˣ) :
    ((GeneralLinearGroup.map (σ : F →+* F) (InnerDiagA.diagGL d) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal fun i => σ ((d i : Fˣ) : F) := by
  ext a c
  rw [GeneralLinearGroup.map_apply, diagGL_apply, diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · exact map_zero _

theorem coe_map_inverseTranspose_diagGL (σ : F ≃+* F) (d : Fin (m + 1) → Fˣ) :
    ((GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose (InnerDiagA.diagGL d)) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal fun i => σ (((d i)⁻¹ : Fˣ) : F) := by
  ext a c
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_inverseTranspose, transpose_apply,
    InnerDiagA.coe_diagGL_inv, diagonal_apply, diagonal_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem exists_conj_mul_diag [Finite F] (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {g : G}
    (hg : g ∈ Subgroup.normalizer (ψ.range : Set G)) {w : G} {d : Fin (m + 1) → Fˣ}
    (hw : (w, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ (B X : GL (Fin (m + 1)) F) (e : Fin (m + 1) → F),
      (g * w * g⁻¹, B * X * B⁻¹) ∈ LinFusion.ggInducedPairs ψ ∧
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal e ∧ (∀ i, e i ≠ 0) ∧
      ∀ i j, d i = d j → e i = e j := by
  have hwN := mem_normalizer_of_mem_ggInducedPairs hw
  have hgwN : g * w * g⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hwN) (Subgroup.inv_mem _ hg)
  have h1 : autOf hker hC ⟨g * w * g⁻¹, hgwN⟩ =
      autOf hker hC ⟨g, hg⟩ * autOf hker hC ⟨w, hwN⟩ * (autOf hker hC ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [(autOf_eq_conjAut_iff hker hC hwN _).mpr hw] at h1
  obtain ⟨B, σ, ε, hε, hα⟩ :=
    (automorphism_generation (K := F) (n := m + 1) (by omega)).2 (autOf hker hC ⟨g, hg⟩)
  have htrans := standard_automorphism_transport (K := F) (n := m + 1)
  rw [hα] at h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · refine ⟨B, GeneralLinearGroup.map (σ : F →+* F) (InnerDiagA.diagGL d),
      fun i => σ ((d i : Fˣ) : F), ?_, coe_map_diagGL σ d,
      fun i => (map_ne_zero σ).mpr (Units.ne_zero _), fun i j h => by dsimp only; rw [h]⟩
    apply (autOf_eq_conjAut_iff hker hC hgwN _).mp
    rw [h1, pow_zero, mul_one, map_mul, map_mul, map_inv, ← htrans.2.2.1]
    group
  · refine ⟨B, GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose (InnerDiagA.diagGL d)),
      fun i => σ (((d i)⁻¹ : Fˣ) : F), ?_, coe_map_inverseTranspose_diagGL σ d,
      fun i => (map_ne_zero σ).mpr (Units.ne_zero _), fun i j h => by dsimp only; rw [h]⟩
    apply (autOf_eq_conjAut_iff hker hC hgwN _).mp
    have hδinv : (dualAut (m + 1) F)⁻¹ = dualAut (m + 1) F :=
      inv_eq_of_mul_eq_one_right htrans.2.2.2.1
    have key : dualAut (m + 1) F * conjAut (m + 1) F (InnerDiagA.diagGL d) *
        (dualAut (m + 1) F)⁻¹ =
        conjAut (m + 1) F (GeneralLinearGroup.inverseTranspose (InnerDiagA.diagGL d)) := by
      rw [hδinv]
      exact htrans.2.2.2.2.1 _
    rw [h1, pow_one, map_mul, map_mul, map_inv, ← htrans.2.2.1, ← key]
    group

end Conj

end LinModel

theorem ggLinearRegularConjInput_holds : GGLinearRegularConjInput := by
  intro G _ _ m f ψ hm hker hC z A π hzA hπ hcyc hsupp g hg d hd
  obtain ⟨B, X, e, hBX, hXe, he0, hde⟩ := LinModel.exists_conj_mul_diag hm hker hC hg hd
  rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hBX
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hBX hzA
  have h1 : A * B = B * (GeneralLinearGroup.scalar (Fin (m + 1)) c * X) := by
    rw [hc, mul_assoc, inv_mul_cancel_right, ← mul_assoc, (TypeA.PGLTor.commute_scalar c B).eq,
      mul_assoc]
  have hAB : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
        diagonal fun i => (c : GaloisField 2 f) * e i := by
    have h2 := congrArg (fun Y : GL (Fin (m + 1)) (GaloisField 2 f) =>
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) h1
    simp only [Units.val_mul] at h2
    rw [h2, GeneralLinearGroup.coe_scalar, hXe, scalar_apply, diagonal_mul_diagonal]
  have hinj := LinModel.injective_of_mul_eq_mul_diagonal hπ hcyc hsupp B
    (fun i => mul_ne_zero c.ne_zero (he0 i)) hAB
  intro i j hij
  apply hinj
  simp only [hde i j hij]

end CFSG.StandardType
