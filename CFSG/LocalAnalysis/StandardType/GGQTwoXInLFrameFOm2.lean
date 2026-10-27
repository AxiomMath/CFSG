module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.StandardType.QTwoOmFrame

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.StandardType.QTwoFrameTorus
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup mem_sesqUnitaryGroup)
open Matrix

lemma four_le_of_diag {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {E : Subgroup ↥(orthDerived Q)} {x : ↥(orthDerived Q)}
    {L D J : Subgroup ↥(orthDerived Q)}
    (hC : GGQTwoFRCfg E x L D J) {n : ℕ} {M : Type} [Field M] [Finite M] [Algebra K M]
    (hM : Nat.card M = 4)
    {U : Type} [AddCommGroup U] [Module K U] {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hEdiag : ∀ e ∈ E, ∃ a : Fin n → M, (∀ i, a i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) :
    4 ≤ n := by
  let aOf : ↥E → Fin n → M := fun e => Classical.choose (hEdiag e e.2)
  have haOf : ∀ e : ↥E, (∀ i, aOf e i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => aOf e i * d i, w) :=
    fun e => Classical.choose_spec (hEdiag e e.2)
  let f : ↥E → Fin n → Mˣ := fun e i =>
    Units.mk0 (aOf e i) (by
      intro hzero
      have h := (haOf e).1 i
      rw [hzero] at h
      norm_num at h)
  have hf : Function.Injective f := by
    intro e e' hee'
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    have hval : ∀ i, aOf e i = aOf e' i := by
      intro i
      have h := congrFun hee' i
      have h' := congrArg (fun u : Mˣ => (u : M)) h
      simpa [f] using h'
    rw [(haOf e).2 d w, (haOf e').2 d w]
    congr 1
    refine Prod.ext ?_ rfl
    funext i
    show aOf e i * d i = aOf e' i * d i
    rw [hval i]
  exact frame_four_le_of_injective hM hf hC.2.1


lemma rho_mem_orthogonalGroup {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {Q : QuadraticForm K V} {n : ℕ} {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hnorm : ∀ d w, algebraMap K M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w))))
    {ρ₀ : ↥(heldGU n M τ hτ) →* ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))}
    (hρ₀ : ∀ (A : ↥(heldGU n M τ hτ)) d w,
      (((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
        LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (d, w)) =
        Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d, w))
    (A : ↥(heldGU n M τ hτ)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv K V
      ((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
        LinearMap.GeneralLinearGroup K V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  change Q ((((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
    LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (d, w))) = Q (Φ (d, w))
  apply (algebraMap K M).injective
  rw [hρ₀ A d w,
    hnorm (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d) w,
    hnorm d w, heldGU_herm_mulVec A d d]


lemma exists_heldSU_mul_diag {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (hτ2 : ∀ y, τ y = y ^ 2) (hn : 4 ≤ n) (A : ↥(heldGU n M τ hτ)) :
    ∃ (A₁ Dg : ↥(heldGU n M τ hτ)) (d : Fin n → Mˣ),
      A = A₁ * Dg ∧ (A₁ : GL (Fin n) M) ∈ heldSU n M τ hτ ∧
      ((Dg : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        Matrix.diagonal (fun i => (d i : M)) ∧
      ((Dg : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det =
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det := by
  let δ : M := ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det
  have hδτ : τ δ * δ = 1 := by
    have h := congrArg Matrix.det (mem_heldGU.mp A.2)
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    change (τ.toRingHom.mapMatrix
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)).det *
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det = 1 at h
    rw [← RingHom.map_det τ.toRingHom
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)] at h
    simpa [δ] using h
  have hδne : δ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hδτ
    exact zero_ne_one hδτ
  let i₀ : Fin n := ⟨0, by omega⟩
  let d : Fin n → Mˣ := fun i => if i = i₀ then Units.mk0 δ hδne else 1
  let Dg : ↥(heldGU n M τ hτ) :=
    ↑(frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 d)
  let A₁ : ↥(heldGU n M τ hτ) := A * Dg⁻¹
  have hDgmat : ((Dg : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun i => (d i : M)) := by
    dsimp only [Dg]
    rw [frameDiagEquiv_apply_val, frameDiagGL_val]
  have hDgunit : Matrix.GeneralLinearGroup.det (Dg : GL (Fin n) M) =
      Units.mk0 δ hδne := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hDgmat, Matrix.det_diagonal,
      Finset.prod_eq_single i₀]
    · simp [d]
    · intro b _ hb
      simp [d, hb]
    · simp
  have hDgdet : ((Dg : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det = δ := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply (Dg : GL (Fin n) M), hDgunit,
      Units.val_mk0]
  have hfactor : A = A₁ * Dg := by
    rw [show A₁ * Dg = A from by
      dsimp [A₁]
      rw [mul_assoc, inv_mul_cancel, mul_one]]
  have hA₁GU : (A₁ : GL (Fin n) M) ∈ heldGU n M τ hτ := A₁.2
  have hAunit : Matrix.GeneralLinearGroup.det (A : GL (Fin n) M) =
      Units.mk0 δ hδne := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mk0]
  have hA₁unitdet : Matrix.GeneralLinearGroup.det (A₁ : GL (Fin n) M) = 1 := by
    have hA₁eq : (A₁ : GL (Fin n) M) = (A : GL (Fin n) M) * (Dg : GL (Fin n) M)⁻¹ := by
      change (((A * Dg⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M)) = _
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hA₁eq, map_mul, map_inv, hAunit, hDgunit]
    simp
  have hA₁det : ((A₁ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply (A₁ : GL (Fin n) M), hA₁unitdet,
      Units.val_one]
  refine ⟨A₁, Dg, d, hfactor, ?_, hDgmat, hDgdet⟩
  exact Subgroup.mem_inf.mpr ⟨hA₁GU, CFSG.Open.StatedAPI.mem_statedSL_of_det hA₁det⟩


lemma rho_mem_orthDerived {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {Q : QuadraticForm K V} {n : ℕ} {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) (hn : 4 ≤ n)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    {ρ₀ : ↥(heldGU n M τ hτ) →* ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))}
    (hρ₀ : ∀ (A : ↥(heldGU n M τ hτ)) d w,
      (((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
        LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (d, w)) =
        Φ ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) *ᵥ d, w))
    (hOg : ∀ A : ↥(heldGU n M τ hτ),
      LinearMap.GeneralLinearGroup.generalLinearEquiv K V
        ((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
          LinearMap.GeneralLinearGroup K V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hSUperf : Group.IsPerfect ↥(heldSU n M τ hτ))
    {E : Subgroup ↥(orthDerived Q)}
    (hEtorus : ∀ a : Fin n → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ E,
      ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w))
    (A : ↥(heldGU n M τ hτ)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv K V
      ((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
        LinearMap.GeneralLinearGroup K V) ∈ orthDerived Q := by
  let φ : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q)) →* (V ≃ₗ[K] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp
      (Subgroup.subtype (sesqUnitaryGroup (QuadraticMap.polarBilin Q)))
  have hOg' : ∀ A : ↥(heldGU n M τ hτ), φ (ρ₀ A) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun A => hOg A
  let fSU : ↥(heldSU n M τ hτ) →* ↥(heldGU n M τ hτ) :=
    { toFun := fun x => ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨A₁, Dg, d, hfac, hA₁SU, hDgmat, _hDgdet⟩ :=
    exists_heldSU_mul_diag hM hτ2 hn A
  have hcommSU : ⁅(⊤ : Subgroup ↥(heldSU n M τ hτ)), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have hmapcomm : (⊤ : Subgroup ↥(heldSU n M τ hτ)).map ((φ.comp ρ₀).comp fSU) =
      ⁅(⊤ : Subgroup ↥(heldSU n M τ hτ)).map ((φ.comp ρ₀).comp fSU),
        (⊤ : Subgroup ↥(heldSU n M τ hτ)).map ((φ.comp ρ₀).comp fSU)⁆ := by
    rw [← Subgroup.map_commutator (⊤ : Subgroup ↥(heldSU n M τ hτ))
      (⊤ : Subgroup ↥(heldSU n M τ hτ)) ((φ.comp ρ₀).comp fSU), hcommSU]
  have hSUmapO : (⊤ : Subgroup ↥(heldSU n M τ hτ)).map ((φ.comp ρ₀).comp fSU) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro x hx
    obtain ⟨B, _hB, rfl⟩ := Subgroup.mem_map.mp hx
    exact hOg' (fSU B)
  have hmemA₁ : φ (ρ₀ A₁) ∈ orthDerived Q := by
    have hmem : φ (ρ₀ A₁) ∈
        (⊤ : Subgroup ↥(heldSU n M τ hτ)).map ((φ.comp ρ₀).comp fSU) := by
      refine Subgroup.mem_map.mpr ⟨⟨A₁, hA₁SU⟩, Subgroup.mem_top _, ?_⟩
      rfl
    rw [hmapcomm] at hmem
    exact Subgroup.commutator_mono hSUmapO hSUmapO hmem
  have hDgmem : φ (ρ₀ Dg) ∈ orthDerived Q := by
    obtain ⟨e, heE, heact⟩ := hEtorus (fun i => (d i : M))
      (fun i => QTwoFrameTorus.frame_pow_three_eq_one hM (Units.ne_zero (d i)))
    have hDg_eq_e : φ (ρ₀ Dg) = (e : V ≃ₗ[K] V) := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨⟨dvec, w⟩, rfl⟩ := Φ.surjective v
      change (((ρ₀ Dg : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
        LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (dvec, w)) =
        (e : V ≃ₗ[K] V) (Φ (dvec, w))
      rw [hρ₀ Dg dvec w, heact dvec w]
      congr 1
      refine Prod.ext ?_ rfl
      funext i
      rw [hDgmat]
      change (Matrix.diagonal (fun i => (d i : M))).mulVec dvec i = (d i : M) * dvec i
      rw [Matrix.mulVec_diagonal]
    rw [hDg_eq_e]
    exact e.2
  change φ (ρ₀ A) ∈ orthDerived Q
  rw [hfac, map_mul]
  exact (orthDerived Q).mul_mem hmemA₁ hDgmem


end CFSG.StandardType.QTwoOmFrame

end
