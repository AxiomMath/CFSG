module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSU
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOmFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOm2
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.StandardType.QTwoFrameTorus
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup mem_sesqUnitaryGroup)
open Matrix

theorem ggQTwoUFrame_of_cfg_orth {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup ↥(orthDerived Q)} {x : ↥(orthDerived Q)} {L D J : Subgroup ↥(orthDerived Q)}
    (hC : GGQTwoFRCfg E x L D J) :
    ∃ (n : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ y, τ (τ y) = y)
      (ρ : ↥(heldGU n M τ hτ) →* ↥(orthDerived Q)),
      Nat.card M = 4 ∧ (∀ y, τ y = y ^ 2) ∧ GGQTwoUFrame ρ E x L := by
  obtain ⟨n, M, _, _, _, τ, U, _, _, Φ, c, hM, hτ2, hc2, hpol, hnorm, hx, hEdiag,
    hEtorus⟩ := exists_traceFrame_of_cfg_orth hK hQ hC
  have : Fintype M := Fintype.ofFinite M
  have h4 : ∀ y : M, y ^ 4 = y := by
    intro y
    have h := FiniteField.pow_card y
    rwa [← Nat.card_eq_fintype_card, hM] at h
  have hτ : ∀ y, τ (τ y) = y := by
    intro y
    calc τ (τ y) = τ (y ^ 2) := congrArg τ (hτ2 y)
      _ = (τ y) ^ 2 := map_pow τ y 2
      _ = (y ^ 2) ^ 2 := by rw [hτ2]
      _ = y ^ 4 := by rw [← pow_mul]
      _ = y := h4 y
  have hn4 : 4 ≤ n := QTwoOmFrame.four_le_of_diag hC hM hEdiag
  obtain ⟨ρ₀, hρ₀inj, hρ₀apply, hfrob, hcent⟩ :=
    exists_heldGU_rep_of_traceFrame (K := K) (M := M) (V := V) (U := U)
      hK hM hτ Φ hpol
  let φ : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q)) →* (V ≃ₗ[K] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp
      (Subgroup.subtype (sesqUnitaryGroup (QuadraticMap.polarBilin Q)))
  have hOg : ∀ A : ↥(heldGU n M τ hτ),
      LinearMap.GeneralLinearGroup.generalLinearEquiv K V
        ((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
          LinearMap.GeneralLinearGroup K V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun A => QTwoOmFrame.rho_mem_orthogonalGroup hnorm hρ₀apply A
  have hchar : CharP M 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) (by rw [hM]; norm_num)
  have hSUeq : heldSU n M τ hτ = CFSG.Open.StatedSU n 2 M :=
    hct_heldSU_eq_statedSU (Q := 2) hτ2
  have hSUperf : Group.IsPerfect ↥(heldSU n M τ hτ) := by
    rw [hSUeq]
    exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) (n := n)
      (by rw [hM]; norm_num) (le_trans (by norm_num) hn4)
      (by
        intro h
        have hn3 : n = 3 := by simpa using congrArg Prod.fst h
        omega)
  have hρmem : ∀ A : ↥(heldGU n M τ hτ),
      LinearMap.GeneralLinearGroup.generalLinearEquiv K V
        ((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
          LinearMap.GeneralLinearGroup K V) ∈ orthDerived Q :=
    fun A => QTwoOmFrame.rho_mem_orthDerived hM hτ2 hn4 hρ₀apply hOg hSUperf hEtorus A
  have hρmem' : ∀ A : ↥(heldGU n M τ hτ), φ (ρ₀ A) ∈ orthDerived Q :=
    fun A => hρmem A
  let ρ : ↥(heldGU n M τ hτ) →* ↥(orthDerived Q) :=
    (φ.comp ρ₀).codRestrict (orthDerived Q) hρmem'
  have hρinj : Function.Injective ρ := by
    intro A A' h
    apply hρ₀inj
    apply Subtype.ext
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
    exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) h
  have hE : ∀ g : ↥(orthDerived Q), g ∈ E ↔ ∃ A : ↥(heldGU n M τ hτ),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) ∧
        ρ A = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨a, ha3, hact⟩ := hEdiag g hg
      let d : Fin n → Mˣ := fun i => Units.mk0 (a i) (by
        intro hzero
        have h := ha3 i
        rw [hzero] at h
        norm_num at h)
      let A : ↥(heldGU n M τ hτ) :=
        ↑(frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 d)
      have hAmat : ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
          Matrix.diagonal (fun i => (d i : M)) := by
        dsimp only [A]
        rw [frameDiagEquiv_apply_val, frameDiagGL_val]
      refine ⟨A, ?_, ?_⟩
      · intro i j hij
        rw [hAmat]
        exact Matrix.diagonal_apply_ne _ hij
      · apply Subtype.ext
        change φ (ρ₀ A) = (g : V ≃ₗ[K] V)
        apply LinearEquiv.ext
        intro v
        obtain ⟨⟨dvec, w⟩, rfl⟩ := Φ.surjective v
        change (((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
          LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (dvec, w)) =
          (g : V ≃ₗ[K] V) (Φ (dvec, w))
        rw [hρ₀apply A dvec w, hact dvec w]
        congr 1
        refine Prod.ext ?_ rfl
        funext i
        rw [hAmat]
        change (Matrix.diagonal (fun i => (d i : M))).mulVec dvec i = a i * dvec i
        rw [Matrix.mulVec_diagonal, Units.val_mk0]
    · rintro ⟨A, hdiag, rfl⟩
      let a : Fin n → M := fun i => ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i
      have hAmat : ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
          Matrix.diagonal a := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [a]
        · rw [hdiag i j hij]
          simp [Matrix.diagonal_apply_ne _ hij]
      have ha3 : ∀ i, a i ^ 3 = 1 := fun i =>
        QTwoFrameTorus.frame_pow_three_eq_one hM
          (QTwoFrameTorus.frame_diag_entry_ne_zero (n := n) hdiag i)
      obtain ⟨e, heE, heact⟩ := hEtorus a ha3
      have heq : e = ρ A := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        obtain ⟨⟨dvec, w⟩, rfl⟩ := Φ.surjective v
        change (e : V ≃ₗ[K] V) (Φ (dvec, w)) = φ (ρ₀ A) (Φ (dvec, w))
        rw [heact dvec w]
        change Φ (fun i => a i * dvec i, w) =
          (((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
            LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (dvec, w))
        rw [hρ₀apply A dvec w, hAmat]
        congr 1
        refine Prod.ext ?_ rfl
        funext i
        change a i * dvec i = (Matrix.diagonal a).mulVec dvec i
        rw [Matrix.mulVec_diagonal]
      exact heq ▸ heE
  have hc0 : c ≠ 0 := by
    intro h
    exact hc2 (by rw [h]; simp)
  have hc1 : c ≠ 1 := by
    intro h
    exact hc2 (by rw [h]; simp)
  let d0 : Fin n → Mˣ := fun _ => Units.mk0 c hc0
  let A₀ : ↥(heldGU n M τ hτ) :=
    ↑(frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 d0)
  have hA₀mat : ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun _ => c) := by
    dsimp only [A₀]
    rw [frameDiagEquiv_apply_val, frameDiagGL_val]
    simp [d0]
  have hA₀x : ρ A₀ = x := by
    apply Subtype.ext
    change φ (ρ₀ A₀) = (x : V ≃ₗ[K] V)
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨dvec, w⟩, rfl⟩ := Φ.surjective v
    change (((ρ₀ A₀ : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
      LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (dvec, w)) =
      (x : V ≃ₗ[K] V) (Φ (dvec, w))
    rw [hρ₀apply A₀ dvec w, hA₀mat]
    change Φ ((Matrix.diagonal (fun _ => c)).mulVec dvec, w) =
      (x : V ≃ₗ[K] V) (Φ (dvec, w))
    rw [hx dvec w]
    congr 1
    refine Prod.ext ?_ rfl
    funext i
    change (Matrix.diagonal (fun _ => c)).mulVec dvec i = (c • dvec) i
    rw [Matrix.mulVec_diagonal]
    simp [Pi.smul_apply, smul_eq_mul]
  have hN' : ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)),
      ∀ A : ↥(heldGU n M τ hτ), (A : GL (Fin n) M) ∈ heldSU n M τ hτ →
      ∃ A' : ↥(heldGU n M τ hτ), (A' : GL (Fin n) M) ∈ heldSU n M τ hτ ∧
        g * ρ A * g⁻¹ = ρ A' := by
    intro g hg A hA
    have hgx : x * g = g * x :=
      (Subgroup.mem_centralizer_iff.mp hg) x (Set.mem_singleton x)
    have hgO : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) g.2
    let u : LinearMap.GeneralLinearGroup K V :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm (g : V ≃ₗ[K] V)
    have hu_eq : (LinearMap.GeneralLinearGroup.generalLinearEquiv K V) u =
        (g : V ≃ₗ[K] V) := by
      simp [u]
    have hu_apply : ∀ x, (u : V →ₗ[K] V) x = (g : V ≃ₗ[K] V) x := by
      intro x
      have h := congrFun (congrArg (fun e : V ≃ₗ[K] V => (e : V → V)) hu_eq) x
      simpa only [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] using h
    have hgS : u ∈ sesqUnitaryGroup (QuadraticMap.polarBilin Q) := by
      rw [mem_sesqUnitaryGroup]
      intro x y
      change QuadraticMap.polarBilin Q ((u : V →ₗ[K] V) x) ((u : V →ₗ[K] V) y) =
        QuadraticMap.polarBilin Q x y
      rw [hu_apply x, hu_apply y]
      exact CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO x y
    let gs : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q)) := ⟨u, hgS⟩
    have hA₀xφ : (LinearMap.GeneralLinearGroup.generalLinearEquiv K V) (ρ₀ A₀) =
        (x : V ≃ₗ[K] V) :=
      congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) hA₀x
    have hs : ∀ d w,
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) (ρ₀ A₀) :
          V →ₗ[K] V) (Φ (d, w)) = Φ (c • d, w) := by
      intro d w
      have hx' : ((x : V ≃ₗ[K] V) : V →ₗ[K] V) (Φ (d, w)) = Φ (c • d, w) := hx d w
      have h := congrArg (fun e : V ≃ₗ[K] V => (e : V →ₗ[K] V) (Φ (d, w))) hA₀xφ
      rwa [hx'] at h
    have hcommS : gs * ρ₀ A₀ = ρ₀ A₀ * gs := by
      apply Subtype.ext
      change u * (ρ₀ A₀ : LinearMap.GeneralLinearGroup K V) =
        (ρ₀ A₀ : LinearMap.GeneralLinearGroup K V) * u
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
      rw [map_mul, map_mul]
      rw [hu_eq, hA₀xφ]
      simpa only [Subgroup.coe_mul] using
        congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) hgx.symm
    obtain ⟨Ag, g0, hgact⟩ := hcent (ρ₀ A₀) gs c hc2 hs hcommS
    have hgact' : ∀ d w, (g : V ≃ₗ[K] V) (Φ (d, w)) =
        Φ (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d, g0 w) := by
      intro d w
      rw [← hu_apply (Φ (d, w))]
      exact hgact d w
    let A' : ↥(heldGU n M τ hτ) :=
      ⟨(Ag : GL (Fin n) M) * (A : GL (Fin n) M) * (Ag : GL (Fin n) M)⁻¹, by
        exact (heldGU n M τ hτ).mul_mem
          ((heldGU n M τ hτ).mul_mem Ag.2 A.2) ((heldGU n M τ hτ).inv_mem Ag.2)⟩
    have hGL : (A' : GL (Fin n) M) * (Ag : GL (Fin n) M) =
        (Ag : GL (Fin n) M) * (A : GL (Fin n) M) := by
      change ((Ag : GL (Fin n) M) * (A : GL (Fin n) M) * (Ag : GL (Fin n) M)⁻¹) *
        (Ag : GL (Fin n) M) = (Ag : GL (Fin n) M) * (A : GL (Fin n) M)
      group
    have hGLm : ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        ((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        ((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
      rw [← Units.val_mul, ← Units.val_mul, hGL]
    have hA'vec : ∀ d : Fin n → M,
        ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ
          (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d) =
        ((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ
          (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d) := by
      intro d
      rw [Matrix.mulVec_mulVec, hGLm, ← Matrix.mulVec_mulVec]
    have hA'SU : (A' : GL (Fin n) M) ∈ heldSU n M τ hτ := by
      refine Subgroup.mem_inf.mpr ⟨A'.2, ?_⟩
      refine CFSG.Open.StatedAPI.mem_statedSL_of_det ?_
      have hAunit : Matrix.GeneralLinearGroup.det (A : GL (Fin n) M) = 1 := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact CFSG.Open.StatedAPI.det_of_mem_statedSL (Subgroup.mem_inf.mp hA).2
      have hA'unit : Matrix.GeneralLinearGroup.det (A' : GL (Fin n) M) = 1 := by
        change Matrix.GeneralLinearGroup.det
          ((Ag : GL (Fin n) M) * (A : GL (Fin n) M) * (Ag : GL (Fin n) M)⁻¹) = 1
        rw [map_mul, map_mul, map_inv, hAunit]
        simp
      rw [← Matrix.GeneralLinearGroup.val_det_apply (A' : GL (Fin n) M), hA'unit,
        Units.val_one]
    refine ⟨A', hA'SU, ?_⟩
    have hleft : (g * ρ A * g⁻¹) * g = g * ρ A := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hEq : (g * ρ A * g⁻¹) * g = ρ A' * g := by
      rw [hleft]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      obtain ⟨⟨dvec, w⟩, rfl⟩ := Φ.surjective v
      have hρA : φ (ρ₀ A) (Φ (dvec, w)) =
          Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec, w) := by
        change (((ρ₀ A : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
          LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (dvec, w)) = _
        rw [hρ₀apply A dvec w]
      have hρA' : φ (ρ₀ A')
          (Φ (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec, g0 w)) =
          Φ (((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ
            (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec), g0 w) := by
        change (((ρ₀ A' : ↥(sesqUnitaryGroup (QuadraticMap.polarBilin Q))) :
          LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
            (Φ (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec, g0 w)) = _
        rw [hρ₀apply A' (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec)
          (g0 w)]
      change ((g : V ≃ₗ[K] V) * φ (ρ₀ A)) (Φ (dvec, w)) =
        (φ (ρ₀ A') * (g : V ≃ₗ[K] V)) (Φ (dvec, w))
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρA]
      rw [show (g : V ≃ₗ[K] V) (Φ (((A : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) *ᵥ dvec, w)) =
          Φ (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ
            (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec), g0 w) from
        hgact' (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec) w]
      rw [show (g : V ≃ₗ[K] V) (Φ (dvec, w)) =
          Φ (((Ag : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ dvec, g0 w) from
        hgact' dvec w]
      rw [hρA', hA'vec dvec]
    exact mul_right_cancel hEq
  have hL : L = ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) :=
      Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
    have : Finite ↥(orthDerived Q) := Subtype.finite
    exact ggQTwo_L_eq_map_heldSU hC hM hτ2 hρinj hE hc2 hA₀mat hA₀x hN'
  have halpha : ∀ i : Fin n, ∃ α : MulAut ↥(orthDerived Q),
      (∀ A A' : ↥(heldGU n M τ hτ),
        (∀ j k, j ≠ k → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
        (∀ j k, j ≠ k → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
        ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
          τ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) →
        (∀ j, j ≠ i → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j =
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j) →
        α (ρ A) = ρ A') ∧
      ∀ A : ↥(heldGU n M τ hτ),
        (∀ j, j ≠ i → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0 ∧
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j i = 0) →
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i = 1 → α (ρ A) = ρ A := by
    intro i
    obtain ⟨f, hf_act, hf_diag, hf_triv⟩ := hfrob i
    let fV : V ≃ₗ[K] V := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V) f
    have hfV : ∀ x, fV x = ((f : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x := by
      intro x
      exact congrFun (LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv
        (R := K) (M := V) (f := f)) x
    have hfO : fV ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      obtain ⟨⟨dvec, w⟩, rfl⟩ := Φ.surjective v
      change Q (fV (Φ (dvec, w))) = Q (Φ (dvec, w))
      rw [hfV (Φ (dvec, w)), hf_act dvec w]
      apply (algebraMap K M).injective
      rw [hnorm (Function.update dvec i (τ (dvec i))) w, hnorm dvec w]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self]
        rw [hτ (dvec j), hτ2]
        ring
      · rw [Function.update_of_ne hji]
    have hmapO : (TauCeti.QuadraticMap.orthogonalGroup Q).map
        (MulAut.conj fV).toMonoidHom =
        TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hfO)
    have hmapDer : (orthDerived Q).map (MulAut.conj fV).toMonoidHom =
        orthDerived Q := by
      change ((⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).map
          (MulAut.conj fV).toMonoidHom) = _
      rw [Subgroup.map_commutator, hmapO]
    let α : MulAut ↥(orthDerived Q) :=
      (Subgroup.equivMapOfInjective (orthDerived Q)
        (MulAut.conj fV).toMonoidHom
        (MulAut.conj fV).injective).trans
        (MulEquiv.subgroupCongr hmapDer)
    refine ⟨α, ?_, ?_⟩
    · intro A A' hA hA' hii hjj
      have h := congrArg φ (hf_diag A A' hA hA' hii hjj)
      apply Subtype.ext
      change fV * (ρ A : V ≃ₗ[K] V) * fV⁻¹ =
        (ρ A' : V ≃ₗ[K] V)
      simpa [ρ, φ, fV, map_mul, map_inv] using h
    · intro A htriv hii
      have h := congrArg φ (hf_triv A htriv hii)
      apply Subtype.ext
      change fV * (ρ A : V ≃ₗ[K] V) * fV⁻¹ =
        (ρ A : V ≃ₗ[K] V)
      simpa [ρ, φ, fV, map_mul, map_inv] using h
  exact ⟨n, M, inferInstance, inferInstance, τ, hτ, ρ, hM, hτ2,
    ⟨hρinj, hE, ⟨A₀, c, hc1, hA₀mat, hA₀x⟩, hL, halpha⟩⟩


end CFSG.StandardType

end
