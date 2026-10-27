module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalSubfield
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.Open.QuasithinDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.LocalAnalysis.ComponentInitial

noncomputable def kgLangS1A_pslRingCongr
    (d : ℕ) (hd0 : 0 < d) {F₀ E : Type} [Field F₀] [Field E] (τ : F₀ ≃+* E) :
    LinearFlag.projectiveSL d F₀ ≃* LinearFlag.projectiveSL d E :=
  MulEquiv.ofBijective
    (CFSG.SeitzReduction.LinearPilot.projMap d (τ : F₀ →+* E))
    ⟨CFSG.SeitzReduction.LinearPilot.projMap_injective hd0 _,
      fun x => by
        rw [← MonoidHom.mem_range]
        refine (CFSG.SeitzReduction.LinearPilot.mem_range_projMap (τ : F₀ →+* E)).mpr ?_
        obtain ⟨a, rfl⟩ := LinearFlag.proj_surjective d E x
        exact ⟨a, fun i j => τ.surjective _, rfl⟩⟩

theorem kgLangS1A_pslRingCongr_conjAut
    {d : ℕ} {F₀ E : Type} [Field F₀] [Field E] (hd0 : 0 < d) (τ : F₀ ≃+* E)
    (X : GL (Fin d) F₀) (x : LinearFlag.projectiveSL d F₀) :
    kgLangS1A_pslRingCongr d hd0 τ (LinearFlag.conjAut d F₀ X x) =
      LinearFlag.conjAut d E (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) X)
        (kgLangS1A_pslRingCongr d hd0 τ x) := by
  have h := CFSG.SeitzReduction.LinearPilot.projMap_std_apply (n := d) (K := F₀) (F := E)
    (τ : F₀ →+* E) X (ρ := 1) (ρ' := 1) (by intro c; rfl) (ε := 0) (by norm_num) x
  change CFSG.SeitzReduction.LinearPilot.projMap d (τ : F₀ →+* E)
      (LinearFlag.conjAut d F₀ X x) =
    LinearFlag.conjAut d E (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) X)
      (CFSG.SeitzReduction.LinearPilot.projMap d (τ : F₀ →+* E) x)
  simpa only [map_one, pow_zero, mul_one] using h.symm

private theorem kgLangS1ALinTransferAux_conjAut_mul_inv_eq
    {d : ℕ} {K : Type} [Field K] (A B : GL (Fin d) K) :
    LinearFlag.conjAut d K A * LinearFlag.conjAut d K B * (LinearFlag.conjAut d K A)⁻¹ =
      LinearFlag.conjAut d K (A * B * A⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]

private theorem kgLangS1ALinTransferAux_conj_std
    {d : ℕ} {K : Type} [Field K] (A : GL (Fin d) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1)
    (X : GL (Fin d) K) :
    (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K ^ ε) *
        LinearFlag.conjAut d K X *
        (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K ^ ε)⁻¹ =
      LinearFlag.conjAut d K (A *
        (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : K →+* K) X
         else Matrix.GeneralLinearGroup.inverseTranspose
           (Matrix.GeneralLinearGroup.map (σ : K →+* K) X)) *
        A⁻¹) := by
  obtain ⟨hcc, hff, hfc, hδδ, hδc, hδf, -, -, -⟩ :=
    LinearFlag.standard_automorphism_transport (K := K) (n := d)
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [pow_zero, mul_one, if_pos rfl]
    calc (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ) * LinearFlag.conjAut d K X *
          (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ)⁻¹
        = LinearFlag.conjAut d K A *
            (LinearFlag.fieldAut d K σ * LinearFlag.conjAut d K X *
              (LinearFlag.fieldAut d K σ)⁻¹) * (LinearFlag.conjAut d K A)⁻¹ := by group
      _ = LinearFlag.conjAut d K A *
            LinearFlag.conjAut d K (Matrix.GeneralLinearGroup.map (σ : K →+* K) X) *
            (LinearFlag.conjAut d K A)⁻¹ := by rw [hfc]
      _ = LinearFlag.conjAut d K
            (A * Matrix.GeneralLinearGroup.map (σ : K →+* K) X * A⁻¹) :=
            kgLangS1ALinTransferAux_conjAut_mul_inv_eq A _
  · simp only [pow_one, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    have hδinv : (LinearFlag.dualAut d K)⁻¹ = LinearFlag.dualAut d K :=
      inv_eq_of_mul_eq_one_right hδδ
    have hinv : (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ *
        LinearFlag.dualAut d K)⁻¹ =
        LinearFlag.dualAut d K * (LinearFlag.fieldAut d K σ)⁻¹ *
          (LinearFlag.conjAut d K A)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hδinv]; group
    calc (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K) *
          LinearFlag.conjAut d K X *
          (LinearFlag.conjAut d K A * LinearFlag.fieldAut d K σ * LinearFlag.dualAut d K)⁻¹
        = LinearFlag.conjAut d K A *
            (LinearFlag.fieldAut d K σ *
              (LinearFlag.dualAut d K * LinearFlag.conjAut d K X * LinearFlag.dualAut d K) *
              (LinearFlag.fieldAut d K σ)⁻¹) * (LinearFlag.conjAut d K A)⁻¹ := by
            rw [hinv]; group
      _ = LinearFlag.conjAut d K A *
            (LinearFlag.fieldAut d K σ *
              LinearFlag.conjAut d K (Matrix.GeneralLinearGroup.inverseTranspose X) *
              (LinearFlag.fieldAut d K σ)⁻¹) * (LinearFlag.conjAut d K A)⁻¹ := by rw [hδc]
      _ = LinearFlag.conjAut d K A *
            LinearFlag.conjAut d K
              (Matrix.GeneralLinearGroup.map (σ : K →+* K)
                (Matrix.GeneralLinearGroup.inverseTranspose X)) *
            (LinearFlag.conjAut d K A)⁻¹ := by rw [hfc]
      _ = LinearFlag.conjAut d K
            (A * Matrix.GeneralLinearGroup.map (σ : K →+* K)
                (Matrix.GeneralLinearGroup.inverseTranspose X) * A⁻¹) :=
            kgLangS1ALinTransferAux_conjAut_mul_inv_eq A _
      _ = LinearFlag.conjAut d K
            (A * Matrix.GeneralLinearGroup.inverseTranspose
                (Matrix.GeneralLinearGroup.map (σ : K →+* K) X) * A⁻¹) := by
            rw [Matrix.GeneralLinearGroup.map_inverseTranspose]

private theorem kgLangS1ALinTransferAux_scalar_comm
    {d : ℕ} {K : Type} [Field K] (u : Kˣ) (X : GL (Fin d) K) :
    Matrix.GeneralLinearGroup.scalar (Fin d) u * X =
      X * Matrix.GeneralLinearGroup.scalar (Fin d) u := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact Matrix.scalar_comm (u : K) (fun r' => Commute.all (u : K) r')
    (X : Matrix (Fin d) (Fin d) K)

private theorem kgLangS1ALinTransferAux_exists_scalar_of_conjAut_eq
    {d : ℕ} {K : Type} [Field K] [Finite K] (hd : 0 < d) {X Y : GL (Fin d) K}
    (h : LinearFlag.conjAut d K X = LinearFlag.conjAut d K Y) :
    ∃ u : Kˣ, X = Matrix.GeneralLinearGroup.scalar (Fin d) u * Y := by
  have h1 : LinearFlag.conjAut d K (Y⁻¹ * X) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := CFSG.StandardType.TypeA.exists_scalar_of_conjAut_eq_one h1
  obtain ⟨u, hu⟩ := CFSG.StandardType.TypeA.exists_unit_of_scalar hd hc
  refine ⟨u, ?_⟩
  calc X = Y * (Y⁻¹ * X) := by group
    _ = Y * Matrix.GeneralLinearGroup.scalar (Fin d) u := by rw [hu]
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) u * Y :=
          (kgLangS1ALinTransferAux_scalar_comm u Y).symm

private theorem kgLangS1ALinTransferAux_commute_scalar_mul
    {d : ℕ} {K : Type} [Field K] {X Y : GL (Fin d) K} (h : X * Y = Y * X) (u v : Kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) =
      (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) := by
  have hX : Matrix.GeneralLinearGroup.scalar (Fin d) v * X =
      X * Matrix.GeneralLinearGroup.scalar (Fin d) v :=
    kgLangS1ALinTransferAux_scalar_comm v X
  have hY : Matrix.GeneralLinearGroup.scalar (Fin d) u * Y =
      Y * Matrix.GeneralLinearGroup.scalar (Fin d) u :=
    kgLangS1ALinTransferAux_scalar_comm u Y
  have huv : Matrix.GeneralLinearGroup.scalar (Fin d) u *
      Matrix.GeneralLinearGroup.scalar (Fin d) v =
      Matrix.GeneralLinearGroup.scalar (Fin d) v *
        Matrix.GeneralLinearGroup.scalar (Fin d) u :=
    kgLangS1ALinTransferAux_scalar_comm u (Matrix.GeneralLinearGroup.scalar (Fin d) v)
  calc (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y)
      = Matrix.GeneralLinearGroup.scalar (Fin d) u *
          (Matrix.GeneralLinearGroup.scalar (Fin d) v * X) * Y := by rw [hX]; group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) u *
          Matrix.GeneralLinearGroup.scalar (Fin d) v) * (X * Y) := by group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) v *
          Matrix.GeneralLinearGroup.scalar (Fin d) u) * (X * Y) := by rw [huv]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) v *
          Matrix.GeneralLinearGroup.scalar (Fin d) u) * (Y * X) := by rw [h]
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) v *
          (Matrix.GeneralLinearGroup.scalar (Fin d) u * Y) * X := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) v *
          (Y * Matrix.GeneralLinearGroup.scalar (Fin d) u) * X := by rw [hY]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) := by group

private theorem kgLangS1ALinTransferAux_star_comm
    {d : ℕ} {K : Type} [Field K] (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    {X Y : GL (Fin d) K} (h : X * Y = Y * X) :
    (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : K →+* K) X
      else Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.map (σ : K →+* K) X)) *
    (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : K →+* K) Y
      else Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.map (σ : K →+* K) Y)) =
    (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : K →+* K) Y
      else Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.map (σ : K →+* K) Y)) *
    (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : K →+* K) X
      else Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.map (σ : K →+* K) X)) := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [if_true]
    rw [← map_mul, ← map_mul, h]
  · simp only [if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h]

private theorem kgLangS1ALinTransferAux_conj_comm
    {d : ℕ} {K : Type} [Field K] {A X Y : GL (Fin d) K} (h : X * Y = Y * X) :
    (A * X * A⁻¹) * (A * Y * A⁻¹) = (A * Y * A⁻¹) * (A * X * A⁻¹) := by
  rw [show (A * X * A⁻¹) * (A * Y * A⁻¹) = A * (X * Y) * A⁻¹ from by group,
    show (A * Y * A⁻¹) * (A * X * A⁻¹) = A * (Y * X) * A⁻¹ from by group, h]

theorem kgLangS1A_commute_transfer {d : ℕ} {F₀ E : Type} [Field F₀] [Finite F₀] [Field E]
    [Finite E] (hd : 3 ≤ d) (hcard : Nat.card E = Nat.card F₀)
    (ψ : LinearFlag.projectiveSL d F₀ ≃* LinearFlag.projectiveSL d E)
    {M N : GL (Fin d) F₀} {g h : GL (Fin d) E}
    (hM : ∀ x, ψ (LinearFlag.conjAut d F₀ M x) = LinearFlag.conjAut d E g (ψ x))
    (hN : ∀ x, ψ (LinearFlag.conjAut d F₀ N x) = LinearFlag.conjAut d E h (ψ x))
    (hgh : g * h = h * g) : M * N = N * M := by
  classical
  have hd0 : 0 < d := by omega
  letI := Fintype.ofFinite F₀
  letI := Fintype.ofFinite E
  have hcard' : Fintype.card F₀ = Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard.symm
  let τ : F₀ ≃+* E := FiniteField.ringEquivOfCardEq hcard'
  let gτ : LinearFlag.projectiveSL d F₀ ≃* LinearFlag.projectiveSL d E :=
    kgLangS1A_pslRingCongr d hd0 τ
  let β : MulAut (LinearFlag.projectiveSL d E) := ψ.symm.trans gτ
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    (LinearFlag.automorphism_generation (K := E) (n := d) hd).2 β
  let Star : GL (Fin d) E → GL (Fin d) E := fun X =>
    if ε = 0 then Matrix.GeneralLinearGroup.map (σ : E →+* E) X
    else Matrix.GeneralLinearGroup.inverseTranspose
      (Matrix.GeneralLinearGroup.map (σ : E →+* E) X)
  let Pg : GL (Fin d) E := A * Star g * A⁻¹
  let Ph : GL (Fin d) E := A * Star h * A⁻¹
  have hβconj : β * LinearFlag.conjAut d E g * β⁻¹ =
      LinearFlag.conjAut d E (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) M) := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := β.surjective x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    simp only [β, MulEquiv.trans_apply]
    have hM' : ψ.symm (LinearFlag.conjAut d E g y) =
        LinearFlag.conjAut d F₀ M (ψ.symm y) := by
      refine ψ.injective ?_
      rw [MulEquiv.apply_symm_apply, hM (ψ.symm y), MulEquiv.apply_symm_apply]
    rw [hM']
    exact kgLangS1A_pslRingCongr_conjAut hd0 τ M (ψ.symm y)
  have hβstd : β * LinearFlag.conjAut d E g * β⁻¹ = LinearFlag.conjAut d E Pg := by
    rw [hβ]
    exact kgLangS1ALinTransferAux_conj_std A σ ε hε g
  have hβconj' : β * LinearFlag.conjAut d E h * β⁻¹ =
      LinearFlag.conjAut d E (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) N) := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := β.surjective x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    simp only [β, MulEquiv.trans_apply]
    have hN' : ψ.symm (LinearFlag.conjAut d E h y) =
        LinearFlag.conjAut d F₀ N (ψ.symm y) := by
      refine ψ.injective ?_
      rw [MulEquiv.apply_symm_apply, hN (ψ.symm y), MulEquiv.apply_symm_apply]
    rw [hN']
    exact kgLangS1A_pslRingCongr_conjAut hd0 τ N (ψ.symm y)
  have hβstd' : β * LinearFlag.conjAut d E h * β⁻¹ = LinearFlag.conjAut d E Ph := by
    rw [hβ]
    exact kgLangS1ALinTransferAux_conj_std A σ ε hε h
  obtain ⟨u, hu⟩ := kgLangS1ALinTransferAux_exists_scalar_of_conjAut_eq hd0
    (hβconj.symm.trans hβstd)
  obtain ⟨v, hv⟩ := kgLangS1ALinTransferAux_exists_scalar_of_conjAut_eq hd0
    (hβconj'.symm.trans hβstd')
  have hPgPh : Pg * Ph = Ph * Pg := by
    have hstar : Star g * Star h = Star h * Star g := by
      change (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : E →+* E) g
          else Matrix.GeneralLinearGroup.inverseTranspose
            (Matrix.GeneralLinearGroup.map (σ : E →+* E) g)) *
        (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : E →+* E) h
          else Matrix.GeneralLinearGroup.inverseTranspose
            (Matrix.GeneralLinearGroup.map (σ : E →+* E) h)) =
        (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : E →+* E) h
          else Matrix.GeneralLinearGroup.inverseTranspose
            (Matrix.GeneralLinearGroup.map (σ : E →+* E) h)) *
        (if ε = 0 then Matrix.GeneralLinearGroup.map (σ : E →+* E) g
          else Matrix.GeneralLinearGroup.inverseTranspose
            (Matrix.GeneralLinearGroup.map (σ : E →+* E) g))
      exact kgLangS1ALinTransferAux_star_comm σ hε hgh
    exact kgLangS1ALinTransferAux_conj_comm hstar
  have hcomm : (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) M) *
      (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) N) =
      (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) N) *
      (Matrix.GeneralLinearGroup.map (τ : F₀ →+* E) M) := by
    rw [hu, hv]
    exact kgLangS1ALinTransferAux_commute_scalar_mul hPgPh u v
  rw [← map_mul, ← map_mul] at hcomm
  exact Matrix.GeneralLinearGroup.map_injective τ.injective hcomm

end CFSG.StandardType
