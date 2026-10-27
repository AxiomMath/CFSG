module

public import CFSG.Milestones.ASVolI.F431.BF436U5A
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F431.BCoreU5Chart

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF.ClassicalRoots

section GraphData5

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_u5_graph_data (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) {fb : E}
    (hg : hyp.chart.IsGraphInv fb) :
    ∃ (mk : Marking .U5 2 1 ↥Gp) (conj : MulAut ↥Gp) (sigma : mk.field →+* mk.field),
      (∀ p, sigma p = p ^ (2 ^ 1)) ∧
      Gp ⊓ M₁ = (mk.parabolic false).map Gp.subtype ∧
      Gp ⊓ M₂ = (mk.parabolic true).map Gp.subtype ∧
      ∀ A : nativeGroup .U5 (2 ^ 1) mk.field, ∃ B : nativeGroup .U5 (2 ^ 1) mk.field,
        (B : GL (Coord .U5) mk.field) =
            mk.basis * Matrix.GeneralLinearGroup.map sigma
              (mk.basis⁻¹ * (A : GL (Coord .U5) mk.field) * mk.basis) * mk.basis⁻¹ ∧
          ((conj (mk.transport B) : ↥Gp) : E) =
            fb * ((conj (mk.transport A) : ↥Gp) : E) * fb⁻¹ := by
  obtain ⟨-, -, -, conj, -, hpure⟩ := hg
  have hfits := hyp.chart.coordinatePayload_fits
  have hm := hyp.chart_matches
  generalize hcp : hyp.chart.coordinatePayload = cp at hpure hfits
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .U5 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    simp only [NativeCoordinates.transport, NativeCoordinates.PureGraphAction,
      NativeRepresentativeAction] at hpure
    obtain ⟨-, sigma, hsig, hrep⟩ := hpure
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    refine ⟨mk, conj, sigma, hsig, ?_, ?_, fun A => ?_⟩
    · rw [hm.2.1]
      exact hpts
    · rw [hm.2.2]
      exact hlns
    · obtain ⟨B, hB, hBA⟩ := hrep A
      exact ⟨B, hB, hBA⟩
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

end GraphData5

section Transport5

theorem burnsideF4m_matrix_frob_n {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {n : ℕ}
    (σ : K →+* K) (Bm Bi : Matrix (Fin n) (Fin n) K) (hBiBm : Bi * Bm = 1)
    (P : Matrix (Fin n) ι K) (Q : Matrix ι (Fin n) K) (hPs : P.map σ = P) (hQs : Q.map σ = Q)
    (g : Matrix ι ι K) :
    Bm * (Bi * (Bm * P * g * (Q * Bi)) * Bm).map σ * Bi = Bm * P * g.map σ * (Q * Bi) := by
  have e1 : Bi * (Bm * P * g * (Q * Bi)) * Bm = P * g * Q := by
    rw [show Bi * (Bm * P * g * (Q * Bi)) * Bm = (Bi * Bm) * P * g * Q * (Bi * Bm) by
      simp only [Matrix.mul_assoc], hBiBm, Matrix.one_mul, Matrix.mul_one]
  rw [e1, Matrix.map_mul, Matrix.map_mul, hPs, hQs]
  simp only [Matrix.mul_assoc]

variable {H : Type} [Group H] (mk : Marking .U5 2 1 H)

theorem burnsideF4m_u5_T_frob (sigma : mk.field →+* mk.field) (hsig : ∀ p, sigma p = p ^ (2 ^ 1))
    (g : hypSU (burnsideF4m_U5_fieldData mk) 2 1) :
    mk.basis * Matrix.GeneralLinearGroup.map sigma
        (mk.basis⁻¹ * ((burnsideF4m_U5_T mk g : nativeGroup .U5 (2 ^ 1) mk.field) :
          GL (Coord .U5) mk.field) * mk.basis) * mk.basis⁻¹ =
      ((burnsideF4m_U5_T mk (fieldAut (burnsideF4m_U5_fieldData mk)
          (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) g) :
        nativeGroup .U5 (2 ^ 1) mk.field) : GL (Coord .U5) mk.field) := by
  have hBiBm : ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) *
      (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBmBi : (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
      ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hR := burnsideF4m_U5_isHypTransport mk
  have h1 := transportInv_mul hR
  have hRP : burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) =
      (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id fullPosEquiv := by
    ext i a
    simp only [burnsideF4m_hypR, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.one_apply, id,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hPQ : (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id
      (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) *
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
        (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]
    ext i j
    simp [Matrix.one_apply]
  have hRinv : transportInv (burnsideF4m_U5_fieldData mk)
      (burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) =
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
        (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id *
        ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) := by
    set Rinv := transportInv (burnsideF4m_U5_fieldData mk)
      (burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field))
    have hq : Rinv * (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) =
        (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
          (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id := by
      calc Rinv * (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)
          = Rinv * (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
              ((1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id
                (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) *
                (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
                  (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id) := by
            rw [hPQ, Matrix.mul_one]
        _ = Rinv * ((mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
              (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id
                (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1))) *
              (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
                (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hRP, h1, Matrix.one_mul]
    calc Rinv = Rinv * ((mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
          ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field)) := by
          rw [hBmBi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hq]
  have hPs : ((1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id
      (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1))).map sigma =
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id
        (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) := by
    ext i a
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hQs : ((1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
      (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id).map sigma =
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
        (fullPosEquiv : HypIndex 2 1 ≃ Fin (2 * 2 + 1)) id := by
    ext a i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hbar : ((g : GL (HypIndex 2 1) mk.field) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field).map sigma =
      ((g : GL (HypIndex 2 1) mk.field) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field).map
          (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) := by
    ext a b
    simp only [Matrix.map_apply, hsig, CFSG.Quasithin.H13.F431.Un.OL5.fld5_bar_apply,
      (burnsideF4m_U5_fieldData mk).bar_apply]
  apply Units.ext
  have hT : (((burnsideF4m_U5_T mk g : nativeGroup .U5 (2 ^ 1) mk.field) :
      GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) =
      burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        ((g : GL (HypIndex 2 1) mk.field) : Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) *
        transportInv (burnsideF4m_U5_fieldData mk)
          (burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) :=
    coe_hypTransport hR g
  have hfa : (((fieldAut (burnsideF4m_U5_fieldData mk)
      (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) g :
        hypSU (burnsideF4m_U5_fieldData mk) 2 1) : GL (HypIndex 2 1) mk.field) :
          Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) =
      ((g : GL (HypIndex 2 1) mk.field) : Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field).map
        (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) := rfl
  have hT' : (((burnsideF4m_U5_T mk (fieldAut (burnsideF4m_U5_fieldData mk)
      (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) g) :
        nativeGroup .U5 (2 ^ 1) mk.field) :
      GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) =
      burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        (((fieldAut (burnsideF4m_U5_fieldData mk)
          (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) g :
            hypSU (burnsideF4m_U5_fieldData mk) 2 1) : GL (HypIndex 2 1) mk.field) :
              Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) *
        transportInv (burnsideF4m_U5_fieldData mk)
          (burnsideF4m_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) :=
    coe_hypTransport hR (fieldAut (burnsideF4m_U5_fieldData mk)
      (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) g)
  rw [hfa, ← hbar, hRinv, hRP] at hT'
  rw [hRinv, hRP] at hT
  change (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
      ((((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) *
        (((burnsideF4m_U5_T mk g : nativeGroup .U5 (2 ^ 1) mk.field) : GL (Coord .U5) mk.field) :
          Matrix (Fin 5) (Fin 5) mk.field) *
        (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)).map sigma) *
      ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) = _
  rw [hT, hT']
  exact burnsideF4m_matrix_frob_n sigma _ _ hBiBm _ _ hPs hQs _

noncomputable def burnsideF4m_U5_Psi :
    hypPSU (burnsideF4m_U5_fieldData mk) 2 1 ≃* H :=
  (hypPSUEquivStatedProj (burnsideF4m_U5_fieldData mk) (burnsideF4m_U5_isHypTransport mk)
    (by norm_num)).trans mk.identification

theorem burnsideF4m_U5_Psi_proj (g : hypSU (burnsideF4m_U5_fieldData mk) 2 1) :
    burnsideF4m_U5_Psi mk (hypProj _ 2 1 g) = mk.transport (burnsideF4m_U5_T mk g) := by
  show mk.identification (hypPSUEquivStatedProj _ _ _ (hypProj _ 2 1 g)) = _
  rw [hypPSUEquivStatedProj_hypProj]
  rfl

theorem burnsideF4m_U5_Psi_parabolics :
    mk.parabolic false =
        (u5PtP (burnsideF4m_U5_fieldData mk)).map (burnsideF4m_U5_Psi mk).toMonoidHom ∧
      mk.parabolic true =
        (u5LnP (burnsideF4m_U5_fieldData mk)).map (burnsideF4m_U5_Psi mk).toMonoidHom := by
  have hcomp : (burnsideF4m_U5_Psi mk).toMonoidHom.comp
      (hypProj (burnsideF4m_U5_fieldData mk) 2 1) =
      mk.transport.comp (burnsideF4m_U5_T mk).toMonoidHom :=
    MonoidHom.ext fun g => burnsideF4m_U5_Psi_proj mk g
  refine ⟨?_, ?_⟩
  · rw [u5PtP, projIsoStabilizer, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      ← burnsideF4m_U5_parabolic_false]
    rfl
  · rw [u5LnP, projIsoStabilizer, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      ← burnsideF4m_U5_parabolic_true]
    rfl

end Transport5

section FrobConj5

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_u5_fb_acts (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) {fb : E}
    (hg : hyp.chart.IsGraphInv fb) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 1 K) (Ψ : hypPSU h 2 1 ≃* ↥Gp)
      (conj : MulAut ↥Gp),
      Gp ⊓ M₁ = (u5PtP h).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      Gp ⊓ M₂ = (u5LnP h).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      ∀ y : hypPSU h 2 1, ((conj (Ψ (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y)) :
        ↥Gp) : E) = fb * ((conj (Ψ y) : ↥Gp) : E) * fb⁻¹ := by
  obtain ⟨mk, conj, sigma, hsig, h1, h2, hrep⟩ := burnsideF4m_u5_graph_data hyp hg
  obtain ⟨e1, e2⟩ := burnsideF4m_U5_Psi_parabolics mk
  refine ⟨mk.field, inferInstance, burnsideF4m_U5_fieldData mk, burnsideF4m_U5_Psi mk, conj,
    ?_, ?_, fun y => ?_⟩
  · rw [h1, e1, Subgroup.map_map]
  · rw [h2, e2, Subgroup.map_map]
  · obtain ⟨g, rfl⟩ := hypProj_surjective _ 2 1 y
    obtain ⟨B, hB, hBA⟩ := hrep (burnsideF4m_U5_T mk g)
    have hBeq : B = burnsideF4m_U5_T mk (fieldAut (burnsideF4m_U5_fieldData mk)
        (CFSG.Quasithin.H13.F431.Un.OL5.bar5 (burnsideF4m_U5_fieldData mk)) g) :=
      Subtype.ext (hB.trans (burnsideF4m_u5_T_frob mk sigma hsig g))
    rw [fieldP_apply, burnsideF4m_U5_Psi_proj, burnsideF4m_U5_Psi_proj, ← hBeq]
    exact hBA

theorem burnsideF4m_u5_exists_frob_conj (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) {fb : E}
    (hg : hyp.chart.IsGraphInv fb) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 1 K) (Ψ : hypPSU h 2 1 ≃* ↥Gp) (a : ↥Gp),
      Gp ⊓ M₁ = (u5PtP h).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      Gp ⊓ M₂ = (u5LnP h).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      ∀ y : hypPSU h 2 1, ((a : E)⁻¹ * fb * a) * (Ψ y : E) * ((a : E)⁻¹ * fb * a)⁻¹ =
        (Ψ (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y) : E) := by
  obtain ⟨K, fK, h, Ψ, conj, h1, h2, hact⟩ := burnsideF4m_u5_fb_acts hyp hg
  have := h.finite
  obtain ⟨g₀, τ, hδ⟩ := burnsideF4m_u5_normalForm h ((Ψ.trans conj).trans Ψ.symm)
  have hδy : ∀ y, conj (Ψ y) =
      Ψ (hypProj h 2 1 g₀ * fieldP h τ y * (hypProj h 2 1 g₀)⁻¹) := by
    intro y
    have := congrArg (fun α : MulAut (hypPSU h 2 1) => α y) hδ
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, innM_apply] at this
    rw [← this, MulEquiv.apply_symm_apply]
  refine ⟨K, fK, h, Ψ, Ψ (hypProj h 2 1 g₀), h1, h2, fun y => ?_⟩
  set y' := (fieldP h τ).symm y with hy'
  have hy'y : fieldP h τ y' = y := (fieldP h τ).apply_symm_apply y
  have hcomm : fieldP h τ (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y') =
      fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y := by
    rw [← MulAut.mul_apply, fieldP_comm h τ (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h),
      MulAut.mul_apply, hy'y]
  have e1 := hact y'
  rw [hδy, hδy, hcomm, hy'y] at e1
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at e1
  calc ((Ψ (hypProj h 2 1 g₀) : E))⁻¹ * fb * (Ψ (hypProj h 2 1 g₀) : E) * (Ψ y : E) *
        ((Ψ (hypProj h 2 1 g₀) : E)⁻¹ * fb * (Ψ (hypProj h 2 1 g₀) : E))⁻¹
      = (Ψ (hypProj h 2 1 g₀) : E)⁻¹ * (fb * ((Ψ (hypProj h 2 1 g₀) : E) * (Ψ y : E) *
          (Ψ (hypProj h 2 1 g₀) : E)⁻¹) * fb⁻¹) * (Ψ (hypProj h 2 1 g₀) : E) := by
        group
    _ = (Ψ (hypProj h 2 1 g₀) : E)⁻¹ * ((Ψ (hypProj h 2 1 g₀) : E) *
          (Ψ (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y) : E) *
          (Ψ (hypProj h 2 1 g₀) : E)⁻¹) * (Ψ (hypProj h 2 1 g₀) : E) := by
        rw [e1]
    _ = (Ψ (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y) : E) := by group

end FrobConj5

section Witness

@[expose] def burnsideF4m_u5v : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 :=
  !![1, 0, 0, 0, 1; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def burnsideF4m_u5t : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 1]

@[expose] def burnsideF4m_u5x : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 :=
  !![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

theorem burnsideF4m_u5_sp_gram_v :
    ((burnsideF4m_u5X burnsideF4m_u5v).map (· ^ 2))ᵀ * hypGram 2 1 CFSG.Fischer.F4 *
      burnsideF4m_u5X burnsideF4m_u5v = hypGram 2 1 CFSG.Fischer.F4 := by
  decide

theorem burnsideF4m_u5_sp_gram_t :
    ((burnsideF4m_u5X burnsideF4m_u5t).map (· ^ 2))ᵀ * hypGram 2 1 CFSG.Fischer.F4 *
      burnsideF4m_u5X burnsideF4m_u5t = hypGram 2 1 CFSG.Fischer.F4 := by
  decide

theorem burnsideF4m_u5_sp_gram_x :
    ((burnsideF4m_u5X burnsideF4m_u5x).map (· ^ 2))ᵀ * hypGram 2 1 CFSG.Fischer.F4 *
      burnsideF4m_u5X burnsideF4m_u5x = hypGram 2 1 CFSG.Fischer.F4 := by
  decide

theorem burnsideF4m_u5_sp_rel_v :
    burnsideF4m_u5X burnsideF4m_u5v * burnsideF4m_u5X burnsideF4m_u5v = 1 := by
  decide

theorem burnsideF4m_u5_sp_rel_x :
    burnsideF4m_u5X burnsideF4m_u5x * burnsideF4m_u5X burnsideF4m_u5x = 1 := by
  decide

theorem burnsideF4m_u5_sp_rel_t :
    burnsideF4m_u5X burnsideF4m_u5t * burnsideF4m_u5X burnsideF4m_u5t *
      burnsideF4m_u5X burnsideF4m_u5t = 1 := by
  decide

theorem burnsideF4m_u5_sp_rel2 :
    burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5t *
        burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5t *
          burnsideF4m_u5X burnsideF4m_u5t)) =
      burnsideF4m_u5X burnsideF4m_u5t * burnsideF4m_u5X burnsideF4m_u5v *
        (burnsideF4m_u5X burnsideF4m_u5t * burnsideF4m_u5X burnsideF4m_u5t) *
        burnsideF4m_u5X burnsideF4m_u5v := by
  decide

theorem burnsideF4m_u5_sp_rel3 :
    burnsideF4m_u5X burnsideF4m_u5t * (burnsideF4m_u5X burnsideF4m_u5t *
        burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5t *
          burnsideF4m_u5X burnsideF4m_u5t)) *
        (burnsideF4m_u5X burnsideF4m_u5t * burnsideF4m_u5X burnsideF4m_u5t) =
      burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5t *
        burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5t *
          burnsideF4m_u5X burnsideF4m_u5t)) := by
  decide +kernel

theorem burnsideF4m_u5_sp_rel4 :
    burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5x *
        burnsideF4m_u5X burnsideF4m_u5v * burnsideF4m_u5X burnsideF4m_u5x) *
      (burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5x *
        burnsideF4m_u5X burnsideF4m_u5v * burnsideF4m_u5X burnsideF4m_u5x)) *
      (burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5x *
        burnsideF4m_u5X burnsideF4m_u5v * burnsideF4m_u5X burnsideF4m_u5x)) = 1 := by
  decide

theorem burnsideF4m_u5_sp_entry :
    (burnsideF4m_u5X burnsideF4m_u5v * (burnsideF4m_u5X burnsideF4m_u5x *
        burnsideF4m_u5X burnsideF4m_u5v * burnsideF4m_u5X burnsideF4m_u5x)) ιe₂ ιf₂ = 1 := by
  decide

theorem burnsideF4m_u5_sp_fix_v :
    (burnsideF4m_u5X burnsideF4m_u5v).map (· ^ 2) = burnsideF4m_u5X burnsideF4m_u5v := by
  decide

theorem burnsideF4m_u5_sp_fix_t :
    (burnsideF4m_u5X burnsideF4m_u5t).map (· ^ 2) = burnsideF4m_u5X burnsideF4m_u5t := by
  decide

theorem burnsideF4m_u5_sp_fix_x :
    (burnsideF4m_u5X burnsideF4m_u5x).map (· ^ 2) = burnsideF4m_u5X burnsideF4m_u5x := by
  decide

theorem burnsideF4m_u5_sp_stab_v1 :
    ∀ a : HypIndex 2 1, a ≠ ιe₁ → burnsideF4m_u5X burnsideF4m_u5v a ιe₁ = 0 := by
  decide

theorem burnsideF4m_u5_sp_stab_x1 :
    ∀ a : HypIndex 2 1, a ≠ ιe₁ → burnsideF4m_u5X burnsideF4m_u5x a ιe₁ = 0 := by
  decide

theorem burnsideF4m_u5_sp_stab_v2 (a b : HypIndex 2 1) (hb : b = ιe₁ ∨ b = ιe₂)
    (ha : a = ιz ∨ a = ιf₂ ∨ a = ιf₁) : burnsideF4m_u5X burnsideF4m_u5v a b = 0 := by
  rcases hb with rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> decide

theorem burnsideF4m_u5_sp_stab_t2 (a b : HypIndex 2 1) (hb : b = ιe₁ ∨ b = ιe₂)
    (ha : a = ιz ∨ a = ιf₂ ∨ a = ιf₁) : burnsideF4m_u5X burnsideF4m_u5t a b = 0 := by
  rcases hb with rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> decide

@[expose] def burnsideF4m_frobF4 : CFSG.Fischer.F4 →+* CFSG.Fischer.F4 where
  toFun x := x ^ 2
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem burnsideF4m_f4_sq_one : ∀ d : CFSG.Fischer.F4, d * d = 1 → d = 1 := by
  decide

theorem burnsideF4m_f4_cube_one : ∀ d : CFSG.Fischer.F4, d ^ 2 = d → d * d * d = 1 → d = 1 := by
  decide

theorem burnsideF4m_u5_sp_det :
    (burnsideF4m_u5X burnsideF4m_u5v).det = 1 ∧ (burnsideF4m_u5X burnsideF4m_u5x).det = 1 ∧
      (burnsideF4m_u5X burnsideF4m_u5t).det = 1 := by
  have hv := burnsideF4m_u5_sp_rel_v
  have hx := burnsideF4m_u5_sp_rel_x
  have ht := burnsideF4m_u5_sp_rel_t
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg Matrix.det hv
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact burnsideF4m_f4_sq_one _ this
  · have := congrArg Matrix.det hx
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact burnsideF4m_f4_sq_one _ this
  · have h3 := congrArg Matrix.det ht
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h3
    have h2 : (burnsideF4m_u5X burnsideF4m_u5t).det ^ 2 = (burnsideF4m_u5X burnsideF4m_u5t).det := by
      have := RingHom.map_det burnsideF4m_frobF4 (burnsideF4m_u5X burnsideF4m_u5t)
      have e : burnsideF4m_frobF4.mapMatrix (burnsideF4m_u5X burnsideF4m_u5t) =
          burnsideF4m_u5X burnsideF4m_u5t := burnsideF4m_u5_sp_fix_t
      rw [e] at this
      exact this
    exact burnsideF4m_f4_cube_one _ h2 h3

variable {K : Type} [Field K]

@[expose] noncomputable def burnsideF4m_u5GLi (h : UnitaryFieldData 2 1 K)
    (X Y : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4) (hXY : X * Y = 1)
    (hYX : Y * X = 1) : GL (HypIndex 2 1) K where
  val := (burnsideF4m_eF4 h).mapMatrix X
  inv := (burnsideF4m_eF4 h).mapMatrix Y
  val_inv := by rw [← map_mul, hXY, map_one]
  inv_val := by rw [← map_mul, hYX, map_one]

theorem burnsideF4m_u5GLi_mem (h : UnitaryFieldData 2 1 K)
    (X Y : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4) (hXY : X * Y = 1)
    (hYX : Y * X = 1)
    (hG : (X.map (· ^ 2))ᵀ * hypGram 2 1 CFSG.Fischer.F4 * X = hypGram 2 1 CFSG.Fischer.F4)
    (hd : X.det = 1) : burnsideF4m_u5GLi h X Y hXY hYX ∈ hypSU h 2 1 := by
  set e := burnsideF4m_eF4 h with he
  have hg : ((burnsideF4m_u5GLi h X Y hXY hYX : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = e.mapMatrix X := rfl
  have hbar : ((burnsideF4m_u5GLi h X Y hXY hYX : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K).map h.bar = e.mapMatrix (X.map (· ^ 2)) := by
    rw [hg]
    ext a b
    simp [RingHom.mapMatrix_apply, h.bar_apply]
  have hJ : hypGram 2 1 K = e.mapMatrix (hypGram 2 1 CFSG.Fischer.F4) := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hypGram_apply]
    split_ifs <;> simp
  refine mem_hypSU.mpr ⟨?_, ?_⟩
  · rw [hbar, hJ, hg]
    have ht : (e.mapMatrix (X.map (· ^ 2)))ᵀ = e.mapMatrix ((X.map (· ^ 2))ᵀ) := by
      simp only [RingHom.mapMatrix_apply, Matrix.transpose_map]
    rw [ht, ← map_mul, ← map_mul, hG]
  · rw [hg, ← RingHom.map_det, hd, map_one]

@[expose] noncomputable def burnsideF4m_u5elti (h : UnitaryFieldData 2 1 K)
    (X Y : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4) (hXY : X * Y = 1)
    (hYX : Y * X = 1)
    (hG : (X.map (· ^ 2))ᵀ * hypGram 2 1 CFSG.Fischer.F4 * X = hypGram 2 1 CFSG.Fischer.F4)
    (hd : X.det = 1) : hypSU h 2 1 :=
  ⟨burnsideF4m_u5GLi h X Y hXY hYX, burnsideF4m_u5GLi_mem h X Y hXY hYX hG hd⟩

theorem burnsideF4m_u5_sp_witness (h : UnitaryFieldData 2 1 K) :
    ∃ v t x : hypSU h 2 1, (v ∈ u5PtStab h ∧ v ∈ u5LnStab h) ∧ t ∈ u5LnStab h ∧
      x ∈ u5PtStab h ∧
      fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) v = v ∧
      fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) t = t ∧
      fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) x = x ∧
      v * v = 1 ∧ t ^ 3 = 1 ∧ v * (t * v * t⁻¹) = t * v * t⁻¹ * v ∧
      t * (t * v * t⁻¹) * t⁻¹ = v * (t * v * t⁻¹) ∧ (v * (x * v * x⁻¹)) ^ 3 = 1 ∧
      v * (x * v * x⁻¹) ≠ 1 := by
  have gv := burnsideF4m_u5_sp_gram_v
  have gt := burnsideF4m_u5_sp_gram_t
  have gx := burnsideF4m_u5_sp_gram_x
  have rv := burnsideF4m_u5_sp_rel_v
  have rx := burnsideF4m_u5_sp_rel_x
  have rt := burnsideF4m_u5_sp_rel_t
  obtain ⟨dv, dx, dt⟩ := burnsideF4m_u5_sp_det
  have fv := burnsideF4m_u5_sp_fix_v
  have ft := burnsideF4m_u5_sp_fix_t
  have fx := burnsideF4m_u5_sp_fix_x
  have sv1 := burnsideF4m_u5_sp_stab_v1
  have sx1 := burnsideF4m_u5_sp_stab_x1
  have sv2 := burnsideF4m_u5_sp_stab_v2
  have st2 := burnsideF4m_u5_sp_stab_t2
  have rt' : burnsideF4m_u5X burnsideF4m_u5t *
      (burnsideF4m_u5X burnsideF4m_u5t * burnsideF4m_u5X burnsideF4m_u5t) = 1 := by
    rw [← Matrix.mul_assoc, rt]
  have rt'' : burnsideF4m_u5X burnsideF4m_u5t * burnsideF4m_u5X burnsideF4m_u5t *
      burnsideF4m_u5X burnsideF4m_u5t = 1 := rt
  set e := burnsideF4m_eF4 h with he
  set v := burnsideF4m_u5elti h _ _ rv rv gv dv with hv
  set x := burnsideF4m_u5elti h _ _ rx rx gx dx with hx
  set t := burnsideF4m_u5elti h _ _ rt' rt'' gt dt with ht
  have hmv : mat v = e.mapMatrix (burnsideF4m_u5X burnsideF4m_u5v) := rfl
  have hmx : mat x = e.mapMatrix (burnsideF4m_u5X burnsideF4m_u5x) := rfl
  have hmt : mat t = e.mapMatrix (burnsideF4m_u5X burnsideF4m_u5t) := rfl
  have hvv : v * v = 1 := mat_injective (by rw [mat_mul, mat_one, hmv, ← map_mul, rv, map_one])
  have hxx : x * x = 1 := mat_injective (by rw [mat_mul, mat_one, hmx, ← map_mul, rx, map_one])
  have httt : t * t * t = 1 :=
    mat_injective (by rw [mat_mul, mat_mul, mat_one, hmt, ← map_mul, ← map_mul, rt, map_one])
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hti : t⁻¹ = t * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, httt])
  have hfix : ∀ (g : hypSU h 2 1) (X : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4),
      mat g = e.mapMatrix X → X.map (· ^ 2) = X →
        fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) g = g := by
    intro g X hg hX
    apply mat_injective
    rw [CFSG.Quasithin.H13.F431.Un.mat_fieldAut, hg]
    conv_rhs => rw [← hX]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      CFSG.Quasithin.H13.F431.Un.OL5.fld5_bar_apply, h.bar_apply, map_pow, pow_one]
  have hpt : ∀ (g : hypSU h 2 1) (X : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4),
      mat g = e.mapMatrix X → (∀ a : HypIndex 2 1, a ≠ ιe₁ → X a ιe₁ = 0) → g ∈ u5PtStab h := by
    intro g X hg hX
    rw [mem_u5PtStab_iff]
    intro a ha
    rw [hg, RingHom.mapMatrix_apply, Matrix.map_apply, hX a ha, map_zero]
  have hln : ∀ (g : hypSU h 2 1) (X : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4),
      mat g = e.mapMatrix X → (∀ a b : HypIndex 2 1, (b = ιe₁ ∨ b = ιe₂) →
        (a = ιz ∨ a = ιf₂ ∨ a = ιf₁) → X a b = 0) → g ∈ u5LnStab h := by
    intro g X hg hX
    rw [mem_u5LnStab_iff]
    intro a b hb ha
    rw [hg, RingHom.mapMatrix_apply, Matrix.map_apply, hX a b hb ha, map_zero]
  refine ⟨v, t, x, ⟨hpt v _ hmv sv1, hln v _ hmv sv2⟩, hln t _ hmt st2, hpt x _ hmx sx1,
    hfix v _ hmv fv, hfix t _ hmt ft, hfix x _ hmx fx, hvv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_three, ← mul_assoc, httt]
  · rw [hti]
    apply mat_injective
    simp only [mat_mul, hmv, hmt, ← map_mul]
    rw [burnsideF4m_u5_sp_rel2]
  · rw [hti]
    apply mat_injective
    simp only [mat_mul, hmv, hmt, ← map_mul]
    rw [burnsideF4m_u5_sp_rel3]
  · rw [hxi, pow_three]
    apply mat_injective
    simp only [mat_mul, mat_one, hmv, hmx, ← map_mul]
    rw [← Matrix.mul_assoc, burnsideF4m_u5_sp_rel4, map_one]
  · rw [hxi]
    intro h1
    have h2 := congrArg (fun g : hypSU h 2 1 => mat g ιe₂ ιf₂) h1
    simp only [mat_mul, mat_one, hmv, hmx, ← map_mul] at h2
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, burnsideF4m_u5_sp_entry, map_one] at h2
    have h3 : (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) ιe₂ ιf₂ = 0 := by
      rw [Matrix.one_apply_ne (by decide)]
    rw [h3] at h2
    exact one_ne_zero h2

end Witness

end CFSG.ASVolI
