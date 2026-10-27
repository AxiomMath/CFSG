module

public import CFSG.Milestones.ASVolI.F431.BCoreU4Q
public import CFSG.Milestones.ASVolI.F431.BF436Sp
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Quasithin.H13.U4Par CFSG.ASVolI.ChF.ClassicalRoots CFSG.QuasithinUnique.Setup.X7a

section GraphData

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_u4_graph_data (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) {fb : E}
    (hg : hyp.chart.IsGraphInv fb) :
    ∃ (mk : Marking .U4 2 1 ↥Gp) (conj : MulAut ↥Gp) (sigma : mk.field →+* mk.field),
      (∀ p, sigma p = p ^ (2 ^ 1)) ∧
      Gp ⊓ M₁ = (mk.parabolic false).map Gp.subtype ∧
      Gp ⊓ M₂ = (mk.parabolic true).map Gp.subtype ∧
      ∀ A : nativeGroup .U4 (2 ^ 1) mk.field, ∃ B : nativeGroup .U4 (2 ^ 1) mk.field,
        (B : GL (Coord .U4) mk.field) =
            mk.basis * Matrix.GeneralLinearGroup.map sigma
              (mk.basis⁻¹ * (A : GL (Coord .U4) mk.field) * mk.basis) * mk.basis⁻¹ ∧
          ((conj (mk.transport B) : ↥Gp) : E) =
            fb * ((conj (mk.transport A) : ↥Gp) : E) * fb⁻¹ := by
  obtain ⟨-, -, -, conj, -, hpure⟩ := hg
  have hfits := hyp.chart.coordinatePayload_fits
  have hm := hyp.chart_matches
  generalize hcp : hyp.chart.coordinatePayload = cp at hpure hfits
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .U4 := by
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

end GraphData

section Transport

theorem burnsideF4m_matrix_frob {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (Bm Bi : Matrix (Fin 4) (Fin 4) K) (hBiBm : Bi * Bm = 1)
    (P : Matrix (Fin 4) ι K) (Q : Matrix ι (Fin 4) K) (hPs : P.map σ = P) (hQs : Q.map σ = Q)
    (g : Matrix ι ι K) :
    Bm * (Bi * (Bm * P * g * (Q * Bi)) * Bm).map σ * Bi = Bm * P * g.map σ * (Q * Bi) := by
  have e1 : Bi * (Bm * P * g * (Q * Bi)) * Bm = P * g * Q := by
    rw [show Bi * (Bm * P * g * (Q * Bi)) * Bm = (Bi * Bm) * P * g * Q * (Bi * Bm) by
      simp only [Matrix.mul_assoc], hBiBm, Matrix.one_mul, Matrix.mul_one]
  rw [e1, Matrix.map_mul, Matrix.map_mul, hPs, hQs]
  simp only [Matrix.mul_assoc]

variable {H : Type} [Group H] (mk : Marking .U4 2 1 H)

theorem burnsideF4m_u4_T_frob (sigma : mk.field →+* mk.field) (hsig : ∀ p, sigma p = p ^ (2 ^ 1))
    (g : hypSU (burnsideF4gU4_fieldData mk) 2 0) :
    mk.basis * Matrix.GeneralLinearGroup.map sigma
        (mk.basis⁻¹ * ((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ 1) mk.field) :
          GL (Coord .U4) mk.field) * mk.basis) * mk.basis⁻¹ =
      ((burnsideF4gU4_T mk (frobElt (burnsideF4gU4_fieldData mk) g) :
        nativeGroup .U4 (2 ^ 1) mk.field) : GL (Coord .U4) mk.field) := by
  have hBiBm : ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) *
      (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBmBi : (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
      ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hR := burnsideF4gU4_marking_isHypTransport mk
  have h1 := transportInv_mul hR
  have hRP : burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) =
      (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
        (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv := by
    ext i a
    simp only [burnsideF4gU4_R, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.one_apply, id,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hPQ : (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv *
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]
    ext i j
    simp [Matrix.one_apply]
  have hRinv : transportInv (burnsideF4gU4_fieldData mk)
      (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)) =
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id *
        ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) := by
    set Rinv := transportInv (burnsideF4gU4_fieldData mk)
      (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field))
    have hq : Rinv * (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) =
        (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id := by
      calc Rinv * (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)
          = Rinv * (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
              ((1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv *
                (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id) := by
            rw [hPQ, Matrix.mul_one]
        _ = Rinv * ((mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
              (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv) *
              (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hRP, h1, Matrix.one_mul]
    calc Rinv = Rinv * ((mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
          ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field)) := by
          rw [hBmBi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hq]
  have hPs : ((1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv).map sigma =
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv := by
    ext i a
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hQs : ((1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id).map sigma =
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id := by
    ext a i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hbar : ((g : GL (HypIndex 2 0) mk.field) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field).map sigma =
      ((g : GL (HypIndex 2 0) mk.field) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field).map (burnsideF4gU4_fieldData mk).bar := by
    ext a b
    simp only [Matrix.map_apply, hsig, (burnsideF4gU4_fieldData mk).bar_apply]
  apply Units.ext
  have hT := burnsideF4gU4_coe_T mk g
  have hT' := burnsideF4gU4_coe_T mk (frobElt (burnsideF4gU4_fieldData mk) g)
  rw [coe_frobElt, ← hbar, hRinv, hRP] at hT'
  rw [hRinv, hRP] at hT
  change (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
      ((((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) *
        (((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ 1) mk.field) : GL (Coord .U4) mk.field) :
          Matrix (Fin 4) (Fin 4) mk.field) *
        (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)).map sigma) *
      ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) = _
  rw [hT, hT']
  exact burnsideF4m_matrix_frob sigma _ _ hBiBm _ _ hPs hQs _

end Transport

section FrobConj

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_u4_fb_acts (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) {fb : E}
    (hg : hyp.chart.IsGraphInv fb) :
    ∃ (mk : Marking .U4 2 1 ↥Gp) (conj : MulAut ↥Gp),
      Gp ⊓ M₁ = (parP (burnsideF4gU4_fieldData mk)).map
        (Gp.subtype.comp (burnsideF4gU4_Phi mk).toMonoidHom) ∧
      Gp ⊓ M₂ = (parP2 (burnsideF4gU4_fieldData mk)).map
        (Gp.subtype.comp (burnsideF4gU4_Phi mk).toMonoidHom) ∧
      ∀ g : hypSU (burnsideF4gU4_fieldData mk) 2 0,
        ((conj (burnsideF4gU4_Phi mk (frobElt (burnsideF4gU4_fieldData mk) g)) : ↥Gp) : E) =
          fb * ((conj (burnsideF4gU4_Phi mk g) : ↥Gp) : E) * fb⁻¹ := by
  obtain ⟨mk, conj, sigma, hsig, h1, h2, hrep⟩ := burnsideF4m_u4_graph_data hyp hg
  have hPhi : ∀ g, burnsideF4gU4_Phi mk g = mk.transport (burnsideF4gU4_T mk g) := fun g =>
    congrArg (fun φ : hypSU (burnsideF4gU4_fieldData mk) 2 0 →* ↥Gp => φ g)
      (burnsideF4gU4_Phi_toMonoidHom mk)
  refine ⟨mk, conj, ?_, ?_, fun g => ?_⟩
  · rw [h1, ← Subgroup.map_map]
    congr 1
    show (nativeParabolic .U4 (2 ^ 1) mk.field mk.basis false).map mk.transport = _
    rw [burnsideF4gU4_parabolic_false, Subgroup.map_map, burnsideF4gU4_Phi_toMonoidHom]
  · rw [h2, ← Subgroup.map_map]
    congr 1
    show (nativeParabolic .U4 (2 ^ 1) mk.field mk.basis true).map mk.transport = _
    rw [burnsideF4gU4_parabolic_true, Subgroup.map_map, burnsideF4gU4_Phi_toMonoidHom]
  · obtain ⟨B, hB, hBA⟩ := hrep (burnsideF4gU4_T mk g)
    have hBeq : B = burnsideF4gU4_T mk (frobElt (burnsideF4gU4_fieldData mk) g) :=
      Subtype.ext (hB.trans (burnsideF4m_u4_T_frob mk sigma hsig g))
    rw [hPhi, hPhi, ← hBeq]
    exact hBA

theorem burnsideF4m_u4_fieldElt_frob {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (τ : K ≃+* K) (g : hypSU h 2 0) :
    burnsideF4m_U4_fieldAut h τ (frobElt h g) = frobElt h (burnsideF4m_U4_fieldAut h τ g) := by
  apply hypSU_ext h
  change (((burnsideF4m_U4_fieldElt h τ (frobElt h g) : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
    (((frobElt h (burnsideF4m_U4_fieldElt h τ g) : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)
  rw [burnsideF4m_U4_coe_fieldElt, coe_glAut, coe_frobElt, coe_frobElt,
    burnsideF4m_U4_coe_fieldElt, coe_glAut]
  ext a b
  simp only [Matrix.map_apply, h.bar_apply, map_pow]

theorem burnsideF4m_u4_exists_frob_conj (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) {fb : E}
    (hg : hyp.chart.IsGraphInv fb) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 1 K) (Φ : hypSU h 2 0 ≃* ↥Gp) (a : ↥Gp),
      Gp ⊓ M₁ = (parP h).map (Gp.subtype.comp Φ.toMonoidHom) ∧
      Gp ⊓ M₂ = (parP2 h).map (Gp.subtype.comp Φ.toMonoidHom) ∧
      ∀ g : hypSU h 2 0, ((a : E)⁻¹ * fb * a) * (Φ g : E) * ((a : E)⁻¹ * fb * a)⁻¹ =
        (Φ (frobElt h g) : E) := by
  obtain ⟨mk, conj, h1, h2, hact⟩ := burnsideF4m_u4_fb_acts hyp hg
  set h := burnsideF4gU4_fieldData mk with hh
  set Φ := burnsideF4gU4_Phi mk with hΦ
  obtain ⟨a₀, τ, hδ⟩ := burnsideF4m_U4_normalForm h ((Φ.trans conj).trans Φ.symm)
  have hδg : ∀ g, conj (Φ g) = Φ (a₀ * burnsideF4m_U4_fieldAut h τ g * a₀⁻¹) := by
    intro g
    have := congrArg (fun α : MulAut (hypSU h 2 0) => α g) hδ
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.conj_apply] at this
    rw [← this, MulEquiv.apply_symm_apply]
  refine ⟨mk.field, inferInstance, h, Φ, Φ a₀, h1, h2, fun y => ?_⟩
  set g := (burnsideF4m_U4_fieldAut h τ).symm y with hgdef
  have hgy : burnsideF4m_U4_fieldAut h τ g = y := (burnsideF4m_U4_fieldAut h τ).apply_symm_apply y
  have e1 := hact g
  rw [hδg, hδg, burnsideF4m_u4_fieldElt_frob, hgy] at e1
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at e1
  calc ((Φ a₀ : E))⁻¹ * fb * (Φ a₀ : E) * (Φ y : E) * ((Φ a₀ : E)⁻¹ * fb * (Φ a₀ : E))⁻¹
      = (Φ a₀ : E)⁻¹ * (fb * ((Φ a₀ : E) * (Φ y : E) * (Φ a₀ : E)⁻¹) * fb⁻¹) * (Φ a₀ : E) := by
        group
    _ = (Φ a₀ : E)⁻¹ * ((Φ a₀ : E) * (Φ (frobElt h y) : E) * (Φ a₀ : E)⁻¹) * (Φ a₀ : E) := by
        rw [e1]
    _ = (Φ (frobElt h y) : E) := by group

end FrobConj

section Generic

variable {E : Type} [Group E]

theorem burnsideF4m_oTwoRes_map {A : Type} [Group A] (φ : A →* E) (hφ : Function.Injective φ)
    (X : Subgroup A) : oTwoRes (X.map φ) = (oTwoRes X).map φ := by
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, m, hm, hym⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, m, hm, hφ (by rw [map_pow, hym, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, m, hm, hxm⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ hx, m, hm, by rw [← map_pow, hxm, map_one]⟩

theorem burnsideF4m_mem_normalizer_of_act {C : Type} [Group C] {Gp : Subgroup E} [Gp.Normal]
    (φ : C →* E) (hφ : Function.Injective φ) (hrange : φ.range = Gp) {P : Subgroup C}
    {s : E} (α : C → C) (hα : ∀ g, s * φ g * s⁻¹ = φ (α g)) (hαP : ∀ g ∈ P, α g ∈ P)
    (hαα : ∀ g, α (α g) = g) : s ∈ Subgroup.normalizer ((P.map φ : Subgroup E) : Set E) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [hα]
    exact ⟨α g, hαP g hg, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    have hxG : x ∈ Gp := by
      have h1 : s * x * s⁻¹ ∈ Gp := hrange ▸ ⟨g, hgx⟩
      have h2 := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ h1 s⁻¹
      simpa [mul_assoc] using h2
    rw [← hrange] at hxG
    obtain ⟨y, rfl⟩ := hxG
    rw [hα] at hgx
    have hgy : g = α y := hφ hgx
    refine ⟨y, ?_, rfl⟩
    rw [← hαα y, ← hgy]
    exact hαP g hg

theorem burnsideF4m_V_conj {A B : Subgroup E} {s : E} (c : E)
    (hcA : c ∈ Subgroup.normalizer (A : Set E)) (hcB : c ∈ Subgroup.normalizer (B : Set E))
    (hV : pCoreOf 2 (oTwoRes (cenIn A s)) ≤ cenIn B s ∧
      ¬ pCoreOf 2 (oTwoRes (cenIn A s)) ≤ pCoreOf 2 (cenIn B s)) :
    pCoreOf 2 (oTwoRes (cenIn A (c⁻¹ * s * c))) ≤ cenIn B (c⁻¹ * s * c) ∧
      ¬ pCoreOf 2 (oTwoRes (cenIn A (c⁻¹ * s * c))) ≤ pCoreOf 2 (cenIn B (c⁻¹ * s * c)) := by
  set φ : E →* E := (MulAut.conj c⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj c⁻¹).injective
  have hcen : ∀ {X : Subgroup E}, c ∈ Subgroup.normalizer (X : Set E) →
      cenIn X (c⁻¹ * s * c) = (cenIn X s).map φ := by
    intro X hcX
    ext y
    constructor
    · intro hy
      obtain ⟨hyX, hys⟩ := Subgroup.mem_inf.mp hy
      refine ⟨c * y * c⁻¹, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hcX y).mp hyX, ?_⟩,
        ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hys ⊢
        calc c * y * c⁻¹ * s = c * (y * (c⁻¹ * s * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * s * c) * y) * c⁻¹ := by rw [hys]
          _ = s * (c * y * c⁻¹) := by group
      · simp [hφ, MulAut.conj_apply, mul_assoc]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzX, hzs⟩ := Subgroup.mem_inf.mp hz
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcX) z).mp hzX
        simpa [hφ, MulAut.conj_apply] using this
      · rw [Subgroup.mem_centralizer_singleton_iff] at hzs ⊢
        simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        calc c⁻¹ * z * c * (c⁻¹ * s * c) = c⁻¹ * (z * s) * c := by group
          _ = c⁻¹ * (s * z) * c := by rw [hzs]
          _ = c⁻¹ * s * c * (c⁻¹ * z * c) := by group
  rw [hcen hcA, hcen hcB, burnsideF4m_oTwoRes_map φ hφinj,
    CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφinj,
    CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφinj,
    Subgroup.map_le_map_iff_of_injective hφinj, Subgroup.map_le_map_iff_of_injective hφinj]
  exact hV

end Generic

section LineSp

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF4m_ixEF_vals : ixEF ie2 = (Sum.inl 1 : Fin 2 ⊕ Fin 2) ∧
    ixEF if1 = (Sum.inr 0 : Fin 2 ⊕ Fin 2) ∧ ixEF if2 = (Sum.inr 1 : Fin 2 ⊕ Fin 2) := by
  refine ⟨by decide, by decide, by decide⟩

theorem burnsideF4m_spIncl_mem_parP2_iff (A : StatedSp 2 h.fixedField) :
    spIncl h A ∈ parP2 h ↔ ∀ i j, burnsideF4m_spM A (Sum.inr i) (Sum.inl j) = 0 := by
  obtain ⟨h2, h3, h4⟩ := burnsideF4m_ixEF_vals
  rw [mem_parP2_iff, coe_spIncl, inclMat_apply, inclMat_apply, inclMat_apply, inclMat_apply,
    ixEF_ie1, h2, h3, h4]
  constructor
  · rintro ⟨a1, a2, a3, a4⟩ i j
    fin_cases i <;> fin_cases j
    · exact Subtype.ext a1
    · exact Subtype.ext a2
    · exact Subtype.ext a3
    · exact Subtype.ext a4
  · intro hA
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hA]

theorem burnsideF4m_map_spIncl_Q2_one : (Q2 h.fixedField 1).map (spIncl h) = parP2 h ⊓ frobFix h := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨(burnsideF4m_spIncl_mem_parP2_iff h A).mpr (burnsideF4m_spQ1_bl hA),
      range_spIncl h ▸ ⟨A, rfl⟩⟩
  · rintro g ⟨hgP, hgF⟩
    rw [← range_spIncl h] at hgF
    obtain ⟨A, rfl⟩ := hgF
    refine ⟨A, burnsideF4m_spQ1_of_bl ((burnsideF4m_spIncl_mem_parP2_iff h A).mp hgP) ?_, rfl⟩
    have hinv : spIncl h A⁻¹ ∈ parP2 h := by
      rw [map_inv]
      exact (parP2 h).inv_mem hgP
    exact (burnsideF4m_spIncl_mem_parP2_iff h A⁻¹).mp hinv

end LineSp

section Conj2

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_f436_U4_V (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) :
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
      ∀ fb ∈ Tb, hyp.toHypF_4_4g.chart.IsGraphInv fb →
        ∃ r ∈ Tb, (∃ g : E, g * fb * g⁻¹ = r) ∧
          ((pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₁) r)) ≤ cenIn (Gp ⊓ M₂) r ∧
              ¬ pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₁) r)) ≤ pCoreOf 2 (cenIn (Gp ⊓ M₂) r)) ∨
            (pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₂) r)) ≤ cenIn (Gp ⊓ M₁) r ∧
              ¬ pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₂) r)) ≤ pCoreOf 2 (cenIn (Gp ⊓ M₁) r))) := by
  intro Tb hTb fb hfbT hgr
  haveI := hyp.finite
  haveI := hyp.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfb2 : fb * fb = 1 := hgr.2.1
  obtain ⟨K, fK, h, Φ, a, h1, h2, hs⟩ := burnsideF4m_u4_exists_frob_conj hyp.toHypF_4_4g hgr
  set s : E := (a : E)⁻¹ * fb * a with hsdef
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hrange : φ.range = Gp := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hsφ : ∀ g, s * φ g * s⁻¹ = φ (frobElt h g) := hs
  have hff : ∀ g, frobElt h (frobElt h g) = g := frobElt_frobElt h
  have hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₁ ⊓ M₂, e = n * k := fun e => by
    obtain ⟨n, hn, k, hk, he⟩ := hyp.split e
    exact ⟨n, hn, k, hk, he⟩
  have hsM1 : s ∈ M₁ := by
    have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := parP h) (frobElt h) hsφ
      (fun g hg => frobElt_mem_parP h hg) hff
    rw [← h1] at hN
    have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₂ ⊓ M₁, e = n * k := fun e => by
      obtain ⟨n, hn, k, hk, he⟩ := hsplit e
      exact ⟨n, hn, k, ⟨hk.2, hk.1⟩, he⟩
    exact burnsideF4m_normalizer_inf_le (M₁ := M₂) hsplit' φ hφ hrange h1
      (fun g hg => burnsideF4d_selfNorm (isYAmalgamPair_parP_parP2 h) g
        (Subgroup.mem_normalizer_iff.mp hg)) hN
  have hsM2 : s ∈ M₂ := by
    have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := parP2 h) (frobElt h) hsφ
      (fun g hg => frobElt_mem_parP2 h hg) hff
    rw [← h2] at hN
    exact burnsideF4m_normalizer_inf_le (M₁ := M₁) hsplit φ hφ hrange h2
      (burnsideF4m_U4_parP2_selfNorm h) hN
  have hs2 : s ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hsdef]
    calc (a : E)⁻¹ * fb * a * ((a : E)⁻¹ * fb * a) = (a : E)⁻¹ * (fb * fb) * a := by group
      _ = 1 := by rw [hfb2]; group
  have hTb' : CFSG.QuasithinUnique.IsSylowTwoOf Tb (M₁ ⊓ M₂) := hTb
  obtain ⟨c, hc, hle⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hTb'
    ((Subgroup.zpowers_le (H := M₁ ⊓ M₂)).mpr ⟨hsM1, hsM2⟩)
    (CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hs2)
  have hsc : s ∈ CFSG.Quasithin.conjSub c Tb := hle (Subgroup.mem_zpowers s)
  rw [CFSG.Quasithin.mem_conjSub] at hsc
  refine ⟨c⁻¹ * s * c, hsc, ⟨c⁻¹ * (a : E)⁻¹, by rw [hsdef]; group⟩, Or.inr ?_⟩
  have hcN : ∀ {M : Subgroup E}, c ∈ M → c ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) :=
    fun hcM => burnsideF4m_mem_normalizer_inf (Gp := Gp) hcM
  refine burnsideF4m_V_conj c (hcN hc.2) (hcN hc.1) ?_
  set θ : StatedSp 2 h.fixedField →* E := φ.comp (spIncl h) with hθ
  have hθinj : Function.Injective θ := hφ.comp (spIncl_injective h)
  have hX : ∀ {M : Subgroup E} {P : Subgroup (hypSU h 2 0)}, Gp ⊓ M = P.map φ →
      cenIn (Gp ⊓ M) s = (P ⊓ frobFix h).map φ := by
    intro M P hMP
    ext x
    constructor
    · intro hx
      obtain ⟨hxM, hxs⟩ := Subgroup.mem_inf.mp hx
      rw [hMP] at hxM
      obtain ⟨g, hg, rfl⟩ := hxM
      refine ⟨g, Subgroup.mem_inf.mpr ⟨hg, ?_⟩, rfl⟩
      rw [mem_frobFix]
      apply hφ
      rw [← hsφ]
      rw [Subgroup.mem_centralizer_singleton_iff] at hxs
      rw [← hxs, mul_inv_cancel_right]
    · rintro ⟨g, hg', rfl⟩
      obtain ⟨hg, hgF⟩ := Subgroup.mem_inf.mp hg'
      refine Subgroup.mem_inf.mpr ⟨hMP ▸ ⟨g, hg, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hsφ g
      rw [(mem_frobFix h).mp hgF] at this
      calc φ g * s = s * φ g * s⁻¹ * s := by rw [this]
        _ = s * φ g := by group
  have hX1 : cenIn (Gp ⊓ M₁) s = (Q2 h.fixedField 0).map θ := by
    rw [hX h1, ← map_spIncl_Q2, Subgroup.map_map]
  have hX2 : cenIn (Gp ⊓ M₂) s = (Q2 h.fixedField 1).map θ := by
    rw [hX h2, ← burnsideF4m_map_spIncl_Q2_one, Subgroup.map_map]
  have hF2 : Nat.card h.fixedField = 2 := by rw [h.card_fixedField, pow_one]
  obtain ⟨hV1, hV2⟩ := burnsideF4m_sp2_V hF2
  rw [hX1, hX2, burnsideF4m_oTwoRes_map θ hθinj, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hθinj,
    CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hθinj,
    Subgroup.map_le_map_iff_of_injective hθinj, Subgroup.map_le_map_iff_of_injective hθinj]
  exact ⟨hV1, hV2⟩

end Conj2

end CFSG.ASVolI
