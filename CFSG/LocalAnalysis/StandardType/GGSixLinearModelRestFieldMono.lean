module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestFieldBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinModel

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem map_diagGL_eq {σ : F ≃+* F} {d : Fin (m + 1) → Fˣ} (h : ∀ i, σ (d i : F) = d i) :
    GeneralLinearGroup.map (σ : F →+* F) (InnerDiagA.diagGL d) = InnerDiagA.diagGL d := by
  apply Units.ext
  rw [coe_map_diagGL, InnerDiagA.coe_diagGL]
  congr 1
  funext i
  exact h i

variable (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
  (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)

include hker hC in
theorem conj_mem_ggInducedPairs_of_autOf {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) {A : GL (Fin (m + 1)) F} {σ : F ≃+* F}
    (hα : autOf hker hC ⟨y, hy⟩ = conjAut (m + 1) F A * fieldAut (m + 1) F σ)
    {b : G} {X : GL (Fin (m + 1)) F} (hb : (b, X) ∈ LinFusion.ggInducedPairs ψ)
    (hσX : GeneralLinearGroup.map (σ : F →+* F) X = X) :
    (y * b * y⁻¹, A * X * A⁻¹) ∈ LinFusion.ggInducedPairs ψ := by
  have hbN := mem_normalizer_of_mem_ggInducedPairs hb
  have hN : y * b * y⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hbN) (Subgroup.inv_mem _ hy)
  apply (autOf_eq_conjAut_iff hker hC hN _).mp
  have h1 : autOf hker hC ⟨y * b * y⁻¹, hN⟩ =
      autOf hker hC ⟨y, hy⟩ * autOf hker hC ⟨b, hbN⟩ * (autOf hker hC ⟨y, hy⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have key : fieldAut (m + 1) F σ * conjAut (m + 1) F X * (fieldAut (m + 1) F σ)⁻¹ =
      conjAut (m + 1) F X := by
    rw [(standard_automorphism_transport (K := F) (n := m + 1)).2.2.1, hσX]
  rw [h1, hα, (autOf_eq_conjAut_iff hker hC hbN X).mpr hb, map_mul, map_mul, map_inv]
  conv_rhs => rw [← key]
  group

theorem eq_of_ne_zero_of_mul_diagGL {A : GL (Fin (m + 1)) F} {ω : Fˣ} (hω1 : ω ≠ 1)
    (h : ∀ l : Fin (m + 1), ∃ (κ : Fˣ) (d : Fin (m + 1) → Fˣ),
      A * InnerDiagA.diagGL d =
        InnerDiagA.diagGL (fun k => κ * (Pi.mulSingle l ω : Fin (m + 1) → Fˣ) k) * A)
    {i l l' : Fin (m + 1)} (hl : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l i ≠ 0)
    (hl' : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l' i ≠ 0) : l = l' := by
  by_contra hne
  obtain ⟨κ, d, h2⟩ := h l
  have h3 := congrArg (fun X : GL (Fin (m + 1)) F => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    h2
  simp only [Units.val_mul, InnerDiagA.coe_diagGL] at h3
  have hli := congrFun (congrFun h3 l) i
  have hl'i := congrFun (congrFun h3 l') i
  rw [mul_diagonal, diagonal_mul, Pi.mulSingle_eq_same] at hli
  rw [mul_diagonal, diagonal_mul, Pi.mulSingle_eq_of_ne (Ne.symm hne), Units.val_one,
    mul_one] at hl'i
  have e1 : ((d i : Fˣ) : F) = (κ : F) * (ω : F) := mul_left_cancel₀ hl (by rw [hli]; ring)
  have e2 : ((d i : Fˣ) : F) = (κ : F) := mul_left_cancel₀ hl' (by rw [hl'i]; ring)
  apply hω1
  have e3 : (κ : F) * (ω : F) = (κ : F) * 1 := by rw [← e1, e2, mul_one]
  exact Units.ext (by rw [mul_left_cancel₀ κ.ne_zero e3, Units.val_one])

include hker hC in
theorem exists_isPermOf_of_autOf [CharP F 2] {p : ℕ} {ω : Fˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ)
    {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs) {σ : F ≃+* F}
    (hfix : ∀ x : F, x ^ p = 1 → σ x = x) {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyN : y ∈ Subgroup.normalizer (Bs : Set G))
    {A : GL (Fin (m + 1)) F}
    (hα : autOf hker hC ⟨y, hy⟩ = conjAut (m + 1) F A * fieldAut (m + 1) F σ) :
    ∃ π, IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π := by
  refine exists_isPermOf fun i l l' hl hl' =>
    eq_of_ne_zero_of_mul_diagGL hω1 (fun l => ?_) hl hl'
  obtain ⟨g, hg⟩ := hreal l
  have hgBs : g ∈ Bs := by
    rw [← hBs]
    refine ⟨_, fun k => ?_, hg⟩
    by_cases hk : k = l
    · rw [hk, Pi.mulSingle_eq_same, hωp]
    · rw [Pi.mulSingle_eq_of_ne hk, one_pow]
  have hb : y⁻¹ * g * y ∈ Bs := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) g).mp hgBs
    rwa [inv_inv] at this
  rw [← hBs] at hb
  obtain ⟨e, he, hbe⟩ := hb
  have hσe : GeneralLinearGroup.map (σ : F →+* F) (InnerDiagA.diagGL e) = InnerDiagA.diagGL e :=
    map_diagGL_eq fun i => hfix _ (by rw [← Units.val_pow_eq_pow_val, he i, Units.val_one])
  have h1 := conj_mem_ggInducedPairs_of_autOf hker hC hy hα hbe hσe
  rw [show y * (y⁻¹ * g * y) * y⁻¹ = g by group] at h1
  obtain ⟨κ, hκ⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hg h1
  rw [scalar_mul_diagGL] at hκ
  refine ⟨κ, e, ?_⟩
  rw [← hκ]
  group

include hker hC in
theorem false_of_autOf_eq_diag_field [CharP F 2] {p : ℕ} (hm : 1 ≤ m) {Bs : Subgroup G}
    (hBs : rootTorus p ψ = Bs) (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hfix : ∀ x : F, x ^ p = 1 → σ x = x) {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyp : y ^ p = 1)
    {a : Fin (m + 1) → Fˣ}
    (hα : autOf hker hC ⟨y, hy⟩ = conjAut (m + 1) F (InnerDiagA.diagGL a) *
      fieldAut (m + 1) F σ) : False := by
  have hyC : y ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨e, he, hbe⟩ := hb
    have hσe : GeneralLinearGroup.map (σ : F →+* F) (InnerDiagA.diagGL e) =
        InnerDiagA.diagGL e :=
      map_diagGL_eq fun i => hfix _ (by rw [← Units.val_pow_eq_pow_val, he i, Units.val_one])
    have h1 := conj_mem_ggInducedPairs_of_autOf hker hC hy hα hbe hσe
    rw [LinFusion.diagGL_mul_comm a e, mul_inv_cancel_right] at h1
    have h2 := (LinFusion.ggInducedPairs ψ).mul_mem h1 ((LinFusion.ggInducedPairs ψ).inv_mem hbe)
    rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h2
    have h3 := LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h2
    rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h3
    calc b * y = y * b * y⁻¹ * y := by rw [h3]
      _ = y * b := by group
  have hyB := hom y hyC hyp
  rw [← hBs] at hyB
  obtain ⟨d, -, hyd⟩ := hyB
  have h1 := (autOf_eq_conjAut_iff hker hC hy _).mpr hyd
  rw [hα] at h1
  apply hσ1
  apply AutPSL.eq_one_of_fieldAut_mem (n := m + 1) (by omega)
  refine ⟨(InnerDiagA.diagGL a)⁻¹ * InnerDiagA.diagGL d, ?_⟩
  rw [map_mul, map_inv, ← h1]
  group

end LinModel

end CFSG.StandardType
