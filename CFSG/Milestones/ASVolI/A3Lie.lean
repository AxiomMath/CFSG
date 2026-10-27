module

public import CFSG.Milestones.ASVolI.A3
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Open.StatedDefs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

public section

namespace CFSG.ASVolI

open CFSG.Open
open CFSG.ASVolI.ChA
open scoped Pointwise MatrixGroups

noncomputable def burnsideA315h_e (F : Type) [Field F] :
    PSL(3, F) ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
  CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F

theorem burnsideA315h_e_mk (F : Type) [Field F] (s : SL(3, F)) :
    burnsideA315h_e F (QuotientGroup.mk s) = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s := by
  unfold burnsideA315h_e
  exact QuotientGroup.quotientMulEquivOfEq_mk _ s

theorem burnsideA315h_e_symm_proj (F : Type) [Field F] (s : SL(3, F)) :
    (burnsideA315h_e F).symm (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) =
      QuotientGroup.mk s := by
  rw [MulEquiv.symm_apply_eq, burnsideA315h_e_mk]

theorem burnsideA315h_pslOfSL_mk {F : Type} [Field F] (e : SL(3, F) ≃* SL(3, F)) (s : SL(3, F)) :
    pslOfSL e (QuotientGroup.mk s) = QuotientGroup.mk (e s) :=
  QuotientGroup.congr_mk' _ _ _ _ s

noncomputable def burnsideA315h_Phi (F : Type) [Field F] :
    MulAut PSL(3, F) ≃* MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
  MulAut.congr (burnsideA315h_e F)

theorem burnsideA315h_Phi_apply_proj (F : Type) [Field F] (α : MulAut PSL(3, F)) (s : SL(3, F)) :
    burnsideA315h_Phi F α (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) =
      burnsideA315h_e F (α (QuotientGroup.mk s)) := by
  unfold burnsideA315h_Phi
  show burnsideA315h_e F (α ((burnsideA315h_e F).symm _)) = _
  rw [burnsideA315h_e_symm_proj]

theorem burnsideA315h_Phi_diag (F : Type) [Field F] (g : GL (Fin 3) F) :
    burnsideA315h_Phi F (psl3DiagAut g) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F g := by
  ext x
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  rw [burnsideA315h_Phi_apply_proj, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
  unfold psl3DiagAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_e_mk]
  have h : slConj g s = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      3 F g s := by
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl
  rw [h]

theorem burnsideA315h_Phi_field (F : Type) [Field F] (σ : RingAut F) :
    burnsideA315h_Phi F (psl3FieldAut σ) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ := by
  ext x
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  rw [burnsideA315h_Phi_apply_proj, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj]
  unfold psl3FieldAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_e_mk]
  rfl

theorem burnsideA315h_Phi_graph (F : Type) [Field F] :
    burnsideA315h_Phi F psl3GraphAut =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 3 F := by
  ext x
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  rw [burnsideA315h_Phi_apply_proj, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_proj]
  unfold psl3GraphAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_e_mk]
  rfl


theorem burnsideA315h_diag_one (F : Type) [Field F] : psl3DiagAut (1 : GL (Fin 3) F) = 1 := by
  apply (burnsideA315h_Phi F).injective
  rw [burnsideA315h_Phi_diag, map_one, map_one]

theorem burnsideA315h_diag_mul {F : Type} [Field F] (g h : GL (Fin 3) F) :
    psl3DiagAut (g * h) = psl3DiagAut g * psl3DiagAut h := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_diag]

theorem burnsideA315h_field_one (F : Type) [Field F] : psl3FieldAut (1 : RingAut F) = 1 := by
  apply (burnsideA315h_Phi F).injective
  rw [burnsideA315h_Phi_field, map_one, map_one]

theorem burnsideA315h_field_mul {F : Type} [Field F] (σ ρ : RingAut F) :
    psl3FieldAut (σ * ρ) = psl3FieldAut σ * psl3FieldAut ρ := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_field]

noncomputable def burnsideA315h_diagHom (F : Type) [Field F] : GL (Fin 3) F →* MulAut PSL(3, F) where
  toFun := psl3DiagAut
  map_one' := burnsideA315h_diag_one F
  map_mul' := burnsideA315h_diag_mul

noncomputable def burnsideA315h_fieldHom (F : Type) [Field F] : RingAut F →* MulAut PSL(3, F) where
  toFun := psl3FieldAut
  map_one' := burnsideA315h_field_one F
  map_mul' := burnsideA315h_field_mul

noncomputable abbrev burnsideA315h_gmap {F : Type} [Field F] (σ : RingAut F) (g : GL (Fin 3) F) :
    GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.map (σ : F →+* F) g

theorem burnsideA315h_field_conj {F : Type} [Field F] (σ : RingAut F) (g : GL (Fin 3) F) :
    psl3FieldAut σ * psl3DiagAut g * (psl3FieldAut σ)⁻¹ = psl3DiagAut (burnsideA315h_gmap σ g) := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, map_inv, burnsideA315h_Phi_diag, burnsideA315h_Phi_field]
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport
    (K := F) (n := 3)).2.2.1 σ g

theorem burnsideA315h_field_mul_diag {F : Type} [Field F] (σ : RingAut F) (g : GL (Fin 3) F) :
    psl3FieldAut σ * psl3DiagAut g = psl3DiagAut (burnsideA315h_gmap σ g) * psl3FieldAut σ := by
  rw [← burnsideA315h_field_conj, inv_mul_cancel_right]

theorem burnsideA315h_graph_sq (F : Type) [Field F] :
    psl3GraphAut * psl3GraphAut = (1 : MulAut PSL(3, F)) := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_graph, map_one]
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport
    (K := F) (n := 3)).2.2.2.1

theorem burnsideA315h_graph_diag {F : Type} [Field F] (g : GL (Fin 3) F) :
    psl3GraphAut * psl3DiagAut g * psl3GraphAut =
      psl3DiagAut (Matrix.GeneralLinearGroup.inverseTranspose g) := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_graph, burnsideA315h_Phi_diag]
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport
    (K := F) (n := 3)).2.2.2.2.1 g

theorem burnsideA315h_graph_field {F : Type} [Field F] (σ : RingAut F) :
    psl3GraphAut * psl3FieldAut σ * psl3GraphAut = psl3FieldAut σ := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_graph, burnsideA315h_Phi_field]
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport
    (K := F) (n := 3)).2.2.2.2.2.1 σ

theorem burnsideA315h_graph_comm_field {F : Type} [Field F] (σ : RingAut F) :
    psl3GraphAut * psl3FieldAut σ = psl3FieldAut σ * psl3GraphAut := by
  have h := burnsideA315h_graph_field σ
  have h2 := burnsideA315h_graph_sq F
  calc psl3GraphAut * psl3FieldAut σ
      = psl3GraphAut * psl3FieldAut σ * (psl3GraphAut * psl3GraphAut) := by rw [h2, mul_one]
    _ = psl3GraphAut * psl3FieldAut σ * psl3GraphAut * psl3GraphAut := by simp only [mul_assoc]
    _ = psl3FieldAut σ * psl3GraphAut := by rw [h]

theorem burnsideA315h_diagfield_mul {F : Type} [Field F] (g h : GL (Fin 3) F) (σ ρ : RingAut F) :
    psl3DiagAut g * psl3FieldAut σ * (psl3DiagAut h * psl3FieldAut ρ) =
      psl3DiagAut (g * burnsideA315h_gmap σ h) * psl3FieldAut (σ * ρ) := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_diag, burnsideA315h_Phi_field]
  simpa only [map_mul] using
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mul_fieldAut_mul g h σ ρ

theorem burnsideA315h_classification {F : Type} [Field F] [Finite F] (α : MulAut PSL(3, F)) :
    ∃ (g : GL (Fin 3) F) (σ : RingAut F) (ε : ℕ), ε ≤ 1 ∧
      α = psl3DiagAut g * psl3FieldAut σ * psl3GraphAut ^ ε := by
  obtain ⟨g, σ, ε, hε, h⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F) (n := 3)
      le_rfl).2 (burnsideA315h_Phi F α)
  refine ⟨g, σ, ε, hε, ?_⟩
  apply (burnsideA315h_Phi F).injective
  rw [h]
  simp only [map_mul, map_pow, burnsideA315h_Phi_diag, burnsideA315h_Phi_field,
    burnsideA315h_Phi_graph]


noncomputable def burnsideA315h_cubes (F : Type) [Field F] : Subgroup Fˣ :=
  (powMonoidHom 3 : Fˣ →* Fˣ).range

theorem burnsideA315h_mem_cubes_iff {F : Type} [Field F] (x : Fˣ) :
    x ∈ burnsideA315h_cubes F ↔ ∃ y : Fˣ, x = y ^ 3 := by
  unfold burnsideA315h_cubes
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

theorem burnsideA315h_inn_normal (F : Type) [Field F] : (psl3InnAut F).Normal :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _

theorem burnsideA315h_Phi_mem_inn {F : Type} [Field F] (α : MulAut PSL(3, F)) :
    burnsideA315h_Phi F α ∈ (MulAut.conj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL
      3 F →* MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)).range ↔
      α ∈ psl3InnAut F := by
  have h := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr (burnsideA315h_e F)
  constructor
  · intro hα
    have hα' : burnsideA315h_Phi F α ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        PSL(3, F)).map (burnsideA315h_Phi F).toMonoidHom := by
      rw [burnsideA315h_Phi, h]
      exact hα
    obtain ⟨β, hβ, hβα⟩ := hα'
    have : β = α := (burnsideA315h_Phi F).injective hβα
    exact this ▸ hβ
  · intro hα
    have hα' : burnsideA315h_Phi F α ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        PSL(3, F)).map (burnsideA315h_Phi F).toMonoidHom := ⟨α, hα, rfl⟩
    rw [burnsideA315h_Phi, h] at hα'
    exact hα'

theorem burnsideA315h_conj_mk {F : Type} [Field F] (s : SL(3, F)) :
    MulAut.conj (QuotientGroup.mk s : PSL(3, F)) =
      psl3DiagAut (Matrix.SpecialLinearGroup.toGL s) := by
  apply (burnsideA315h_Phi F).injective
  rw [burnsideA315h_Phi_diag, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_toGL]
  have h := CFSG.ComponentClassification.OuterAutomorphisms.congr_conj (burnsideA315h_e F)
    (QuotientGroup.mk s : PSL(3, F))
  rw [burnsideA315h_e_mk] at h
  exact h

theorem burnsideA315h_diagfield_eq_one {F : Type} [Field F] [Finite F] {g : GL (Fin 3) F}
    {σ : RingAut F} (h : psl3DiagAut g * psl3FieldAut σ = 1) :
    σ = 1 ∧ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = g := by
  have h' := congrArg (burnsideA315h_Phi F) h
  simp only [map_mul, burnsideA315h_Phi_diag, burnsideA315h_Phi_field, map_one] at h'
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
    le_rfl g σ h'

theorem burnsideA315h_diag_mem_inn_of_det {F : Type} [Field F] {g : GL (Fin 3) F}
    (h : Matrix.GeneralLinearGroup.det g ∈ burnsideA315h_cubes F) :
    psl3DiagAut g ∈ psl3InnAut F := by
  obtain ⟨y, hy⟩ := (burnsideA315h_mem_cubes_iff _).1 h
  rw [← burnsideA315h_Phi_mem_inn, burnsideA315h_Phi_diag]
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_range_conj_of_det_eq_pow hy

theorem burnsideA315h_mem_inn_iff {F : Type} [Field F] (ι : MulAut PSL(3, F)) :
    ι ∈ psl3InnAut F ↔ ∃ g : GL (Fin 3) F,
      Matrix.GeneralLinearGroup.det g ∈ burnsideA315h_cubes F ∧ ι = psl3DiagAut g := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨Matrix.SpecialLinearGroup.toGL s, ?_, burnsideA315h_conj_mk s⟩
    rw [Matrix.SpecialLinearGroup.coeToGL_det]
    exact one_mem _
  · rintro ⟨g, hg, rfl⟩
    exact burnsideA315h_diag_mem_inn_of_det hg

theorem burnsideA315h_diag_inv {F : Type} [Field F] (g : GL (Fin 3) F) :
    psl3DiagAut g⁻¹ = (psl3DiagAut g)⁻¹ :=
  map_inv (burnsideA315h_diagHom F) g

theorem burnsideA315h_field_inv {F : Type} [Field F] (σ : RingAut F) :
    psl3FieldAut σ⁻¹ = (psl3FieldAut σ)⁻¹ :=
  map_inv (burnsideA315h_fieldHom F) σ

theorem burnsideA315h_det_scalar_mem_cubes {F : Type} [Field F] (c : Fˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ∈
      burnsideA315h_cubes F :=
  (burnsideA315h_mem_cubes_iff _).2 ⟨c, by rw [Matrix.GeneralLinearGroup.det_scalar]; simp⟩

theorem burnsideA315h_diagfield_mem_inn_iff {F : Type} [Field F] [Finite F] (g : GL (Fin 3) F)
    (σ : RingAut F) :
    psl3DiagAut g * psl3FieldAut σ ∈ psl3InnAut F ↔
      σ = 1 ∧ Matrix.GeneralLinearGroup.det g ∈ burnsideA315h_cubes F := by
  constructor
  · intro h
    obtain ⟨h₀, hh₀, hgh⟩ := (burnsideA315h_mem_inn_iff _).1 h
    have h1 : psl3DiagAut (h₀⁻¹ * g) * psl3FieldAut σ = 1 := by
      rw [burnsideA315h_diag_mul, mul_assoc, hgh, burnsideA315h_diag_inv, inv_mul_cancel]
    obtain ⟨rfl, c, hc⟩ := burnsideA315h_diagfield_eq_one h1
    refine ⟨rfl, ?_⟩
    have hg : g = h₀ * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [hc]; group
    rw [hg, map_mul]
    exact mul_mem hh₀ (burnsideA315h_det_scalar_mem_cubes c)
  · rintro ⟨rfl, hg⟩
    rw [burnsideA315h_field_one, mul_one]
    exact burnsideA315h_diag_mem_inn_of_det hg

theorem burnsideA315h_diag_mem_inn_iff {F : Type} [Field F] [Finite F] (g : GL (Fin 3) F) :
    psl3DiagAut g ∈ psl3InnAut F ↔ Matrix.GeneralLinearGroup.det g ∈ burnsideA315h_cubes F := by
  have h := burnsideA315h_diagfield_mem_inn_iff g 1
  rw [burnsideA315h_field_one, mul_one] at h
  simpa using h

theorem burnsideA315h_conj_injective (F : Type) [Field F] [Finite F] :
    Function.Injective (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  rw [burnsideA315h_conj_mk] at hx
  have h1 : psl3DiagAut (Matrix.SpecialLinearGroup.toGL s) * psl3FieldAut (1 : RingAut F) = 1 := by
    rw [burnsideA315h_field_one, mul_one]; exact hx
  obtain ⟨-, c, hc⟩ := burnsideA315h_diagfield_eq_one h1
  have hdet : c ^ 3 = 1 := by
    have := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, Matrix.SpecialLinearGroup.coeToGL_det] at this
    simpa using this
  have hmat : (s : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c : F) := by
    have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
    simpa using this.symm
  have hs : s ∈ Subgroup.center SL(3, F) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact ⟨c, hdet, hmat⟩
  exact (QuotientGroup.eq_one_iff s).2 hs

theorem burnsideA315h_card_inn (F : Type) [Field F] [Finite F] :
    Nat.card (psl3InnAut F) = Nat.card PSL(3, F) :=
  (Nat.card_congr (MonoidHom.ofInjective (burnsideA315h_conj_injective F)).toEquiv).symm


theorem burnsideA315h_cube_of_dvd {G : Type*} [CommGroup G] (ω : G) {a : ℤ} (h : (3 : ℤ) ∣ a) :
    ∃ z : G, ω ^ a = z ^ 3 := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨ω ^ c, ?_⟩
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem burnsideA315h_cube_iff {G : Type*} [CommGroup G] {ω : G} {M : ℕ}
    (hord : orderOf ω = M) (hgen : ∀ x : G, x ∈ Subgroup.zpowers ω) (h3 : 3 ∣ M) (a : ℤ) :
    (∃ z : G, ω ^ a = z ^ 3) ↔ (3 : ℤ) ∣ a := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen z)
    rw [← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_modEq, hord] at hz
    have h3' : (3 : ℤ) ∣ (M : ℤ) := by exact_mod_cast h3
    have h4 := Int.ModEq.of_dvd h3' hz
    have h5 := (Int.modEq_iff_dvd.1 h4.symm)
    omega
  · exact burnsideA315h_cube_of_dvd ω

theorem burnsideA315h_cube_of_norm {G : Type*} [CommGroup G] {ω : G} {s : ℕ} (hs2 : 2 ≤ s)
    (hs3 : s % 3 = 1) (hM : orderOf ω + 1 = s ^ 3) (hgen : ∀ x : G, x ∈ Subgroup.zpowers ω)
    {d l : G} (hl : l ^ s = l) (hd : d ^ (1 + s + s ^ 2) = l ^ 3) : ∃ z : G, d = z ^ 3 := by
  have hMz : ((orderOf ω : ℕ) : ℤ) = (s : ℤ) ^ 3 - 1 := by
    have := congrArg (Nat.cast : ℕ → ℤ) hM
    push_cast at this
    linarith
  have hs1 : ((s : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ s := by exact_mod_cast hs2
    omega
  have hs2' : ((s : ℤ) ^ 2 + s + 1) ≠ 0 := by positivity
  have hs3z : (3 : ℤ) ∣ (s : ℤ) - 1 := by omega
  have hfac : (s : ℤ) ^ 3 - 1 = ((s : ℤ) - 1) * ((s : ℤ) ^ 2 + s + 1) := by ring
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen d)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen l)
  rw [← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_modEq, hMz] at hl
  have hb : ((s : ℤ) ^ 2 + s + 1) ∣ b := by
    have h1 := Int.modEq_iff_dvd.1 hl.symm
    rw [hfac] at h1
    have h2 : ((s : ℤ) - 1) * ((s : ℤ) ^ 2 + s + 1) ∣ ((s : ℤ) - 1) * b := by
      have h3 : ((s : ℤ) - 1) * b = b * s - b := by ring
      rw [h3]
      exact h1
    exact (mul_dvd_mul_iff_left hs1).1 h2
  obtain ⟨t, rfl⟩ := hb
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (ω ^ _) 3, ← zpow_mul, zpow_eq_zpow_iff_modEq,
    hMz] at hd
  have h1 := Int.modEq_iff_dvd.1 hd.symm
  rw [hfac] at h1
  push_cast at h1
  have h2 : ((s : ℤ) ^ 2 + s + 1) * ((s : ℤ) - 1) ∣ ((s : ℤ) ^ 2 + s + 1) * (a - 3 * t) := by
    have e1 : a * (1 + (s : ℤ) + (s : ℤ) ^ 2) - ((s : ℤ) ^ 2 + s + 1) * t * 3 =
        ((s : ℤ) ^ 2 + s + 1) * (a - 3 * t) := by ring
    rw [e1] at h1
    rw [mul_comm ((s : ℤ) ^ 2 + s + 1) ((s : ℤ) - 1)]
    exact h1
  have h3 : ((s : ℤ) - 1) ∣ (a - 3 * t) := (mul_dvd_mul_iff_left hs2').1 h2
  have h4 : (3 : ℤ) ∣ a := by
    have := hs3z.trans h3
    omega
  exact burnsideA315h_cube_of_dvd ω h4


theorem burnsideA315h_exists_gen (F : Type) [Field F] [Finite F] :
    ∃ ω : Fˣ, orderOf ω = Nat.card Fˣ ∧ ∀ x : Fˣ, x ∈ Subgroup.zpowers ω := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Fˣ)
  exact ⟨ω, orderOf_eq_card_of_forall_mem_zpowers hω, hω⟩

theorem burnsideA315h_card_units (F : Type) [Field F] [Finite F] :
    Nat.card Fˣ + 1 = Nat.card F := by
  rw [Nat.card_units]
  have : 0 < Nat.card F := Nat.card_pos
  omega

theorem burnsideA315h_s_facts {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 4 ^ n ∧ 4 ^ n % 3 = 1 := by
  refine ⟨?_, ?_⟩
  · calc 2 ≤ 4 := by norm_num
      _ = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  · rw [Nat.pow_mod]; norm_num

theorem burnsideA315h_card_cube {F : Type} [Field F] {n : ℕ} (hF : Nat.card F = 2 ^ (6 * n)) :
    Nat.card F = (4 ^ n) ^ 3 := by
  rw [hF, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  ring_nf

theorem burnsideA315h_aut_three {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) :
    ∃ e : ℕ, (e = 4 ^ n ∨ e = (4 ^ n) ^ 2) ∧ ∀ y : F, σ y = y ^ e := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 6 * n) hF
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
  rw [← hfin.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have h3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  rw [← hk, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord] at h3
  have h2n : 2 * n ∣ k := by
    have h' : 3 * (2 * n) ∣ 3 * k := by
      have e1 : 6 * n = 3 * (2 * n) := by ring
      rw [e1] at h3
      rwa [mul_comm k 3] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  obtain ⟨t, rfl⟩ := h2n
  have hS3 : (φ ^ (2 * n)) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * n * 3 = 6 * n by ring, ← hord]
    exact pow_orderOf_eq_one φ
  have hmod : ∀ m : ℕ, (φ ^ (2 * n)) ^ m = (φ ^ (2 * n)) ^ (m % 3) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hS3, one_pow, one_mul]
  have hσt : σ = (φ ^ (2 * n)) ^ (t % 3) := by
    rw [← hk, pow_mul, hmod]
  have ht3 : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hsq := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_apply_of_sq hφ
  interval_cases h : t % 3
  · exfalso
    rw [pow_zero] at hσt
    rw [hσt, orderOf_one] at hσ
    omega
  · refine ⟨4 ^ n, Or.inl rfl, fun y => ?_⟩
    rw [hσt, pow_one, hsq (2 * n) y, pow_mul]
    norm_num
  · refine ⟨(4 ^ n) ^ 2, Or.inr rfl, fun y => ?_⟩
    rw [hσt, ← pow_mul, hsq (2 * n * 2) y]
    rw [pow_mul, pow_mul]
    norm_num

theorem burnsideA315h_det_gmap {F : Type} [Field F] {σ : RingAut F} {e : ℕ}
    (hσ : ∀ y : F, σ y = y ^ e) (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (burnsideA315h_gmap σ g) =
      (Matrix.GeneralLinearGroup.det g) ^ e := by
  apply Units.ext
  rw [burnsideA315h_gmap, Matrix.GeneralLinearGroup.map_det]
  simp [hσ]


theorem burnsideA315h_gen_data {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) :
    ∃ ω : Fˣ, orderOf ω + 1 = (4 ^ n) ^ 3 ∧ (∀ x : Fˣ, x ∈ Subgroup.zpowers ω) ∧
      3 ∣ orderOf ω := by
  obtain ⟨ω, hord, hgen⟩ := burnsideA315h_exists_gen F
  have h1 := burnsideA315h_card_units F
  have h2 := burnsideA315h_card_cube hF
  have hs := (burnsideA315h_s_facts hn).2
  have hM : orderOf ω + 1 = (4 ^ n) ^ 3 := by rw [hord, ← h2, h1]
  refine ⟨ω, hM, hgen, ?_⟩
  have h3 : ((4 ^ n) ^ 3) % 3 = 1 := by rw [Nat.pow_mod, hs]
  omega

theorem burnsideA315h_zpow_mem_cubes_iff {F : Type} [Field F] {ω : Fˣ} {M : ℕ}
    (hord : orderOf ω = M) (hgen : ∀ x : Fˣ, x ∈ Subgroup.zpowers ω) (h3 : 3 ∣ M) (a : ℤ) :
    ω ^ a ∈ burnsideA315h_cubes F ↔ (3 : ℤ) ∣ a := by
  rw [burnsideA315h_mem_cubes_iff]
  exact burnsideA315h_cube_iff hord hgen h3 a

theorem burnsideA315h_cube_dichotomy {F : Type} [Field F] {ω : Fˣ} {M : ℕ}
    (hord : orderOf ω = M) (hgen : ∀ x : Fˣ, x ∈ Subgroup.zpowers ω) (h3 : 3 ∣ M) {u v : Fˣ}
    (hu : u ∉ burnsideA315h_cubes F) (hv : v ∉ burnsideA315h_cubes F) :
    v * u⁻¹ ∈ burnsideA315h_cubes F ∨ v * u ∈ burnsideA315h_cubes F := by
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen u)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen v)
  rw [burnsideA315h_zpow_mem_cubes_iff hord hgen h3] at hu hv
  have e1 : ω ^ b * (ω ^ a)⁻¹ = ω ^ (b - a) := (zpow_sub ω b a).symm
  have e2 : ω ^ b * ω ^ a = ω ^ (b + a) := (zpow_add ω b a).symm
  rw [e1, e2, burnsideA315h_zpow_mem_cubes_iff hord hgen h3,
    burnsideA315h_zpow_mem_cubes_iff hord hgen h3]
  have ha : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

theorem burnsideA315h_exists_noncube {F : Type} [Field F] {ω : Fˣ} {M : ℕ}
    (hord : orderOf ω = M) (hgen : ∀ x : Fˣ, x ∈ Subgroup.zpowers ω) (h3 : 3 ∣ M) :
    ω ∉ burnsideA315h_cubes F := by
  have := burnsideA315h_zpow_mem_cubes_iff (F := F) hord hgen h3 1
  rw [zpow_one] at this
  rw [this]
  omega

theorem burnsideA315h_exists_normone_noncube {F : Type} [Field F] {ω : Fˣ} {M q : ℕ}
    (hord : orderOf ω = M) (hgen : ∀ x : Fˣ, x ∈ Subgroup.zpowers ω) (h3 : 3 ∣ M)
    (hM : M + 1 = q ^ 2) (hq : q % 3 = 2) :
    ∃ β : Fˣ, β ^ (q + 1) = 1 ∧ β ∉ burnsideA315h_cubes F := by
  have hq1 : 1 ≤ q := by omega
  refine ⟨ω ^ (((q - 1 : ℕ) : ℤ)), ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have : ((q - 1 : ℕ) : ℤ) * ((q + 1 : ℕ) : ℤ) = (M : ℤ) := by
      have h := congrArg (Nat.cast : ℕ → ℤ) hM
      push_cast [Nat.cast_sub hq1] at h ⊢
      linarith
    rw [this, zpow_natCast, ← hord]
    exact pow_orderOf_eq_one ω
  · rw [burnsideA315h_zpow_mem_cubes_iff hord hgen h3]
    omega

theorem burnsideA315h_gmap_det_div_cube {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (burnsideA315h_gmap σ g) *
      (Matrix.GeneralLinearGroup.det g)⁻¹ ∈ burnsideA315h_cubes F := by
  obtain ⟨e, he, hσe⟩ := burnsideA315h_aut_three hn hF hσ
  rw [burnsideA315h_det_gmap hσe]
  have hs := burnsideA315h_s_facts hn
  have he1 : e % 3 = 1 := by
    rcases he with rfl | rfl
    · exact hs.2
    · rw [Nat.pow_mod, hs.2]
  have he2 : 1 ≤ e := by omega
  rw [burnsideA315h_mem_cubes_iff]
  refine ⟨Matrix.GeneralLinearGroup.det g ^ ((e - 1) / 3), ?_⟩
  rw [← pow_mul, show (e - 1) / 3 * 3 = e - 1 by omega]
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
  simp [pow_succ]

theorem burnsideA315h_gmap_noncube {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) {g : GL (Fin 3) F}
    (hg : Matrix.GeneralLinearGroup.det g ∉ burnsideA315h_cubes F) :
    Matrix.GeneralLinearGroup.det (burnsideA315h_gmap σ g) ∉ burnsideA315h_cubes F := by
  intro h
  apply hg
  have h2 := burnsideA315h_gmap_det_div_cube hn hF hσ g
  have := mul_mem h (inv_mem h2)
  simpa using this


theorem burnsideA315h_gmap_mul {F : Type} [Field F] (σ ρ : RingAut F) (g : GL (Fin 3) F) :
    burnsideA315h_gmap (σ * ρ) g = burnsideA315h_gmap σ (burnsideA315h_gmap ρ g) := by
  apply Units.ext
  ext i j
  simp [burnsideA315h_gmap, Matrix.GeneralLinearGroup.map_apply]

theorem burnsideA315h_gmap_one {F : Type} [Field F] (g : GL (Fin 3) F) :
    burnsideA315h_gmap (1 : RingAut F) g = g := by
  apply Units.ext
  ext i j
  simp [burnsideA315h_gmap, Matrix.GeneralLinearGroup.map_apply]

theorem burnsideA315h_gmap_mul' {F : Type} [Field F] (σ : RingAut F) (g h : GL (Fin 3) F) :
    burnsideA315h_gmap σ (g * h) = burnsideA315h_gmap σ g * burnsideA315h_gmap σ h :=
  map_mul _ g h

theorem burnsideA315h_pow_three {F : Type} [Field F] (h : GL (Fin 3) F) (σ : RingAut F) :
    (psl3DiagAut h * psl3FieldAut σ) ^ 3 =
      psl3DiagAut (h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h) *
        psl3FieldAut (σ * σ * σ) := by
  have h2 : (psl3DiagAut h * psl3FieldAut σ) ^ 2 =
      psl3DiagAut (h * burnsideA315h_gmap σ h) * psl3FieldAut (σ * σ) := by
    rw [pow_two, burnsideA315h_diagfield_mul]
  rw [pow_succ, h2, burnsideA315h_diagfield_mul]

theorem burnsideA315h_order_three {F : Type} [Field F] {σ : RingAut F} (hσ : orderOf σ = 3) :
    σ ≠ 1 ∧ σ * σ ≠ 1 ∧ σ * σ * σ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at hσ
    omega
  · intro h
    have h2 : σ ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hσ] at this
    omega
  · rw [← pow_three', ← hσ]
    exact pow_orderOf_eq_one σ

theorem burnsideA315h_det_N_cube {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (h : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h) ∈
      burnsideA315h_cubes F := by
  obtain ⟨e, he, hσe⟩ := burnsideA315h_aut_three hn hF hσ
  have hσσ : ∀ y : F, (σ * σ) y = y ^ (e * e) := by
    intro y
    rw [RingAut.mul_apply, hσe, hσe, ← pow_mul]
  rw [map_mul, map_mul, burnsideA315h_det_gmap hσe, burnsideA315h_det_gmap hσσ]
  have hs := burnsideA315h_s_facts hn
  have he1 : e % 3 = 1 := by
    rcases he with rfl | rfl
    · exact hs.2
    · rw [Nat.pow_mod, hs.2]
  have hee : (e * e) % 3 = 1 := by rw [Nat.mul_mod, he1]
  rw [burnsideA315h_mem_cubes_iff]
  refine ⟨Matrix.GeneralLinearGroup.det h ^ ((1 + e + e * e) / 3), ?_⟩
  rw [← pow_mul, show (1 + e + e * e) / 3 * 3 = 1 + e + e * e by omega, pow_add, pow_add, pow_one]

noncomputable abbrev burnsideA315h_pi (F : Type) [Field F] :
    MulAut PSL(3, F) →* CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F) :=
  QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner PSL(3, F))

theorem burnsideA315h_pi_eq_one_iff {F : Type} [Field F] (α : MulAut PSL(3, F)) :
    burnsideA315h_pi F α = 1 ↔ α ∈ psl3InnAut F :=
  QuotientGroup.eq_one_iff α

theorem burnsideA315h_x_facts {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F) :
    psl3FieldAut σ * psl3DiagAut g ∉ psl3InnAut F ∧
      (psl3FieldAut σ * psl3DiagAut g) ^ 2 ∉ psl3InnAut F ∧
      (psl3FieldAut σ * psl3DiagAut g) ^ 3 ∈ psl3InnAut F := by
  obtain ⟨hσ1, hσ2, hσ3⟩ := burnsideA315h_order_three hσ
  have hx : psl3FieldAut σ * psl3DiagAut g =
      psl3DiagAut (burnsideA315h_gmap σ g) * psl3FieldAut σ := burnsideA315h_field_mul_diag σ g
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, burnsideA315h_diagfield_mem_inn_iff]
    exact fun h => hσ1 h.1
  · rw [hx, pow_two, burnsideA315h_diagfield_mul, burnsideA315h_diagfield_mem_inn_iff]
    exact fun h => hσ2 h.1
  · rw [hx, burnsideA315h_pow_three, hσ3, burnsideA315h_field_one, mul_one]
    exact burnsideA315h_diag_mem_inn_of_det (burnsideA315h_det_N_cube hn hF hσ _)


theorem burnsideA315h_closure_eq_comap {F : Type} [Field F] (x : MulAut PSL(3, F)) :
    Subgroup.closure ((psl3InnAut F : Set (MulAut PSL(3, F))) ∪ {x}) =
      (Subgroup.zpowers (burnsideA315h_pi F x)).comap (burnsideA315h_pi F) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · show burnsideA315h_pi F y ∈ Subgroup.zpowers _
      have : burnsideA315h_pi F y = 1 := (burnsideA315h_pi_eq_one_iff y).2 hy
      rw [this]
      exact one_mem _
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_zpowers _
  · intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 ha)
    have hx : x ∈ Subgroup.closure ((psl3InnAut F : Set (MulAut PSL(3, F))) ∪ {x}) :=
      Subgroup.subset_closure (Or.inr rfl)
    have hxk : x ^ k ∈ Subgroup.closure ((psl3InnAut F : Set (MulAut PSL(3, F))) ∪ {x}) :=
      zpow_mem hx k
    have hι : a * (x ^ k)⁻¹ ∈ psl3InnAut F := by
      rw [← burnsideA315h_pi_eq_one_iff, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have : a = (a * (x ^ k)⁻¹) * x ^ k := by group
    rw [this]
    exact mul_mem (Subgroup.subset_closure (Or.inl hι)) hxk

theorem burnsideA315h_orderOf_pi {F : Type} [Field F] {x : MulAut PSL(3, F)}
    (h1 : x ∉ psl3InnAut F) (h3 : x ^ 3 ∈ psl3InnAut F) : orderOf (burnsideA315h_pi F x) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    exact (burnsideA315h_pi_eq_one_iff _).2 h3
  · intro h
    exact h1 ((burnsideA315h_pi_eq_one_iff _).1 h)

theorem burnsideA315h_card_comap {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup H) :
    Nat.card (T.comap f) = Nat.card T * Nat.card f.ker := by
  let f' : ↥(T.comap f) →* ↥T := (f.comp (T.comap f).subtype).codRestrict T (fun x => x.2)
  have hf' : Function.Surjective f' := by
    intro t
    obtain ⟨g, hg⟩ := hf t
    exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact t.2⟩, Subtype.ext hg⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f' hf').toEquiv] at h1
  have hker : f'.ker = f.ker.subgroupOf (T.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hle : f.ker ≤ T.comap f := fun y hy => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hy]
    exact one_mem _
  rw [h1, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem burnsideA315h_ker_pi {F : Type} [Field F] :
    (burnsideA315h_pi F).ker = psl3InnAut F :=
  QuotientGroup.ker_mk' _

theorem burnsideA315h_card_circ {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F) :
    Nat.card (psl3Circ σ g) = 3 * Nat.card PSL(3, F) := by
  obtain ⟨hx1, -, hx3⟩ := burnsideA315h_x_facts hn hF hσ g
  have hπ : orderOf (burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g)) = 3 :=
    burnsideA315h_orderOf_pi hx1 hx3
  unfold psl3Circ
  rw [burnsideA315h_closure_eq_comap, burnsideA315h_card_comap _ (QuotientGroup.mk'_surjective _),
    Nat.card_zpowers, hπ, burnsideA315h_ker_pi, burnsideA315h_card_inn]


theorem burnsideA315h_pow_s3 {F : Type} [Field F] {ω : Fˣ} {s : ℕ}
    (hM : orderOf ω + 1 = s ^ 3) (hgen : ∀ x : Fˣ, x ∈ Subgroup.zpowers ω) (x : Fˣ) :
    x ^ (s ^ 3) = x := by
  have h1 : orderOf x ∣ orderOf ω := orderOf_dvd_of_mem_zpowers (hgen x)
  have h2 : x ^ orderOf ω = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
  rw [← hM, pow_succ, h2, one_mul]

theorem burnsideA315h_unit_norm_cube {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {e : ℕ} (he : e = 4 ^ n ∨ e = (4 ^ n) ^ 2) {d c : Fˣ}
    (hc : c ^ e = c) (hd : d ^ (1 + e + e * e) = c ^ 3) : d ∈ burnsideA315h_cubes F := by
  obtain ⟨ω, hM, hgen, -⟩ := burnsideA315h_gen_data hn hF
  have hs := burnsideA315h_s_facts hn
  have hp := burnsideA315h_pow_s3 hM hgen
  rw [burnsideA315h_mem_cubes_iff]
  rcases he with rfl | rfl
  · exact burnsideA315h_cube_of_norm hs.1 hs.2 hM hgen hc (by rw [pow_two]; exact hd)
  · set s := 4 ^ n with hs'
    have h1 : c ^ (s ^ 4) = c := by
      rw [show s ^ 4 = s ^ 2 * s ^ 2 by ring, pow_mul, hc, hc]
    have h2 : c ^ (s ^ 4) = c ^ s := by
      rw [show s ^ 4 = s ^ 3 * s by ring, pow_mul, hp]
    have hcs : c ^ s = c := by rw [← h2, h1]
    have h3 : d ^ (s ^ 2 * s ^ 2) = d ^ s := by
      rw [show s ^ 2 * s ^ 2 = s ^ 3 * s by ring, pow_mul, hp]
    refine burnsideA315h_cube_of_norm hs.1 hs.2 hM hgen hcs ?_
    rw [pow_add, pow_add] at hd ⊢
    rw [h3] at hd
    rw [← hd]
    exact mul_right_comm _ _ _

theorem burnsideA315h_scalar_inj {F : Type} [Field F] {c c' : Fˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin 3) c = Matrix.GeneralLinearGroup.scalar (Fin 3) c') :
    c = c' := by
  have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  apply Units.ext
  simpa using this

theorem burnsideA315h_norm_not_scalar {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) {h : GL (Fin 3) F}
    (hh : Matrix.GeneralLinearGroup.det h ∉ burnsideA315h_cubes F) (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ≠
      h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h := by
  intro hc
  obtain ⟨hσ1, hσ2, hσ3⟩ := burnsideA315h_order_three hσ
  obtain ⟨e, he, hσe⟩ := burnsideA315h_aut_three hn hF hσ
  have hσσ : ∀ y : F, (σ * σ) y = y ^ (e * e) := by
    intro y
    rw [RingAut.mul_apply, hσe, hσe, ← pow_mul]
  have h1 : burnsideA315h_gmap σ
      (h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h) =
      h⁻¹ * (h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h) * h := by
    rw [burnsideA315h_gmap_mul', burnsideA315h_gmap_mul', ← burnsideA315h_gmap_mul,
      ← burnsideA315h_gmap_mul, show σ * (σ * σ) = 1 by rw [← mul_assoc]; exact hσ3,
      burnsideA315h_gmap_one]
    group
  have hfix : burnsideA315h_gmap σ (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    calc burnsideA315h_gmap σ (Matrix.GeneralLinearGroup.scalar (Fin 3) c)
        = burnsideA315h_gmap σ (h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h) := by
          rw [hc]
      _ = h⁻¹ * (h * burnsideA315h_gmap σ h * burnsideA315h_gmap (σ * σ) h) * h := h1
      _ = h⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c * h := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
          rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel,
            one_mul]
  have hfix' : Units.map (σ : F →+* F) c = c := by
    apply burnsideA315h_scalar_inj
    rw [← Matrix.GeneralLinearGroup.map_scalar]
    exact hfix
  have hce : c ^ e = c := by
    apply Units.ext
    have := congrArg Units.val hfix'
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    rw [Units.val_pow_eq_pow_val, ← hσe]
    exact this
  have hdet := congrArg Matrix.GeneralLinearGroup.det hc
  rw [Matrix.GeneralLinearGroup.det_scalar, map_mul, map_mul, burnsideA315h_det_gmap hσe,
    burnsideA315h_det_gmap hσσ] at hdet
  have hd : Matrix.GeneralLinearGroup.det h ^ (1 + e + e * e) = c ^ 3 := by
    rw [pow_add, pow_add, pow_one]
    simpa using hdet.symm
  exact hh (burnsideA315h_unit_norm_cube hn hF he hce hd)


theorem burnsideA315h_nonsplit {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) {g : GL (Fin 3) F}
    (hg : psl3DiagAut g ∉ psl3InnAut F) :
    ∀ a : MulAut PSL(3, F), (∃ ι ∈ psl3InnAut F, a = ι * (psl3FieldAut σ * psl3DiagAut g)) →
      orderOf a ≠ 3 := by
  rintro a ⟨ι, hι, rfl⟩ h3
  obtain ⟨ĝ, hĝ, rfl⟩ := (burnsideA315h_mem_inn_iff ι).1 hι
  obtain ⟨-, -, hσ3⟩ := burnsideA315h_order_three hσ
  have hdg : Matrix.GeneralLinearGroup.det g ∉ burnsideA315h_cubes F := by
    rwa [← burnsideA315h_diag_mem_inn_iff]
  have hdg' := burnsideA315h_gmap_noncube hn hF hσ hdg
  have hform : psl3DiagAut ĝ * (psl3FieldAut σ * psl3DiagAut g) =
      psl3DiagAut (ĝ * burnsideA315h_gmap σ g) * psl3FieldAut σ := by
    rw [burnsideA315h_field_mul_diag, ← mul_assoc, ← burnsideA315h_diag_mul]
  have hh : Matrix.GeneralLinearGroup.det (ĝ * burnsideA315h_gmap σ g) ∉
      burnsideA315h_cubes F := by
    intro hmem
    apply hdg'
    rw [map_mul] at hmem
    have := mul_mem (inv_mem hĝ) hmem
    simpa using this
  have hpow := pow_orderOf_eq_one (psl3DiagAut ĝ * (psl3FieldAut σ * psl3DiagAut g))
  rw [h3, hform, burnsideA315h_pow_three, hσ3, burnsideA315h_field_one, mul_one] at hpow
  have h1 : psl3DiagAut (ĝ * burnsideA315h_gmap σ g *
        burnsideA315h_gmap σ (ĝ * burnsideA315h_gmap σ g) *
        burnsideA315h_gmap (σ * σ) (ĝ * burnsideA315h_gmap σ g)) *
      psl3FieldAut (1 : RingAut F) = 1 := by
    rw [burnsideA315h_field_one, mul_one]
    exact hpow
  obtain ⟨-, c, hc⟩ := burnsideA315h_diagfield_eq_one h1
  exact burnsideA315h_norm_not_scalar hn hF hσ hh c hc

theorem burnsideA315h_mem_coset {F : Type} [Field F] {a x : MulAut PSL(3, F)}
    (h : burnsideA315h_pi F a = burnsideA315h_pi F x) : ∃ ι ∈ psl3InnAut F, a = ι * x := by
  refine ⟨a * x⁻¹, ?_, by group⟩
  rw [← burnsideA315h_pi_eq_one_iff, map_mul, map_inv, h, mul_inv_cancel]

theorem burnsideA315h_order_three_mem_inn {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) {g : GL (Fin 3) F}
    (hg : psl3DiagAut g ∉ psl3InnAut F) :
    ∀ a ∈ psl3Circ σ g, orderOf a = 3 → a ∈ psl3InnAut F := by
  intro a ha h3
  obtain ⟨hx1, -, hx3⟩ := burnsideA315h_x_facts hn hF hσ g
  have hπ := burnsideA315h_orderOf_pi hx1 hx3
  have hns := burnsideA315h_nonsplit hn hF hσ hg
  unfold psl3Circ at ha
  rw [burnsideA315h_closure_eq_comap] at ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 ha)
  set x := psl3FieldAut σ * psl3DiagAut g with hxdef
  have hk3 : (burnsideA315h_pi F x) ^ (k % 3) = burnsideA315h_pi F a := by
    rw [← hk]
    have := zpow_mod_orderOf (burnsideA315h_pi F x) k
    rwa [hπ] at this
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [hr, zpow_zero] at hk3
    exact (burnsideA315h_pi_eq_one_iff a).1 hk3.symm
  · exfalso
    rw [hr, zpow_one] at hk3
    obtain ⟨ι, hι, hιa⟩ := burnsideA315h_mem_coset hk3.symm
    exact hns a ⟨ι, hι, hιa⟩ h3
  · exfalso
    rw [hr] at hk3
    have h2 : burnsideA315h_pi F a⁻¹ = burnsideA315h_pi F x := by
      rw [map_inv, ← hk3]
      have h3' : burnsideA315h_pi F x ^ 3 = 1 := by
        have := pow_orderOf_eq_one (burnsideA315h_pi F x)
        rwa [hπ] at this
      calc (burnsideA315h_pi F x ^ (2 : ℤ))⁻¹ = (burnsideA315h_pi F x ^ 2)⁻¹ := by norm_cast
        _ = burnsideA315h_pi F x := by
          rw [inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv, ← pow_succ, h3']
    obtain ⟨ι, hι, hιa⟩ := burnsideA315h_mem_coset h2.symm.symm
    have := hns a⁻¹ ⟨ι, hι, hιa⟩
    rw [orderOf_inv] at this
    exact this h3

theorem burnsideA315h_isL3Circ_true {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) {g : GL (Fin 3) F}
    (hg : psl3DiagAut g ∉ psl3InnAut F) :
    CFSG.Quasithin.IsL3Circ true (2 ^ (6 * n)) ↥(psl3Circ σ g) := by
  refine ⟨(psl3InnAut F).subgroupOf (psl3Circ σ g), n, F, inferInstance, inferInstance, hn, hF,
    σ, g, hσ, hg, ?_⟩
  simp only [if_true]
  refine ⟨trivial, MulEquiv.refl _, ?_⟩
  exact Subgroup.map_id _

theorem burnsideA315h_isL3Circ_false {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (hodd : Odd n) {σ : RingAut F} (hσ : orderOf σ = 3)
    {g : GL (Fin 3) F} (hg : psl3DiagAut g ∉ psl3InnAut F) {κ : MulAut PSL(3, F)}
    (hκ : IsPsl3GraphField κ) :
    CFSG.Quasithin.IsL3Circ false (2 ^ (3 * n))
      ↥(psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F)))) := by
  refine ⟨(psl3InnAut F).subgroupOf
    (psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F)))), n, F, inferInstance,
    inferInstance, hn, hF, σ, g, hσ, hg, ?_⟩
  simp only [Bool.false_eq_true, if_false]
  refine ⟨trivial, hodd, κ, hκ, MulEquiv.refl _, ?_⟩
  exact Subgroup.map_id _


theorem burnsideA315h_pow_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ (6 * n)) (y : F) : y ^ (4 ^ n) ^ 3 = y := by
  haveI := Fintype.ofFinite F
  have h := FiniteField.pow_card y
  rwa [Fintype.card_eq_nat_card, burnsideA315h_card_cube hF] at h

theorem burnsideA315h_aut_three_pair {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ σ' : RingAut F} (hσ : orderOf σ = 3)
    (hσ' : orderOf σ' = 3) : σ' = σ ∨ σ' = σ⁻¹ := by
  obtain ⟨e, he, hσe⟩ := burnsideA315h_aut_three hn hF hσ
  obtain ⟨e', he', hσe'⟩ := burnsideA315h_aut_three hn hF hσ'
  have hp := burnsideA315h_pow_card hF
  have hinv : σ * σ' = 1 → σ' = σ⁻¹ := fun h => eq_inv_of_mul_eq_one_right h
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · left
    exact RingEquiv.ext fun y => by rw [hσe, hσe']
  · right
    apply hinv
    apply RingEquiv.ext
    intro y
    rw [RingAut.mul_apply, hσe', hσe, ← pow_mul, RingAut.one_apply]
    convert hp y using 2
    ring
  · right
    apply hinv
    apply RingEquiv.ext
    intro y
    rw [RingAut.mul_apply, hσe', hσe, ← pow_mul, RingAut.one_apply]
    convert hp y using 2
    ring
  · left
    exact RingEquiv.ext fun y => by rw [hσe, hσe']

theorem burnsideA315h_circ_congr {F : Type} [Field F] [Finite F] (σ : RingAut F)
    {g g' : GL (Fin 3) F}
    (h : Matrix.GeneralLinearGroup.det (g⁻¹ * g') ∈ burnsideA315h_cubes F) :
    psl3Circ σ g = psl3Circ σ g' := by
  unfold psl3Circ
  rw [burnsideA315h_closure_eq_comap, burnsideA315h_closure_eq_comap]
  have h1 : burnsideA315h_pi F (psl3DiagAut (g⁻¹ * g')) = 1 :=
    (burnsideA315h_pi_eq_one_iff _).2 (burnsideA315h_diag_mem_inn_of_det h)
  have h2 : burnsideA315h_pi F (psl3DiagAut g') = burnsideA315h_pi F (psl3DiagAut g) := by
    have : psl3DiagAut g' = psl3DiagAut g * psl3DiagAut (g⁻¹ * g') := by
      rw [← burnsideA315h_diag_mul]; congr 1; group
    rw [this, map_mul, h1, mul_one]
  rw [map_mul, map_mul, h2]

theorem burnsideA315h_circ_inv {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F) :
    psl3Circ σ⁻¹ g⁻¹ = psl3Circ σ g := by
  unfold psl3Circ
  rw [burnsideA315h_closure_eq_comap, burnsideA315h_closure_eq_comap]
  have hxx : (psl3FieldAut σ * psl3DiagAut g) * (psl3FieldAut σ⁻¹ * psl3DiagAut g⁻¹) ∈
      psl3InnAut F := by
    have : (psl3FieldAut σ * psl3DiagAut g) * (psl3FieldAut σ⁻¹ * psl3DiagAut g⁻¹) =
        psl3DiagAut (burnsideA315h_gmap σ g * g⁻¹) := by
      rw [burnsideA315h_field_inv, burnsideA315h_diag_mul, ← burnsideA315h_field_conj,
        burnsideA315h_diag_inv]
      group
    rw [this]
    apply burnsideA315h_diag_mem_inn_of_det
    have := burnsideA315h_gmap_det_div_cube hn hF hσ g
    rwa [map_mul, map_inv]
  have h1 : burnsideA315h_pi F (psl3FieldAut σ⁻¹ * psl3DiagAut g⁻¹) =
      (burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul]
    exact (burnsideA315h_pi_eq_one_iff _).2 hxx
  rw [h1, Subgroup.zpowers_inv]

theorem burnsideA315h_map_closure_conj {F : Type} [Field F] (γ x : MulAut PSL(3, F)) :
    (Subgroup.closure ((psl3InnAut F : Set (MulAut PSL(3, F))) ∪ {x})).map
        (MulAut.conj γ).toMonoidHom =
      Subgroup.closure ((psl3InnAut F : Set (MulAut PSL(3, F))) ∪ {γ * x * γ⁻¹}) := by
  rw [MonoidHom.map_closure, Set.image_union, Set.image_singleton]
  have hI : (MulAut.conj γ).toMonoidHom '' (psl3InnAut F : Set (MulAut PSL(3, F))) =
      (psl3InnAut F : Set (MulAut PSL(3, F))) := by
    have hN := burnsideA315h_inn_normal F
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hN.conj_mem i hi γ
    · intro hy
      refine ⟨γ⁻¹ * y * γ⁻¹⁻¹, hN.conj_mem y hy γ⁻¹, ?_⟩
      show γ * (γ⁻¹ * y * γ⁻¹⁻¹) * γ⁻¹ = y
      group
  rw [hI]
  rfl

theorem burnsideA315h_circ_graph {F : Type} [Field F] (σ : RingAut F) (g : GL (Fin 3) F) :
    Nonempty (↥(psl3Circ σ g) ≃*
      ↥(psl3Circ σ (Matrix.GeneralLinearGroup.inverseTranspose g))) := by
  have hmap := burnsideA315h_map_closure_conj (psl3GraphAut : MulAut PSL(3, F))
    (psl3FieldAut σ * psl3DiagAut g)
  have hγ : (psl3GraphAut : MulAut PSL(3, F))⁻¹ = psl3GraphAut :=
    inv_eq_of_mul_eq_one_right (burnsideA315h_graph_sq F)
  have hx : psl3GraphAut * (psl3FieldAut σ * psl3DiagAut g) * (psl3GraphAut : MulAut PSL(3, F))⁻¹ =
      psl3FieldAut σ * psl3DiagAut (Matrix.GeneralLinearGroup.inverseTranspose g) := by
    rw [hγ, ← burnsideA315h_graph_diag, ← mul_assoc, burnsideA315h_graph_comm_field]
    have := burnsideA315h_graph_sq F
    calc psl3FieldAut σ * psl3GraphAut * psl3DiagAut g * psl3GraphAut
        = psl3FieldAut σ * (psl3GraphAut * psl3DiagAut g * psl3GraphAut) := by
          simp only [mul_assoc]
      _ = _ := by rw [burnsideA315h_graph_diag]
  rw [hx] at hmap
  have hinj : Function.Injective (MulAut.conj (psl3GraphAut : MulAut PSL(3, F))).toMonoidHom :=
    (MulAut.conj _).injective
  exact ⟨(Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hmap)⟩

theorem burnsideA315h_det_invT {F : Type} [Field F] (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.inverseTranspose g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_transpose]


theorem burnsideA315h_circ_iso {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ σ' : RingAut F} (hσ : orderOf σ = 3)
    (hσ' : orderOf σ' = 3) {g g' : GL (Fin 3) F} (hg : psl3DiagAut g ∉ psl3InnAut F)
    (hg' : psl3DiagAut g' ∉ psl3InnAut F) :
    Nonempty (↥(psl3Circ σ g) ≃* ↥(psl3Circ σ' g')) := by
  obtain ⟨ω, hM, hgen, h3⟩ := burnsideA315h_gen_data hn hF
  have key : ∀ g'' : GL (Fin 3) F, psl3DiagAut g'' ∉ psl3InnAut F →
      Nonempty (↥(psl3Circ σ g) ≃* ↥(psl3Circ σ g'')) := by
    intro g'' hg''
    have hu : Matrix.GeneralLinearGroup.det g ∉ burnsideA315h_cubes F := by
      rwa [← burnsideA315h_diag_mem_inn_iff]
    have hv : Matrix.GeneralLinearGroup.det g'' ∉ burnsideA315h_cubes F := by
      rwa [← burnsideA315h_diag_mem_inn_iff]
    rcases burnsideA315h_cube_dichotomy rfl hgen h3 hu hv with hd | hd
    · have : psl3Circ σ g = psl3Circ σ g'' := by
        apply burnsideA315h_circ_congr
        rw [map_mul, map_inv, mul_comm]
        exact hd
      exact ⟨MulEquiv.subgroupCongr this⟩
    · obtain ⟨e⟩ := burnsideA315h_circ_graph σ g
      have : psl3Circ σ (Matrix.GeneralLinearGroup.inverseTranspose g) = psl3Circ σ g'' := by
        apply burnsideA315h_circ_congr
        rw [map_mul, map_inv, burnsideA315h_det_invT, inv_inv, mul_comm]
        exact hd
      exact ⟨e.trans (MulEquiv.subgroupCongr this)⟩
  rcases burnsideA315h_aut_three_pair hn hF hσ hσ' with rfl | rfl
  · exact key g' hg'
  · have h1 : psl3Circ σ⁻¹ g' = psl3Circ σ g'⁻¹ := by
      have := burnsideA315h_circ_inv hn hF hσ g'⁻¹
      rwa [inv_inv] at this
    have hg'' : psl3DiagAut g'⁻¹ ∉ psl3InnAut F := by
      rw [burnsideA315h_diag_mem_inn_iff] at hg' ⊢
      rw [map_inv]
      exact fun h => hg' (by simpa using inv_mem h)
    rw [h1]
    exact key g'⁻¹ hg''


theorem burnsideA315h_aut_comm {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (σ τ : RingAut F) : σ * τ = τ * σ := by
  obtain ⟨φ, -, -, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 6 * n) hF
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hzp ▸ Subgroup.mem_top σ)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hzp ▸ Subgroup.mem_top τ)
  exact zpow_mul_comm φ a b

theorem burnsideA315h_gmap_det_div_cube_of_exp {F : Type} [Field F] {σ : RingAut F} {e : ℕ}
    (he1 : e % 3 = 1) (hσe : ∀ y : F, σ y = y ^ e) (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (burnsideA315h_gmap σ g) *
      (Matrix.GeneralLinearGroup.det g)⁻¹ ∈ burnsideA315h_cubes F := by
  rw [burnsideA315h_det_gmap hσe, burnsideA315h_mem_cubes_iff]
  have he2 : 1 ≤ e := by omega
  refine ⟨Matrix.GeneralLinearGroup.det g ^ ((e - 1) / 3), ?_⟩
  rw [← pow_mul, show (e - 1) / 3 * 3 = e - 1 by omega]
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
  simp [pow_succ]

theorem burnsideA315h_pi_field_diag_comm {F : Type} [Field F] [Finite F] {σ : RingAut F}
    {e : ℕ} (he1 : e % 3 = 1) (hσe : ∀ y : F, σ y = y ^ e) (g : GL (Fin 3) F) :
    burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g) =
      burnsideA315h_pi F (psl3DiagAut g * psl3FieldAut σ) := by
  have hdiv := burnsideA315h_gmap_det_div_cube_of_exp he1 hσe g
  have h1 : psl3DiagAut (g⁻¹ * burnsideA315h_gmap σ g) ∈ psl3InnAut F := by
    apply burnsideA315h_diag_mem_inn_of_det
    rw [map_mul, map_inv, mul_comm]
    exact hdiv
  have h2 : burnsideA315h_pi F (psl3DiagAut (burnsideA315h_gmap σ g)) =
      burnsideA315h_pi F (psl3DiagAut g) := by
    have : psl3DiagAut (burnsideA315h_gmap σ g) =
        psl3DiagAut g * psl3DiagAut (g⁻¹ * burnsideA315h_gmap σ g) := by
      rw [← burnsideA315h_diag_mul]; congr 1; group
    rw [this, map_mul, (burnsideA315h_pi_eq_one_iff _).2 h1, mul_one]
  rw [burnsideA315h_field_mul_diag, map_mul, map_mul, h2]

noncomputable def burnsideA315h_E (F : Type) [Field F] : Subgroup (MulAut PSL(3, F)) :=
  (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.semilinearAutGroup 3 F).comap
    (burnsideA315h_Phi F).toMonoidHom

theorem burnsideA315h_mem_E_iff {F : Type} [Field F] (α : MulAut PSL(3, F)) :
    α ∈ burnsideA315h_E F ↔ ∃ (g : GL (Fin 3) F) (σ : RingAut F),
      α = psl3DiagAut g * psl3FieldAut σ := by
  unfold burnsideA315h_E
  rw [Subgroup.mem_comap, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_iff]
  constructor
  · rintro ⟨g, σ, h⟩
    refine ⟨g, σ, (burnsideA315h_Phi F).injective ?_⟩
    simp only [map_mul, burnsideA315h_Phi_diag, burnsideA315h_Phi_field]
    exact h
  · rintro ⟨g, σ, rfl⟩
    refine ⟨g, σ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, burnsideA315h_Phi_diag, burnsideA315h_Phi_field]

theorem burnsideA315h_index_E_le {F : Type} [Field F] [Finite F] :
    (burnsideA315h_E F).index ≤ 2 := by
  have hR := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
    (K := F) (n := 3) le_rfl).1
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_outer_quotients (n := 3) (K := F)
  have h2 : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.semilinearAutGroup 3 F).relIndex
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standardAutGroup 3 F) ≤ 2 := hidx
  rw [hR, Subgroup.relIndex_top_right] at h2
  unfold burnsideA315h_E
  rwa [Subgroup.index_comap_of_surjective _ (burnsideA315h_Phi F).surjective]


theorem burnsideA315h_finite_psl (F : Type) [Field F] [Finite F] : Finite PSL(3, F) := by
  haveI : Finite SL(3, F) := inferInstance
  exact inferInstance

theorem burnsideA315h_finite_aut (F : Type) [Field F] [Finite F] : Finite (MulAut PSL(3, F)) := by
  haveI := burnsideA315h_finite_psl F
  exact Finite.of_injective (fun β : MulAut PSL(3, F) => (β : PSL(3, F) → PSL(3, F)))
    fun _ _ h => MulEquiv.ext (congrFun h)

theorem burnsideA315h_cubes_index {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) : (burnsideA315h_cubes F).index = 3 := by
  obtain ⟨ω, hM, hgen, h3⟩ := burnsideA315h_gen_data hn hF
  have hcub : burnsideA315h_cubes F = Subgroup.zpowers (ω ^ 3) := by
    ext x
    rw [burnsideA315h_mem_cubes_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen y)
      refine ⟨k, ?_⟩
      rw [← hk, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    · rintro ⟨k, rfl⟩
      refine ⟨ω ^ k, ?_⟩
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hord : orderOf ω = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hpos : 0 < orderOf ω := orderOf_pos ω
  have h1 := Subgroup.index_mul_card (burnsideA315h_cubes F)
  rw [hcub, Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) h3, ← hord] at h1
  obtain ⟨k, hk⟩ := h3
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at h1
  rw [hcub]
  exact Nat.eq_of_mul_eq_mul_right hk0 h1

noncomputable abbrev burnsideA315h_D (F : Type) [Field F] : Subgroup (MulAut PSL(3, F)) :=
  (burnsideA315h_diagHom F).range

theorem burnsideA315h_inn_le_D {F : Type} [Field F] : psl3InnAut F ≤ burnsideA315h_D F := by
  intro ι hι
  obtain ⟨g, -, rfl⟩ := (burnsideA315h_mem_inn_iff ι).1 hι
  exact ⟨g, rfl⟩

theorem burnsideA315h_D_le_E {F : Type} [Field F] : burnsideA315h_D F ≤ burnsideA315h_E F := by
  rintro _ ⟨g, rfl⟩
  rw [burnsideA315h_mem_E_iff]
  exact ⟨g, 1, by rw [burnsideA315h_field_one, mul_one]; rfl⟩

theorem burnsideA315h_relIndex_inn_D {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) :
    (psl3InnAut F).relIndex (burnsideA315h_D F) = 3 := by
  let θ : GL (Fin 3) F →* Fˣ ⧸ burnsideA315h_cubes F :=
    (QuotientGroup.mk' (burnsideA315h_cubes F)).comp Matrix.GeneralLinearGroup.det
  have hθ : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective _).comp Matrix.GeneralLinearGroup.det_surjective
  have hcomap : Subgroup.comap (burnsideA315h_diagHom F).rangeRestrict
      ((psl3InnAut F).subgroupOf (burnsideA315h_diagHom F).range) = θ.ker := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    show psl3DiagAut g ∈ psl3InnAut F ↔ (QuotientGroup.mk (Matrix.GeneralLinearGroup.det g) :
      Fˣ ⧸ burnsideA315h_cubes F) = 1
    rw [burnsideA315h_diag_mem_inn_iff, QuotientGroup.eq_one_iff]
  unfold Subgroup.relIndex
  rw [← Subgroup.index_comap_of_surjective _
    (MonoidHom.rangeRestrict_surjective (burnsideA315h_diagHom F))]
  show (Subgroup.comap (burnsideA315h_diagHom F).rangeRestrict
      ((psl3InnAut F).subgroupOf (burnsideA315h_diagHom F).range)).index = 3
  rw [hcomap, Subgroup.index_ker, MonoidHom.range_eq_top.2 hθ, Subgroup.card_top,
    ← Subgroup.index_eq_card, burnsideA315h_cubes_index hn hF]

theorem burnsideA315h_relIndex_D_E {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) :
    (burnsideA315h_D F).relIndex (burnsideA315h_E F) = 6 * n := by
  obtain ⟨φ, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 6 * n) hF
  have hfE : ∀ σ : RingAut F, psl3FieldAut σ ∈ burnsideA315h_E F := fun σ => by
    rw [burnsideA315h_mem_E_iff]
    exact ⟨1, σ, by rw [burnsideA315h_diag_one, one_mul]⟩
  let ι : RingAut F → (burnsideA315h_E F) ⧸ (burnsideA315h_D F).subgroupOf (burnsideA315h_E F) :=
    fun σ => QuotientGroup.mk ⟨psl3FieldAut σ, hfE σ⟩
  have hbij : Function.Bijective ι := by
    constructor
    · intro σ σ' h
      have h1 := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at h1
      obtain ⟨g, hg⟩ := h1
      have h2 : psl3DiagAut g⁻¹ * psl3FieldAut (σ⁻¹ * σ') = 1 := by
        rw [burnsideA315h_diag_inv, burnsideA315h_field_mul, burnsideA315h_field_inv]
        have : (burnsideA315h_diagHom F) g = psl3DiagAut g := rfl
        rw [this] at hg
        show (psl3DiagAut g)⁻¹ * ((psl3FieldAut σ)⁻¹ * psl3FieldAut σ') = 1
        have h3 : psl3DiagAut g = (⟨psl3FieldAut σ, hfE σ⟩ : burnsideA315h_E F)⁻¹.1 *
            (⟨psl3FieldAut σ', hfE σ'⟩ : burnsideA315h_E F).1 := hg
        rw [h3]
        simp
      obtain ⟨h4, -⟩ := burnsideA315h_diagfield_eq_one h2
      have : σ⁻¹ * σ' = 1 := h4
      exact inv_mul_eq_one.1 this
    · intro y
      obtain ⟨⟨e, he⟩, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨g, σ, rfl⟩ := (burnsideA315h_mem_E_iff e).1 he
      refine ⟨σ, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      refine ⟨burnsideA315h_gmap σ⁻¹ g, ?_⟩
      show psl3DiagAut (burnsideA315h_gmap σ⁻¹ g) =
        (psl3FieldAut σ)⁻¹ * (psl3DiagAut g * psl3FieldAut σ)
      rw [← burnsideA315h_field_conj σ⁻¹ g, burnsideA315h_field_inv, inv_inv]
      group
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card, ← Nat.card_eq_of_bijective ι hbij, hcard]

theorem burnsideA315h_card_out {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) :
    ∃ a : ℕ, a ≤ 2 ∧
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F)) =
        a * (6 * n) * 3 := by
  refine ⟨(burnsideA315h_E F).index, burnsideA315h_index_E_le, ?_⟩
  have h1 := Subgroup.relIndex_mul_index (burnsideA315h_inn_le_D (F := F))
  have h2 := Subgroup.relIndex_mul_index (burnsideA315h_D_le_E (F := F))
  rw [burnsideA315h_relIndex_inn_D hn hF] at h1
  rw [burnsideA315h_relIndex_D_E hn hF] at h2
  have h3 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F)) =
      (psl3InnAut F).index := (Subgroup.index_eq_card _).symm
  rw [h3, ← h1, ← h2]
  ring


theorem burnsideA315h_pi_field_pow_eq_one_iff {F : Type} [Field F] [Finite F] (σ : RingAut F)
    (k : ℕ) : burnsideA315h_pi F (psl3FieldAut σ) ^ k = 1 ↔ σ ^ k = 1 := by
  rw [← map_pow, burnsideA315h_pi_eq_one_iff]
  have h1 : (psl3FieldAut σ) ^ k = psl3FieldAut (σ ^ k) :=
    ((burnsideA315h_fieldHom F).map_pow σ k).symm
  rw [h1]
  have h := burnsideA315h_diagfield_mem_inn_iff (1 : GL (Fin 3) F) (σ ^ k)
  rw [burnsideA315h_diag_one, one_mul, map_one] at h
  rw [h]
  exact ⟨fun h => h.1, fun h => ⟨h, one_mem _⟩⟩

theorem burnsideA315h_orderOf_pi_field {F : Type} [Field F] [Finite F] (σ : RingAut F) :
    orderOf (burnsideA315h_pi F (psl3FieldAut σ)) = orderOf σ := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, burnsideA315h_pi_field_pow_eq_one_iff]
    exact pow_orderOf_eq_one σ
  · rw [orderOf_dvd_iff_pow_eq_one, ← burnsideA315h_pi_field_pow_eq_one_iff]
    exact pow_orderOf_eq_one _

theorem burnsideA315h_pi_field_central {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} {e : ℕ} (he1 : e % 3 = 1)
    (hσe : ∀ y : F, σ y = y ^ e) :
    burnsideA315h_pi F (psl3FieldAut σ) ∈
      Subgroup.center (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F)) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g, ρ, ε, -, rfl⟩ := burnsideA315h_classification α
  have hc1 : Commute (burnsideA315h_pi F (psl3FieldAut σ))
      (burnsideA315h_pi F (psl3DiagAut g)) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul]
    exact burnsideA315h_pi_field_diag_comm he1 hσe g
  have hc2 : Commute (burnsideA315h_pi F (psl3FieldAut σ))
      (burnsideA315h_pi F (psl3FieldAut ρ)) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, ← burnsideA315h_field_mul, ← burnsideA315h_field_mul,
      burnsideA315h_aut_comm hn hF σ ρ]
  have hc3 : Commute (burnsideA315h_pi F (psl3FieldAut σ))
      (burnsideA315h_pi F (psl3GraphAut)) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, burnsideA315h_graph_comm_field]
  have := ((hc1.mul_right hc2).mul_right (hc3.pow_right ε)).eq
  show burnsideA315h_pi F _ * _ = _ * burnsideA315h_pi F _
  rw [map_mul, map_mul, map_pow]
  exact this.symm

theorem burnsideA315h_orderOf_pi_diag {F : Type} [Field F] [Finite F] {g : GL (Fin 3) F}
    (hg : Matrix.GeneralLinearGroup.det g ∉ burnsideA315h_cubes F) :
    orderOf (burnsideA315h_pi F (psl3DiagAut g)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · rw [← map_pow, burnsideA315h_pi_eq_one_iff]
    have h1 : (psl3DiagAut g) ^ 3 = psl3DiagAut (g ^ 3) :=
      ((burnsideA315h_diagHom F).map_pow g 3).symm
    rw [h1]
    apply burnsideA315h_diag_mem_inn_of_det
    rw [map_pow]
    exact (burnsideA315h_mem_cubes_iff _).2 ⟨_, rfl⟩
  · intro h
    rw [burnsideA315h_pi_eq_one_iff, burnsideA315h_diag_mem_inn_iff] at h
    exact hg h

theorem burnsideA315h_inf_field_diag {F : Type} [Field F] [Finite F] (σ : RingAut F)
    (g : GL (Fin 3) F) :
    Subgroup.zpowers (burnsideA315h_pi F (psl3FieldAut σ)) ⊓
      Subgroup.zpowers (burnsideA315h_pi F (psl3DiagAut g)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Subgroup.mem_inf.1 hz |>.imp Subgroup.mem_zpowers_iff.1
    Subgroup.mem_zpowers_iff.1
  have e1 : psl3FieldAut (σ ^ a) = (psl3FieldAut σ) ^ a :=
    map_zpow (burnsideA315h_fieldHom F) σ a
  have e2 : psl3DiagAut (g ^ b) = (psl3DiagAut g) ^ b := map_zpow (burnsideA315h_diagHom F) g b
  have h1 : burnsideA315h_pi F (psl3FieldAut (σ ^ a)) =
      burnsideA315h_pi F (psl3DiagAut (g ^ b)) := by
    rw [e1, e2, map_zpow, map_zpow, ha, hb]
  have h2 : psl3DiagAut (g ^ (-b)) * psl3FieldAut (σ ^ a) ∈ psl3InnAut F := by
    rw [← burnsideA315h_pi_eq_one_iff, map_mul, h1]
    have e3 : psl3DiagAut (g ^ (-b)) = (psl3DiagAut (g ^ b))⁻¹ := by
      rw [zpow_neg, burnsideA315h_diag_inv]
    rw [e3, map_inv, inv_mul_cancel]
  rw [burnsideA315h_diagfield_mem_inn_iff] at h2
  have h3 : σ ^ a = 1 := h2.1
  rw [← ha, ← map_zpow, ← e1, h3, burnsideA315h_field_one, map_one]

theorem burnsideA315h_pi_inverter {F : Type} [Field F] [Finite F] {φ : RingAut F}
    (hφ : ∀ y : F, φ y = y ^ 2) (g : GL (Fin 3) F) :
    burnsideA315h_pi F (psl3FieldAut φ) * burnsideA315h_pi F (psl3DiagAut g) *
      (burnsideA315h_pi F (psl3FieldAut φ))⁻¹ = (burnsideA315h_pi F (psl3DiagAut g))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, burnsideA315h_field_conj]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, burnsideA315h_pi_eq_one_iff, ← burnsideA315h_diag_mul]
  apply burnsideA315h_diag_mem_inn_of_det
  rw [map_mul, burnsideA315h_det_gmap hφ, burnsideA315h_mem_cubes_iff]
  exact ⟨Matrix.GeneralLinearGroup.det g, by group⟩


theorem burnsideA315h_sylow_abstract {Q : Type*} [Group Q] [Finite Q] {v k a : ℕ} {f d : Q}
    (hcard : Nat.card Q = a * (3 ^ v * k) * 3) (ha : a ≤ 2) (hk : ¬ 3 ∣ k)
    (hf : orderOf f = 3 ^ v) (hd : orderOf d = 3) (hfc : f ∈ Subgroup.center Q)
    (hinf : Subgroup.zpowers f ⊓ Subgroup.zpowers d = ⊥) :
    IsPGroup 3 ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers d) ∧
      ¬ 3 ∣ (Subgroup.zpowers f ⊔ Subgroup.zpowers d).index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : Nat.card (Subgroup.zpowers f) = 3 ^ v := by rw [Nat.card_zpowers, hf]
  have hU : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd]
  have hTp : IsPGroup 3 (Subgroup.zpowers f) := IsPGroup.of_card hT
  have hUp : IsPGroup 3 (Subgroup.zpowers d) := IsPGroup.of_card (n := 1) (by rw [hU]; simp)
  have hTc : Subgroup.zpowers f ≤ Subgroup.center Q := Subgroup.zpowers_le.2 hfc
  haveI hN : (Subgroup.zpowers f).Normal := Subgroup.normal_of_le_center hTc
  have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer ((Subgroup.zpowers f : Subgroup Q) : Set Q) := by
    intro u _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hN.conj_mem h hh u
    · intro hh
      have := hN.conj_mem _ hh u⁻¹
      convert this using 1
      group
  have hS : IsPGroup 3 ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers d) :=
    IsPGroup.to_sup_of_normal_left' hTp hUp hnorm
  refine ⟨hS, ?_⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hS
  let μ : (Subgroup.zpowers f) × (Subgroup.zpowers d) → ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers d) :=
    fun p => ⟨p.1.1 * p.2.1, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hμ : Function.Injective μ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3a : a'⁻¹ * a ∈ Subgroup.zpowers f :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha
    have h3b : a'⁻¹ * a ∈ Subgroup.zpowers d := by
      rw [h2]
      exact Subgroup.mul_mem _ hb' (Subgroup.inv_mem _ hb)
    have h3 : a'⁻¹ * a ∈ Subgroup.zpowers f ⊓ Subgroup.zpowers d := Subgroup.mem_inf.2 ⟨h3a, h3b⟩
    rw [hinf, Subgroup.mem_bot] at h3
    have h4 : a = a' := by
      have := congrArg (a' * ·) h3
      simpa using this
    have h5 : b = b' := by
      rw [h4] at h1
      exact mul_left_cancel h1
    subst h4; subst h5
    rfl
  have hle : 3 ^ v * 3 ≤ Nat.card ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers d) := by
    have := Nat.card_le_card_of_injective μ hμ
    rwa [Nat.card_prod, hT, hU] at this
  rw [hj] at hle
  have hj1 : v + 1 ≤ j := by
    have : 3 ^ (v + 1) ≤ 3 ^ j := by rwa [pow_succ]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hmul := Subgroup.index_mul_card (Subgroup.zpowers f ⊔ Subgroup.zpowers d)
  rw [hj, hcard] at hmul
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  rw [hcard] at hQpos
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hQpos
  have hak : ¬ 3 ∣ a * k := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · exact hk h
  obtain ⟨d', rfl⟩ : ∃ d', j = v + 1 + d' := ⟨j - (v + 1), by omega⟩
  have h3pos : 0 < 3 ^ (v + 1) := by positivity
  have hmul' : (Subgroup.zpowers f ⊔ Subgroup.zpowers d).index * 3 ^ d' = a * k := by
    apply Nat.eq_of_mul_eq_mul_right h3pos
    calc (Subgroup.zpowers f ⊔ Subgroup.zpowers d).index * 3 ^ d' * 3 ^ (v + 1)
        = (Subgroup.zpowers f ⊔ Subgroup.zpowers d).index * 3 ^ (v + 1 + d') := by ring
      _ = a * (3 ^ v * k) * 3 := hmul
      _ = a * k * 3 ^ (v + 1) := by ring
  intro hdiv
  apply hak
  rw [← hmul']
  exact Dvd.dvd.mul_right hdiv _


theorem burnsideA315h_outer_sylow {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) :
    ∃ (fieldGenerator : RingAut F) (diagonalMatrix : GL (Fin 3) F)
        (outerSylow : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F))),
      let outerMap := QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner PSL(3, F))
      let fieldClass := outerMap (psl3FieldAut fieldGenerator)
      let diagonalClass := outerMap (psl3DiagAut diagonalMatrix)
      IsSylowIn 3 outerSylow ⊤ ∧
      orderOf fieldGenerator = 3 ^ ((6 * n).factorization 3) ∧
      orderOf fieldClass = orderOf fieldGenerator ∧ orderOf diagonalClass = 3 ∧
      fieldClass * diagonalClass = diagonalClass * fieldClass ∧
      Subgroup.zpowers fieldClass ⊓ Subgroup.zpowers diagonalClass = ⊥ ∧
      outerSylow = Subgroup.zpowers fieldClass ⊔ Subgroup.zpowers diagonalClass ∧
      (∀ fieldElement ∈ Subgroup.zpowers fieldClass, orderOf fieldElement = 3 →
        fieldElement ∈ Subgroup.center
          (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F))) ∧
      (∃ inverter : RingAut F,
        psl3FieldAut inverter * psl3FieldAut fieldGenerator =
          psl3FieldAut fieldGenerator * psl3FieldAut inverter ∧
        outerMap (psl3FieldAut inverter) * diagonalClass * (outerMap (psl3FieldAut inverter))⁻¹ =
          diagonalClass⁻¹) := by
  obtain ⟨φ, hφ, hord, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 6 * n) hF
  obtain ⟨ω, hM, hgen, h3⟩ := burnsideA315h_gen_data hn hF
  have hω : ω ∉ burnsideA315h_cubes F := burnsideA315h_exists_noncube rfl hgen h3
  obtain ⟨v, hv⟩ : ∃ v, v = (6 * n).factorization 3 := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = 6 * n / 3 ^ v := ⟨_, rfl⟩
  have h3v : 3 ^ v ∣ 6 * n := hv ▸ Nat.ordProj_dvd _ _
  have hn0 : 6 * n ≠ 0 := by omega
  have hfac : 3 ^ v * k = 6 * n := by
    rw [hkdef, hv]; exact Nat.ordProj_mul_ordCompl_eq_self (6 * n) 3
  have hkdvd : k ∣ 6 * n := hkdef ▸ Nat.div_dvd_of_dvd h3v
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hn0 hfac.symm
  have hkn : ¬ 3 ∣ k := by
    rw [hkdef, hv]; exact Nat.not_dvd_ordCompl Nat.prime_three hn0
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : RingAut F, σ₁ = φ ^ k := ⟨_, rfl⟩
  have hσ₁ord : orderOf σ₁ = 3 ^ v := by
    rw [hσ₁, orderOf_pow_of_dvd hk0 (by rw [hord]; exact hkdvd), hord, hkdef]
    exact Nat.div_div_self h3v hn0
  have hkeven : Even k := by
    have he : Even (3 ^ v * k) := by rw [hfac]; exact ⟨3 * n, by ring⟩
    rcases Nat.even_mul.1 he with h | h
    · exfalso
      have : Odd (3 ^ v) := Odd.pow (by decide)
      exact (Nat.not_even_iff_odd.2 this) h
    · exact h
  have he1 : 2 ^ k % 3 = 1 := by
    obtain ⟨m, hm⟩ := hkeven
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hσ₁e : ∀ y : F, σ₁ y = y ^ (2 ^ k) := fun y => by
    rw [hσ₁]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_apply_of_sq hφ _ y
  have hcentral := burnsideA315h_pi_field_central hn hF he1 hσ₁e
  obtain ⟨g₀, hg₀def⟩ : ∃ g₀ : GL (Fin 3) F, g₀ = TauCeti.diagGL ![ω, 1, 1] := ⟨_, rfl⟩
  have hdet : Matrix.GeneralLinearGroup.det g₀ = ω := by
    simp [hg₀def, TauCeti.det_diagGL, Fin.prod_univ_three]
  have hg₀ : Matrix.GeneralLinearGroup.det g₀ ∉ burnsideA315h_cubes F := by
    rw [hdet]; exact hω
  have hdord := burnsideA315h_orderOf_pi_diag hg₀
  have hford : orderOf (burnsideA315h_pi F (psl3FieldAut σ₁)) = 3 ^ v := by
    rw [burnsideA315h_orderOf_pi_field, hσ₁ord]
  have hinf := burnsideA315h_inf_field_diag σ₁ g₀
  obtain ⟨a, ha, hcardOut⟩ := burnsideA315h_card_out hn hF
  have hfin : Finite (MulAut PSL(3, F)) := burnsideA315h_finite_aut F
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F)) :=
    inferInstanceAs (Finite (MulAut PSL(3, F) ⧸ _))
  have hcard' : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL(3, F)) =
      a * (3 ^ v * k) * 3 := by
    rw [hcardOut, hfac]
  obtain ⟨hP, hidx⟩ := burnsideA315h_sylow_abstract hcard' ha hkn hford hdord hcentral hinf
  refine ⟨σ₁, g₀, Subgroup.zpowers (burnsideA315h_pi F (psl3FieldAut σ₁)) ⊔
    Subgroup.zpowers (burnsideA315h_pi F (psl3DiagAut g₀)), ?_⟩
  dsimp only
  refine ⟨⟨le_top, hP, ?_⟩, hv ▸ hσ₁ord, ?_, hdord, ?_, hinf, rfl, ?_, ?_⟩
  · show ¬ 3 ∣ (_ : Subgroup _).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hidx
  · rw [burnsideA315h_orderOf_pi_field]
  · exact (Subgroup.mem_center_iff.1 hcentral _).symm
  · intro z hz _
    exact Subgroup.zpowers_le.2 hcentral hz
  · refine ⟨φ, ?_, ?_⟩
    · rw [← burnsideA315h_field_mul, ← burnsideA315h_field_mul,
        burnsideA315h_aut_comm hn hF]
    · exact burnsideA315h_pi_inverter hφ g₀


theorem burnsideA315h_det_conj {F : Type} [Field F] (X Y : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (X * Y * X⁻¹) = Matrix.GeneralLinearGroup.det Y := by
  rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det X), mul_assoc,
    mul_inv_cancel, mul_one]

theorem burnsideA315h_kappa_form {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {κ : MulAut PSL(3, F)} (hκ : IsPsl3GraphField κ) :
    ∃ (τ : RingAut F) (H : GL (Fin 3) F), orderOf τ = 2 ∧ (∀ y : F, τ y = y ^ 2 ^ (3 * n)) ∧
      κ = psl3DiagAut H * (psl3FieldAut τ * psl3GraphAut) * (psl3DiagAut H)⁻¹ := by
  obtain ⟨hκ2, τ, g₀, hτ, rfl⟩ := hκ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    omega
  have hsq : (psl3DiagAut g₀ * (psl3GraphAut * psl3FieldAut τ)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (psl3DiagAut g₀ * (psl3GraphAut * psl3FieldAut τ))
    rwa [hκ2] at this
  rw [burnsideA315h_graph_comm_field] at hsq ⊢
  have hP : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F g₀ *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F τ *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 3 F) ^ 2 = 1 := by
    have := congrArg (burnsideA315h_Phi F) hsq
    simp only [map_pow, map_mul, burnsideA315h_Phi_diag, burnsideA315h_Phi_field,
      burnsideA315h_Phi_graph, map_one] at this
    rwa [← mul_assoc] at this
  obtain ⟨-, hτy, H, hH⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.odd_linear_graph_field_involution_conjugacy
      Nat.prime_two (by omega : 1 ≤ 6 * n) hF le_rfl g₀ τ hτ1 hP
  refine ⟨τ, H, hτ, fun y => ?_, ?_⟩
  · rw [hτy y, show 6 * n / 2 = 3 * n by omega]
  · apply (burnsideA315h_Phi F).injective
    simp only [map_mul, map_inv, burnsideA315h_Phi_diag, burnsideA315h_Phi_field,
      burnsideA315h_Phi_graph]
    rw [← mul_assoc]
    exact hH

theorem burnsideA315h_diag_normalizes {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g H : GL (Fin 3) F) :
    (psl3Circ σ g).map (MulAut.conj (psl3DiagAut H)).toMonoidHom = psl3Circ σ g := by
  unfold psl3Circ
  rw [burnsideA315h_map_closure_conj, burnsideA315h_closure_eq_comap,
    burnsideA315h_closure_eq_comap]
  have hcomm : psl3DiagAut H * (psl3FieldAut σ * psl3DiagAut g) * (psl3DiagAut H)⁻¹ *
      (psl3FieldAut σ * psl3DiagAut g)⁻¹ =
      psl3DiagAut (H * burnsideA315h_gmap σ (g * H⁻¹ * g⁻¹)) := by
    calc psl3DiagAut H * (psl3FieldAut σ * psl3DiagAut g) * (psl3DiagAut H)⁻¹ *
          (psl3FieldAut σ * psl3DiagAut g)⁻¹
        = psl3DiagAut H * (psl3FieldAut σ * (psl3DiagAut g * (psl3DiagAut H)⁻¹ *
            (psl3DiagAut g)⁻¹) * (psl3FieldAut σ)⁻¹) := by group
      _ = psl3DiagAut H * (psl3FieldAut σ * psl3DiagAut (g * H⁻¹ * g⁻¹) *
            (psl3FieldAut σ)⁻¹) := by
          rw [burnsideA315h_diag_mul, burnsideA315h_diag_mul, burnsideA315h_diag_inv,
            burnsideA315h_diag_inv]
      _ = psl3DiagAut H * psl3DiagAut (burnsideA315h_gmap σ (g * H⁻¹ * g⁻¹)) := by
          rw [burnsideA315h_field_conj]
      _ = _ := by rw [burnsideA315h_diag_mul]
  have hI : psl3DiagAut (H * burnsideA315h_gmap σ (g * H⁻¹ * g⁻¹)) ∈ psl3InnAut F := by
    apply burnsideA315h_diag_mem_inn_of_det
    have h1 := burnsideA315h_gmap_det_div_cube hn hF hσ H
    have h2 := inv_mem h1
    have e : Matrix.GeneralLinearGroup.det (H * burnsideA315h_gmap σ (g * H⁻¹ * g⁻¹)) =
        (Matrix.GeneralLinearGroup.det (burnsideA315h_gmap σ H) *
          (Matrix.GeneralLinearGroup.det H)⁻¹)⁻¹ := by
      have e1 : burnsideA315h_gmap σ (g * H⁻¹ * g⁻¹) =
          burnsideA315h_gmap σ g * (burnsideA315h_gmap σ H)⁻¹ * (burnsideA315h_gmap σ g)⁻¹ := by
        simp only [burnsideA315h_gmap, map_mul, map_inv]
      rw [map_mul, e1, burnsideA315h_det_conj, map_inv, mul_inv_rev, inv_inv]
    rw [e]
    exact h2
  have h3 : burnsideA315h_pi F (psl3DiagAut H * (psl3FieldAut σ * psl3DiagAut g) *
      (psl3DiagAut H)⁻¹) = burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g) := by
    have h4 := (burnsideA315h_pi_eq_one_iff _).2 (hcomm ▸ hI)
    rw [map_mul, map_inv] at h4
    exact mul_inv_eq_one.1 h4
  rw [h3]


theorem burnsideA315h_kappa0_diag {F : Type} [Field F] (τ : RingAut F) (h : GL (Fin 3) F) :
    (psl3FieldAut τ * psl3GraphAut) * psl3DiagAut h * (psl3FieldAut τ * psl3GraphAut)⁻¹ =
      psl3DiagAut (burnsideA315h_gmap τ (Matrix.GeneralLinearGroup.inverseTranspose h)) := by
  have hγ : (psl3GraphAut : MulAut PSL(3, F))⁻¹ = psl3GraphAut :=
    inv_eq_of_mul_eq_one_right (burnsideA315h_graph_sq F)
  calc (psl3FieldAut τ * psl3GraphAut) * psl3DiagAut h * (psl3FieldAut τ * psl3GraphAut)⁻¹
      = psl3FieldAut τ * (psl3GraphAut * psl3DiagAut h * psl3GraphAut) * (psl3FieldAut τ)⁻¹ := by
        rw [mul_inv_rev, hγ]; group
    _ = _ := by rw [burnsideA315h_graph_diag, burnsideA315h_field_conj]

theorem burnsideA315h_kappa0_field {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (τ σ : RingAut F) :
    (psl3FieldAut τ * psl3GraphAut) * psl3FieldAut σ * (psl3FieldAut τ * psl3GraphAut)⁻¹ =
      psl3FieldAut σ := by
  have hγ : (psl3GraphAut : MulAut PSL(3, F))⁻¹ = psl3GraphAut :=
    inv_eq_of_mul_eq_one_right (burnsideA315h_graph_sq F)
  have hcomm : psl3FieldAut τ * psl3FieldAut σ = psl3FieldAut σ * psl3FieldAut τ := by
    rw [← burnsideA315h_field_mul, ← burnsideA315h_field_mul, burnsideA315h_aut_comm hn hF]
  calc (psl3FieldAut τ * psl3GraphAut) * psl3FieldAut σ * (psl3FieldAut τ * psl3GraphAut)⁻¹
      = psl3FieldAut τ * (psl3GraphAut * psl3FieldAut σ * psl3GraphAut) * (psl3FieldAut τ)⁻¹ := by
        rw [mul_inv_rev, hγ]; group
    _ = psl3FieldAut σ := by
        rw [burnsideA315h_graph_field, hcomm]; group

theorem burnsideA315h_conj_conj {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  apply MulEquiv.ext
  intro h
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    MulAut.inv_apply]
  simp

theorem burnsideA315h_map_fixed {F : Type} [Field F] [Finite F] (κ : MulAut PSL(3, F)) :
    (psl3Fixed κ).map (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)) =
      psl3InnAut F ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F))) := by
  ext ι
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    have hy' : κ y = y := hy
    have h1 := burnsideA315h_conj_conj κ y
    rw [hy'] at h1
    calc MulAut.conj y * κ = κ * MulAut.conj y * κ⁻¹ * κ := by rw [h1]
      _ = κ * MulAut.conj y := by group
  · rintro ⟨⟨y, rfl⟩, hc⟩
    refine ⟨y, ?_, rfl⟩
    have h1 := burnsideA315h_conj_conj κ y
    have h2 : MulAut.conj (κ y) = MulAut.conj y := by
      rw [← h1, ← hc]; group
    exact burnsideA315h_conj_injective F h2

theorem burnsideA315h_card_inn_cent {F : Type} [Field F] [Finite F] (κ : MulAut PSL(3, F)) :
    Nat.card ↥(psl3InnAut F ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F)))) =
      Nat.card ↥(psl3Fixed κ) := by
  rw [← burnsideA315h_map_fixed]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (burnsideA315h_conj_injective F)).toEquiv).symm

theorem burnsideA315h_card_three_mul {G Q : Type*} [Group G] [Group Q] (π : G →* Q)
    (T : Subgroup Q) (hT : Nat.card T = 3) (H : Subgroup G) (hH : H ≤ T.comap π) {a : G}
    (haH : a ∈ H) (ha : π a ≠ 1) : Nat.card H = 3 * Nat.card ↥(H ⊓ π.ker) := by
  let πH : ↥H →* Q := π.comp H.subtype
  have hR : πH.range ≤ T := by
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    exact hH hh
  have hdvd : Nat.card πH.range ∣ 3 := hT ▸ Subgroup.card_dvd_of_le hR
  have hne : Nat.card πH.range ≠ 1 := by
    intro h1
    have h2 := Subgroup.eq_bot_of_card_eq _ h1
    apply ha
    have : π a ∈ πH.range := ⟨⟨a, haH⟩, rfl⟩
    rw [h2] at this
    exact (Subgroup.mem_bot.1 this)
  have hR3 : Nat.card πH.range = 3 := ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left hne
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup πH.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange πH).toEquiv, hR3] at h1
  have hker : πH.ker = π.ker.subgroupOf H := by
    ext x
    rfl
  rw [h1, hker, ← Subgroup.inf_subgroupOf_left]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ π.ker ≤ H)).toEquiv]


theorem burnsideA315h_coset_form {F : Type} [Field F] (σ : RingAut F) (g ĝ : GL (Fin 3) F) :
    psl3DiagAut ĝ * (psl3FieldAut σ * psl3DiagAut g) =
      psl3DiagAut (ĝ * burnsideA315h_gmap σ g) * psl3FieldAut σ := by
  rw [burnsideA315h_field_mul_diag, ← mul_assoc, ← burnsideA315h_diag_mul]

theorem burnsideA315h_cube_of_pow {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {u : Fˣ} {k : ℕ} (hk : ¬ 3 ∣ k)
    (h : u ^ k ∈ burnsideA315h_cubes F) : u ∈ burnsideA315h_cubes F := by
  obtain ⟨ω, hM, hgen, h3⟩ := burnsideA315h_gen_data hn hF
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen u)
  rw [← zpow_natCast, ← zpow_mul, burnsideA315h_zpow_mem_cubes_iff rfl hgen h3] at h
  rw [burnsideA315h_zpow_mem_cubes_iff rfl hgen h3]
  rcases Int.prime_three.dvd_or_dvd h with h | h
  · exact h
  · exfalso
    apply hk
    exact_mod_cast h

theorem burnsideA315h_circ_cases {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    {a : MulAut PSL(3, F)} (ha : a ∈ psl3Circ σ g) :
    a ∈ psl3InnAut F ∨ (∃ ι ∈ psl3InnAut F, a = ι * (psl3FieldAut σ * psl3DiagAut g)) ∨
      (∃ ι ∈ psl3InnAut F, a⁻¹ = ι * (psl3FieldAut σ * psl3DiagAut g)) := by
  obtain ⟨hx1, -, hx3⟩ := burnsideA315h_x_facts hn hF hσ g
  have hπ := burnsideA315h_orderOf_pi hx1 hx3
  unfold psl3Circ at ha
  rw [burnsideA315h_closure_eq_comap] at ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 ha)
  set x := psl3FieldAut σ * psl3DiagAut g with hxdef
  have hk3 : (burnsideA315h_pi F x) ^ (k % 3) = burnsideA315h_pi F a := by
    rw [← hk]
    have := zpow_mod_orderOf (burnsideA315h_pi F x) k
    rwa [hπ] at this
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [hr, zpow_zero] at hk3
    exact Or.inl ((burnsideA315h_pi_eq_one_iff a).1 hk3.symm)
  · rw [hr, zpow_one] at hk3
    exact Or.inr (Or.inl (burnsideA315h_mem_coset hk3.symm))
  · rw [hr] at hk3
    have h2 : burnsideA315h_pi F a⁻¹ = burnsideA315h_pi F x := by
      rw [map_inv, ← hk3]
      have h3' : burnsideA315h_pi F x ^ 3 = 1 := by
        have := pow_orderOf_eq_one (burnsideA315h_pi F x)
        rwa [hπ] at this
      calc (burnsideA315h_pi F x ^ (2 : ℤ))⁻¹ = (burnsideA315h_pi F x ^ 2)⁻¹ := by norm_cast
        _ = burnsideA315h_pi F x := by
          rw [inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv, ← pow_succ, h3']
    exact Or.inr (Or.inr (burnsideA315h_mem_coset h2))

theorem burnsideA315h_even_core {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (heven : Even n) {σ : RingAut F} (hσ : orderOf σ = 3)
    {g : GL (Fin 3) F} (hg : psl3DiagAut g ∉ psl3InnAut F) {τ : RingAut F}
    (hτy : ∀ y : F, τ y = y ^ 2 ^ (3 * n)) {b : MulAut PSL(3, F)}
    (hb : ∃ ι ∈ psl3InnAut F, b = ι * (psl3FieldAut σ * psl3DiagAut g))
    (hcomm : (psl3FieldAut τ * psl3GraphAut) * b = b * (psl3FieldAut τ * psl3GraphAut)) :
    False := by
  obtain ⟨ι, hι, rfl⟩ := hb
  obtain ⟨ĝ, hĝ, rfl⟩ := (burnsideA315h_mem_inn_iff ι).1 hι
  rw [burnsideA315h_coset_form] at hcomm
  have hdg : Matrix.GeneralLinearGroup.det g ∉ burnsideA315h_cubes F := by
    rwa [← burnsideA315h_diag_mem_inn_iff]
  have hdg' := burnsideA315h_gmap_noncube hn hF hσ hdg
  set h := ĝ * burnsideA315h_gmap σ g with hh
  have hhd : Matrix.GeneralLinearGroup.det h ∉ burnsideA315h_cubes F := by
    intro hmem
    apply hdg'
    rw [hh, map_mul] at hmem
    have := mul_mem (inv_mem hĝ) hmem
    simpa using this
  have hκ := burnsideA315h_kappa0_diag τ h
  have hκf := burnsideA315h_kappa0_field hn hF τ σ
  have h1 : psl3DiagAut (burnsideA315h_gmap τ (Matrix.GeneralLinearGroup.inverseTranspose h)) *
      psl3FieldAut σ = psl3DiagAut h * psl3FieldAut σ := by
    have e1 : (psl3FieldAut τ * psl3GraphAut) * (psl3DiagAut h * psl3FieldAut σ) *
        (psl3FieldAut τ * psl3GraphAut)⁻¹ = psl3DiagAut h * psl3FieldAut σ := by
      rw [hcomm]; group
    calc psl3DiagAut (burnsideA315h_gmap τ (Matrix.GeneralLinearGroup.inverseTranspose h)) *
          psl3FieldAut σ
        = ((psl3FieldAut τ * psl3GraphAut) * psl3DiagAut h * (psl3FieldAut τ * psl3GraphAut)⁻¹) *
          ((psl3FieldAut τ * psl3GraphAut) * psl3FieldAut σ *
            (psl3FieldAut τ * psl3GraphAut)⁻¹) := by rw [hκ, hκf]
      _ = (psl3FieldAut τ * psl3GraphAut) * (psl3DiagAut h * psl3FieldAut σ) *
          (psl3FieldAut τ * psl3GraphAut)⁻¹ := by group
      _ = psl3DiagAut h * psl3FieldAut σ := e1
  have h2 := mul_right_cancel h1
  have h3 : psl3DiagAut (h⁻¹ * burnsideA315h_gmap τ (Matrix.GeneralLinearGroup.inverseTranspose h)) *
      psl3FieldAut (1 : RingAut F) = 1 := by
    rw [burnsideA315h_field_one, mul_one, burnsideA315h_diag_mul, burnsideA315h_diag_inv, h2,
      inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := burnsideA315h_diagfield_eq_one h3
  have hdet := congrArg Matrix.GeneralLinearGroup.det hc
  rw [Matrix.GeneralLinearGroup.det_scalar, map_mul, map_inv,
    burnsideA315h_det_gmap hτy, burnsideA315h_det_invT] at hdet
  have hcube : ((Matrix.GeneralLinearGroup.det h) ^ (1 + 2 ^ (3 * n)))⁻¹ ∈
      burnsideA315h_cubes F := by
    rw [burnsideA315h_mem_cubes_iff]
    refine ⟨c, ?_⟩
    rw [← inv_pow, pow_add, pow_one]
    simpa using hdet.symm
  have hk : ¬ 3 ∣ (1 + 2 ^ (3 * n)) := by
    obtain ⟨m, hm⟩ := heven
    rw [hm, show 3 * (m + m) = 6 * m by ring, pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
      Nat.pow_mod]
    norm_num
  exact hhd (burnsideA315h_cube_of_pow hn hF hk ((inv_mem_iff).1 hcube))


theorem burnsideA315h_conj_mem_circ {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) (g H : GL (Fin 3) F)
    {a : MulAut PSL(3, F)} (ha : a ∈ psl3Circ σ g) :
    psl3DiagAut H * a * (psl3DiagAut H)⁻¹ ∈ psl3Circ σ g := by
  have h := burnsideA315h_diag_normalizes hn hF hσ g H
  have : psl3DiagAut H * a * (psl3DiagAut H)⁻¹ ∈
      (psl3Circ σ g).map (MulAut.conj (psl3DiagAut H)).toMonoidHom := ⟨a, ha, rfl⟩
  rwa [h] at this

theorem burnsideA315h_inn_le_circ {F : Type} [Field F] (σ : RingAut F) (g : GL (Fin 3) F) :
    psl3InnAut F ≤ psl3Circ σ g :=
  fun _ hι => Subgroup.subset_closure (Or.inl hι)

theorem burnsideA315h_even_case {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (heven : Even n) {σ : RingAut F} (hσ : orderOf σ = 3)
    {g : GL (Fin 3) F} (hg : psl3DiagAut g ∉ psl3InnAut F) {κ : MulAut PSL(3, F)}
    (hκ : IsPsl3GraphField κ) :
    psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F))) =
      psl3InnAut F ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F))) := by
  apply le_antisymm
  · intro a ha
    rw [Subgroup.mem_inf] at ha ⊢
    obtain ⟨haA, haC⟩ := ha
    refine ⟨?_, haC⟩
    obtain ⟨τ, H, -, hτy, hκeq⟩ := burnsideA315h_kappa_form hn hF hκ
    rw [Subgroup.mem_centralizer_singleton_iff] at haC
    have hu : (psl3DiagAut H)⁻¹ = psl3DiagAut H⁻¹ := (burnsideA315h_diag_inv H).symm
    have ha' : (psl3DiagAut H)⁻¹ * a * psl3DiagAut H ∈ psl3Circ σ g := by
      have := burnsideA315h_conj_mem_circ hn hF hσ g H⁻¹ haA
      rwa [← hu, inv_inv] at this
    have hκ0 : (psl3FieldAut τ * psl3GraphAut) =
        (psl3DiagAut H)⁻¹ * κ * psl3DiagAut H := by
      rw [hκeq]; group
    have hcomm : (psl3FieldAut τ * psl3GraphAut) * ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H) =
        ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H) * (psl3FieldAut τ * psl3GraphAut) := by
      calc (psl3FieldAut τ * psl3GraphAut) * ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)
          = (psl3DiagAut H)⁻¹ * (κ * a) * psl3DiagAut H := by rw [hκ0]; group
        _ = (psl3DiagAut H)⁻¹ * (a * κ) * psl3DiagAut H := by rw [haC]
        _ = _ := by rw [hκ0]; group
    have hcommInv : (psl3FieldAut τ * psl3GraphAut) *
        ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹ =
        ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹ * (psl3FieldAut τ * psl3GraphAut) := by
      calc (psl3FieldAut τ * psl3GraphAut) * ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹
          = ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹ *
            (((psl3DiagAut H)⁻¹ * a * psl3DiagAut H) * (psl3FieldAut τ * psl3GraphAut)) *
            ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹ := by group
        _ = ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹ *
            ((psl3FieldAut τ * psl3GraphAut) * ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)) *
            ((psl3DiagAut H)⁻¹ * a * psl3DiagAut H)⁻¹ := by rw [hcomm]
        _ = _ := by group
    have hI : (psl3DiagAut H)⁻¹ * a * psl3DiagAut H ∈ psl3InnAut F := by
      rcases burnsideA315h_circ_cases hn hF hσ g ha' with h | h | h
      · exact h
      · exact (burnsideA315h_even_core hn hF heven hσ hg hτy h hcomm).elim
      · exact (burnsideA315h_even_core hn hF heven hσ hg hτy h hcommInv).elim
    have := (burnsideA315h_inn_normal F).conj_mem _ hI (psl3DiagAut H)
    convert this using 1
    group
  · exact inf_le_inf_right _ (burnsideA315h_inn_le_circ σ g)


theorem burnsideA315h_kappa0_fix_B {F : Type} [Field F] {τ : RingAut F} {q : ℕ}
    (hτy : ∀ y : F, τ y = y ^ q) {β : Fˣ} (hβ : β ^ (q + 1) = 1) :
    burnsideA315h_gmap τ
      (Matrix.GeneralLinearGroup.inverseTranspose (TauCeti.diagGL ![β, 1, 1])) =
      TauCeti.diagGL ![β, 1, 1] := by
  rw [TauCeti.inverseTranspose_diagGL, burnsideA315h_gmap, TauCeti.map_diagGL]
  have h1 : (β : F) ^ (q + 1) = 1 := by
    have := congrArg Units.val hβ
    simpa using this
  have h2 : (β : F) ^ q * β = 1 := by rw [← pow_succ]; exact h1
  have hβinv : Units.map ((τ : F →+* F) : F →* F) β⁻¹ = β := by
    apply Units.ext
    rw [Units.coe_map, Units.val_inv_eq_inv_val]
    show τ ((β : F)⁻¹) = β
    rw [map_inv₀, hτy]
    exact inv_eq_of_mul_eq_one_right h2
  congr 1
  funext i
  fin_cases i
  · simpa using hβinv
  · simp
  · simp

theorem burnsideA315h_det_diagB {F : Type} [Field F] (β : Fˣ) :
    Matrix.GeneralLinearGroup.det (TauCeti.diagGL ![β, 1, 1] : GL (Fin 3) F) = β := by
  simp [TauCeti.det_diagGL, Fin.prod_univ_three]

theorem burnsideA315h_odd_exists {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (hodd : Odd n) {σ : RingAut F} (hσ : orderOf σ = 3)
    {g : GL (Fin 3) F} (hg : psl3DiagAut g ∉ psl3InnAut F) {κ : MulAut PSL(3, F)}
    (hκ : IsPsl3GraphField κ) :
    ∃ a ∈ psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F))),
      a ∉ psl3InnAut F := by
  obtain ⟨τ, H, -, hτy, hκeq⟩ := burnsideA315h_kappa_form hn hF hκ
  obtain ⟨ω, hM, hgen, h3⟩ := burnsideA315h_gen_data hn hF
  have hdg : Matrix.GeneralLinearGroup.det g ∉ burnsideA315h_cubes F := by
    rwa [← burnsideA315h_diag_mem_inn_iff]
  have hq3 : 2 ^ (3 * n) % 3 = 2 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, show 3 * (2 * m + 1) = 3 * 2 * m + 3 by ring, pow_add, pow_mul, Nat.mul_mod,
      Nat.pow_mod]
    norm_num
  have hqM : orderOf ω + 1 = (2 ^ (3 * n)) ^ 2 := by
    have h42 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [hM, h42, ← pow_mul, ← pow_mul]
    congr 1
    ring
  obtain ⟨β₀, hβ₀, hβ₀nc⟩ :=
    burnsideA315h_exists_normone_noncube (F := F) rfl hgen h3 hqM hq3
  obtain ⟨β, hβ, hβc⟩ : ∃ β : Fˣ, β ^ (2 ^ (3 * n) + 1) = 1 ∧
      (Matrix.GeneralLinearGroup.det g)⁻¹ * β ∈ burnsideA315h_cubes F := by
    rcases burnsideA315h_cube_dichotomy rfl hgen h3 hdg hβ₀nc with h | h
    · exact ⟨β₀, hβ₀, by rw [mul_comm]; exact h⟩
    · refine ⟨β₀⁻¹, by rw [inv_pow, hβ₀, inv_one], ?_⟩
      have := inv_mem h
      rwa [mul_inv_rev] at this
  let B : GL (Fin 3) F := TauCeti.diagGL ![β, 1, 1]
  have hdetB : Matrix.GeneralLinearGroup.det B = β := burnsideA315h_det_diagB β
  have hπ : burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut B) =
      burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g) := by
    have h1 : psl3DiagAut (g⁻¹ * B) ∈ psl3InnAut F := by
      apply burnsideA315h_diag_mem_inn_of_det
      rw [map_mul, map_inv, hdetB]
      exact hβc
    have : psl3DiagAut B = psl3DiagAut g * psl3DiagAut (g⁻¹ * B) := by
      rw [← burnsideA315h_diag_mul]; congr 1; group
    rw [this, ← mul_assoc, map_mul, (burnsideA315h_pi_eq_one_iff _).2 h1, mul_one]
  obtain ⟨hx1, -, hx3⟩ := burnsideA315h_x_facts hn hF hσ g
  have ha₀A : psl3FieldAut σ * psl3DiagAut B ∈ psl3Circ σ g := by
    unfold psl3Circ
    rw [burnsideA315h_closure_eq_comap, Subgroup.mem_comap, hπ]
    exact Subgroup.mem_zpowers _
  have ha₀I : psl3FieldAut σ * psl3DiagAut B ∉ psl3InnAut F := by
    rw [← burnsideA315h_pi_eq_one_iff, hπ, burnsideA315h_pi_eq_one_iff]
    exact hx1
  have hκ0 := burnsideA315h_kappa0_diag τ B
  have hκf := burnsideA315h_kappa0_field hn hF τ σ
  rw [burnsideA315h_kappa0_fix_B hτy hβ] at hκ0
  have ha₀C : (psl3FieldAut τ * psl3GraphAut) * (psl3FieldAut σ * psl3DiagAut B) =
      (psl3FieldAut σ * psl3DiagAut B) * (psl3FieldAut τ * psl3GraphAut) := by
    have e1 : (psl3FieldAut τ * psl3GraphAut) * (psl3FieldAut σ * psl3DiagAut B) *
        (psl3FieldAut τ * psl3GraphAut)⁻¹ = psl3FieldAut σ * psl3DiagAut B := by
      calc (psl3FieldAut τ * psl3GraphAut) * (psl3FieldAut σ * psl3DiagAut B) *
            (psl3FieldAut τ * psl3GraphAut)⁻¹
          = ((psl3FieldAut τ * psl3GraphAut) * psl3FieldAut σ * (psl3FieldAut τ * psl3GraphAut)⁻¹) *
            ((psl3FieldAut τ * psl3GraphAut) * psl3DiagAut B * (psl3FieldAut τ * psl3GraphAut)⁻¹) := by
            group
        _ = psl3FieldAut σ * psl3DiagAut B := by rw [hκf, hκ0]
    calc (psl3FieldAut τ * psl3GraphAut) * (psl3FieldAut σ * psl3DiagAut B)
        = ((psl3FieldAut τ * psl3GraphAut) * (psl3FieldAut σ * psl3DiagAut B) *
          (psl3FieldAut τ * psl3GraphAut)⁻¹) * (psl3FieldAut τ * psl3GraphAut) := by group
      _ = _ := by rw [e1]
  refine ⟨psl3DiagAut H * (psl3FieldAut σ * psl3DiagAut B) * (psl3DiagAut H)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_inf]
    refine ⟨burnsideA315h_conj_mem_circ hn hF hσ g H ha₀A, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hκeq]
    calc psl3DiagAut H * (psl3FieldAut σ * psl3DiagAut B) * (psl3DiagAut H)⁻¹ *
          (psl3DiagAut H * (psl3FieldAut τ * psl3GraphAut) * (psl3DiagAut H)⁻¹)
        = psl3DiagAut H * ((psl3FieldAut σ * psl3DiagAut B) * (psl3FieldAut τ * psl3GraphAut)) *
          (psl3DiagAut H)⁻¹ := by group
      _ = psl3DiagAut H * ((psl3FieldAut τ * psl3GraphAut) * (psl3FieldAut σ * psl3DiagAut B)) *
          (psl3DiagAut H)⁻¹ := by rw [ha₀C]
      _ = _ := by group
  · intro hI
    apply ha₀I
    have := (burnsideA315h_inn_normal F).conj_mem _ hI (psl3DiagAut H)⁻¹
    convert this using 1
    group


open scoped Matrix in
theorem burnsideA315h_mat_mu {F : Type} [Field F] {τ : RingAut F} (hτ2 : ∀ x, τ (τ x) = x)
    {M T : Matrix (Fin 3) (Fin 3) F} (hTM : T * M = 1) {r : F} (hr0 : r ≠ 0)
    (hr : (Tᵀ).map τ = r • M) :
    CFSG.LieType.Universal.Unitary.conjTr τ M * M = (τ r)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) ∧
      τ ((τ r)⁻¹) = (τ r)⁻¹ := by
  have hτr0 : τ r ≠ 0 := (map_ne_zero τ).2 hr0
  have h1 : T = τ r • CFSG.LieType.Universal.Unitary.conjTr τ M := by
    have h := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => (Xᵀ).map τ) hr
    have e1 : (((Tᵀ).map τ)ᵀ).map τ = T := by
      ext i j
      simp [hτ2]
    rw [e1] at h
    rw [h]
    ext i j
    simp [CFSG.LieType.Universal.Unitary.conjTr]
  have h2 : CFSG.LieType.Universal.Unitary.conjTr τ M * M =
      (τ r)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have h3 : τ r • (CFSG.LieType.Universal.Unitary.conjTr τ M * M) = 1 := by
      rw [← Matrix.smul_mul, ← h1, hTM]
    rw [← h3, smul_smul, inv_mul_cancel₀ hτr0, one_smul]
  refine ⟨h2, ?_⟩
  have h4 : CFSG.LieType.Universal.Unitary.conjTr τ (CFSG.LieType.Universal.Unitary.conjTr τ M * M) =
      CFSG.LieType.Universal.Unitary.conjTr τ M * M := by
    rw [CFSG.LieType.Universal.Unitary.conjTr_mul,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjTr_conjTr hτ2]
  rw [h2, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjTr_smul,
    CFSG.LieType.Universal.Unitary.conjTr_one] at h4
  have := congrFun (congrFun h4 0) 0
  simpa using this


def burnsideA315h_slOfSU {F : Type} [Field F] {τ : RingAut F}
    (A : CFSG.LieType.Universal.Unitary.SUid τ 3) : SL(3, F) :=
  ⟨(A.1 : Matrix (Fin 3) (Fin 3) F), (CFSG.LieType.Universal.Unitary.mem_SUid.1 A.2).1⟩

noncomputable def burnsideA315h_suHom {F : Type} [Field F] (τ : RingAut F) :
    CFSG.LieType.Universal.Unitary.SUid τ 3 →* PSL(3, F) where
  toFun A := QuotientGroup.mk (burnsideA315h_slOfSU A)
  map_one' := by
    have : burnsideA315h_slOfSU (1 : CFSG.LieType.Universal.Unitary.SUid τ 3) = 1 :=
      Subtype.ext rfl
    rw [this]
    exact QuotientGroup.mk_one _
  map_mul' A B := by
    have : burnsideA315h_slOfSU (A * B) = burnsideA315h_slOfSU A * burnsideA315h_slOfSU B :=
      Subtype.ext rfl
    rw [this]
    exact QuotientGroup.mk_mul _ _ _

theorem burnsideA315h_kappa0_mk {F : Type} [Field F] (τ : RingAut F) (s : SL(3, F)) :
    (psl3FieldAut τ * psl3GraphAut : MulAut PSL(3, F)) (QuotientGroup.mk s : PSL(3, F)) =
      QuotientGroup.mk (slField τ (slGraph s)) := by
  rw [MulAut.mul_apply]
  unfold psl3GraphAut psl3FieldAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_pslOfSL_mk]

open scoped Matrix in
theorem burnsideA315h_star_coe {F : Type} [Field F] (τ : RingAut F) (s : SL(3, F)) :
    ((slField τ (slGraph s) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ).map τ) := rfl

open scoped Matrix in
theorem burnsideA315h_suHom_fixed {F : Type} [Field F] {τ : RingAut F}
    (hτ2 : ∀ x, τ (τ x) = x) (A : CFSG.LieType.Universal.Unitary.SUid τ 3) :
    (psl3FieldAut τ * psl3GraphAut : MulAut PSL(3, F)) (burnsideA315h_suHom τ A) =
      burnsideA315h_suHom τ A := by
  show (psl3FieldAut τ * psl3GraphAut : MulAut PSL(3, F))
      (QuotientGroup.mk (burnsideA315h_slOfSU A) : PSL(3, F)) =
    QuotientGroup.mk (burnsideA315h_slOfSU A)
  rw [burnsideA315h_kappa0_mk]
  congr 1
  set s := burnsideA315h_slOfSU A with hs
  apply Subtype.ext
  rw [burnsideA315h_star_coe]
  have hT : ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hT' : (s : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hU := (CFSG.LieType.Universal.Unitary.mem_SUid.1 A.2).2
  have hC : CFSG.LieType.Universal.Unitary.conjTr τ (s : Matrix (Fin 3) (Fin 3) F) =
      ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    calc CFSG.LieType.Universal.Unitary.conjTr τ (s : Matrix (Fin 3) (Fin 3) F)
        = CFSG.LieType.Universal.Unitary.conjTr τ (s : Matrix (Fin 3) (Fin 3) F) *
          ((s : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) := by
          rw [hT', Matrix.mul_one]
      _ = (CFSG.LieType.Universal.Unitary.conjTr τ (s : Matrix (Fin 3) (Fin 3) F) *
          (s : Matrix (Fin 3) (Fin 3) F)) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc]
      _ = _ := by
          have : CFSG.LieType.Universal.Unitary.conjTr τ (s : Matrix (Fin 3) (Fin 3) F) *
              (s : Matrix (Fin 3) (Fin 3) F) = 1 := hU
          rw [this, Matrix.one_mul]
  rw [← hC]
  ext i j
  simp [CFSG.LieType.Universal.Unitary.conjTr, hτ2]


open scoped Matrix in
theorem burnsideA315h_fixed_suHom {F : Type} [Field F] {τ : RingAut F}
    (hτ2 : ∀ x, τ (τ x) = x) {x : PSL(3, F)}
    (hx : (psl3FieldAut τ * psl3GraphAut : MulAut PSL(3, F)) x = x) :
    ∃ A : CFSG.LieType.Universal.Unitary.SUid τ 3, burnsideA315h_suHom τ A = x := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  rw [burnsideA315h_kappa0_mk] at hx
  have h1 := QuotientGroup.eq.1 hx.symm
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h1
  rw [Fintype.card_fin] at hr3
  set M : Matrix (Fin 3) (Fin 3) F := (s : Matrix (Fin 3) (Fin 3) F) with hM
  set T : Matrix (Fin 3) (Fin 3) F := ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hT
  have hTM : T * M = 1 := by
    rw [hT, hM, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hMT : M * T = 1 := by
    rw [hT, hM, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, burnsideA315h_star_coe] at hr
  have hS : (Tᵀ).map τ = r • M := by
    calc (Tᵀ).map τ = (M * T) * ((Tᵀ).map τ) := by rw [hMT, Matrix.one_mul]
      _ = M * (T * ((Tᵀ).map τ)) := Matrix.mul_assoc _ _ _
      _ = M * Matrix.scalar (Fin 3) r := by rw [hr]
      _ = r • M := by
          ext i j
          simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr3
  obtain ⟨hμ, hτμ⟩ := burnsideA315h_mat_mu hτ2 hTM hr0 hS
  set μ := (τ r)⁻¹ with hμdef
  have hμ3 : μ ^ 3 = 1 := by
    rw [hμdef, inv_pow, ← map_pow, hr3, map_one, inv_one]
  have hμ0 : μ ≠ 0 := by
    rw [hμdef]
    exact inv_ne_zero ((map_ne_zero τ).2 hr0)
  let μu : Fˣ := Units.mk0 μ hμ0
  let A : GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.scalar (Fin 3) μu * Matrix.SpecialLinearGroup.toGL s
  have hAmat : (A : Matrix (Fin 3) (Fin 3) F) = μ • M := by
    show (Matrix.GeneralLinearGroup.scalar (Fin 3) μu : Matrix (Fin 3) (Fin 3) F) *
      ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = μ • M
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul, μu, hM]
  have hAdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [hAmat, Matrix.det_smul, Fintype.card_fin, hM, s.2, hμ3, mul_one]
  have hAunit : CFSG.LieType.Universal.Unitary.conjTr τ (A : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hAmat, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjTr_smul, Matrix.smul_mul,
      Matrix.mul_smul, hμ, smul_smul, smul_smul, hτμ]
    have h3 : μ * μ * μ = 1 := by
      calc μ * μ * μ = μ ^ 3 := by ring
        _ = 1 := hμ3
    rw [h3, one_smul]
  have hAmem : A ∈ CFSG.LieType.Universal.Unitary.SUid τ 3 := ⟨hAdet, hAunit⟩
  refine ⟨⟨A, hAmem⟩, ?_⟩
  show QuotientGroup.mk (burnsideA315h_slOfSU ⟨A, hAmem⟩) = QuotientGroup.mk s
  apply (QuotientGroup.eq.2 ?_).symm
  apply Matrix.SpecialLinearGroup.mem_center_iff.2
  refine ⟨μ, by rw [Fintype.card_fin]; exact hμ3, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show Matrix.scalar (Fin 3) μ = T * (A : Matrix (Fin 3) (Fin 3) F)
  rw [hAmat, Matrix.mul_smul, hTM]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]


theorem burnsideA315h_suHom_ker {F : Type} [Field F] (τ : RingAut F) :
    (burnsideA315h_suHom τ).ker =
      (StatedScalars (Fin 3) F).subgroupOf (CFSG.LieType.Universal.Unitary.SUid τ 3) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show (QuotientGroup.mk (burnsideA315h_slOfSU A) : PSL(3, F)) = 1 ↔
    (A.1 ∈ StatedScalars (Fin 3) F)
  rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr3, hr⟩
    rw [Fintype.card_fin] at hr3
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr3
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hr
  · rintro ⟨c, hc⟩
    refine ⟨(c : F), ?_, ?_⟩
    · rw [Fintype.card_fin]
      have := congrArg Matrix.GeneralLinearGroup.det hc
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at this
      have h2 : (A.1 : GL (Fin 3) F).val.det = 1 := (CFSG.LieType.Universal.Unitary.mem_SUid.1 A.2).1
      have h3 : ((Matrix.GeneralLinearGroup.det A.1 : Fˣ) : F) = 1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]; exact h2
      rw [← this] at h3
      simpa using h3
    · have := congrArg (fun X : GL (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
      exact this

theorem burnsideA315h_fixed_equiv {F : Type} [Field F] [Finite F] {τ : RingAut F}
    (hτ2 : ∀ x, τ (τ x) = x) :
    Nonempty (↥(psl3Fixed (psl3FieldAut τ * psl3GraphAut)) ≃*
      StatedProj (CFSG.LieType.Universal.Unitary.SUid τ 3)) := by
  have hrange : (burnsideA315h_suHom τ).range = psl3Fixed (psl3FieldAut τ * psl3GraphAut) := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact burnsideA315h_suHom_fixed hτ2 A
    · intro hx
      obtain ⟨A, hA⟩ := burnsideA315h_fixed_suHom hτ2 hx
      exact ⟨A, hA⟩
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (burnsideA315h_suHom_ker τ)))⟩

theorem burnsideA315h_fixed_conj {F : Type} [Field F] (κ₀ β : MulAut PSL(3, F)) :
    Nonempty (↥(psl3Fixed (β * κ₀ * β⁻¹)) ≃* ↥(psl3Fixed κ₀)) := by
  have h : psl3Fixed (β * κ₀ * β⁻¹) = (psl3Fixed κ₀).map β.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv]
    show (β * κ₀ * β⁻¹) y = y ↔ κ₀ (β.symm y) = β.symm y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
    constructor
    · intro h
      have := congrArg β.symm h
      simpa using this
    · intro h
      rw [h]
      simp
  exact ⟨(MulEquiv.subgroupCongr h).trans
    (Subgroup.equivMapOfInjective _ _ β.injective).symm⟩

theorem burnsideA315h_admissible {n : ℕ} (hn : 1 ≤ n) : StatedLieAdmissible .PSU 3 2 (3 * n) := by
  refine ⟨Nat.prime_two, by omega, ?_⟩
  show 3 ≤ 3 ∧ (3, 2 ^ (3 * n)) ≠ (3, 2)
  refine ⟨le_rfl, ?_⟩
  intro h
  have h2 : 2 ^ (3 * n) = 2 ^ 1 := (Prod.mk.inj h).2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

theorem burnsideA315h_isPSU {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {κ : MulAut PSL(3, F)} (hκ : IsPsl3GraphField κ) :
    CFSG.Quasithin.IsPSLEps3 false 2 (3 * n) ↥(psl3Fixed κ) := by
  obtain ⟨τ, H, hτ, hτy, hκeq⟩ := burnsideA315h_kappa_form hn hF hκ
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    have h2 : τ ^ 2 = 1 := by
      have := pow_orderOf_eq_one τ
      rwa [hτ] at this
    have := congrArg (fun φ : RingAut F => φ x) h2
    simpa [pow_two] using this
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 6 * n) hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Nat.card F = (2 ^ (3 * n)) ^ 2 := by
    rw [hF, ← pow_mul]; congr 1; ring
  have hτU : τ = CFSG.LieType.BorelTits.unitaryInvolution F 2 (3 * n) := by
    apply RingEquiv.ext
    intro y
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hτy]
  have hSU : CFSG.LieType.Universal.Unitary.SUid τ 3 = StatedSU 3 (2 ^ (3 * n)) F := by
    rw [hτU]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF' 3
  obtain ⟨e1⟩ := burnsideA315h_fixed_conj (psl3FieldAut τ * psl3GraphAut) (psl3DiagAut H)
  obtain ⟨e2⟩ := burnsideA315h_fixed_equiv hτ2
  rw [hSU] at e2
  rw [hκeq]
  refine ⟨burnsideA315h_admissible hn, F, inferInstance, inferInstance, hF', ⟨e1.trans e2⟩⟩


theorem burnsideA315h_odd_card {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) (hodd : Odd n) {σ : RingAut F} (hσ : orderOf σ = 3)
    {g : GL (Fin 3) F} (hg : psl3DiagAut g ∉ psl3InnAut F) {κ : MulAut PSL(3, F)}
    (hκ : IsPsl3GraphField κ) :
    Nat.card ↥(psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F)))) =
      3 * Nat.card ↥(psl3Fixed κ) := by
  obtain ⟨hx1, -, hx3⟩ := burnsideA315h_x_facts hn hF hσ g
  have hπ := burnsideA315h_orderOf_pi hx1 hx3
  obtain ⟨a, ha, haI⟩ := burnsideA315h_odd_exists hn hF hodd hσ hg hκ
  have hT : Nat.card (Subgroup.zpowers
      (burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g))) = 3 := by
    rw [Nat.card_zpowers, hπ]
  have hH : psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F))) ≤
      (Subgroup.zpowers (burnsideA315h_pi F (psl3FieldAut σ * psl3DiagAut g))).comap
        (burnsideA315h_pi F) := by
    intro y hy
    have h1 := (Subgroup.mem_inf.1 hy).1
    unfold psl3Circ at h1
    rwa [burnsideA315h_closure_eq_comap] at h1
  have h2 := burnsideA315h_card_three_mul (burnsideA315h_pi F) _ hT _ hH ha
    (fun h => haI ((burnsideA315h_pi_eq_one_iff a).1 h))
  rw [h2]
  have hker : (psl3Circ σ g ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F)))) ⊓
      (burnsideA315h_pi F).ker =
      psl3InnAut F ⊓ Subgroup.centralizer ({κ} : Set (MulAut PSL(3, F))) := by
    rw [burnsideA315h_ker_pi]
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hi⟩
      exact ⟨hi, hc⟩
    · rintro ⟨hi, hc⟩
      exact ⟨⟨burnsideA315h_inn_le_circ σ g hi, hc⟩, hi⟩
  rw [hker, burnsideA315h_card_inn_cent]

theorem as_A_3_16 : A_3_16 := by
  intro n hn F _ _ hF
  refine ⟨burnsideA315h_outer_sylow hn hF, ?_⟩
  intro σ σ' g g' hσ hσ' hg hg'
  refine ⟨burnsideA315h_card_circ hn hF hσ g, burnsideA315h_circ_iso hn hF hσ hσ' hg hg',
    burnsideA315h_nonsplit hn hF hσ hg, burnsideA315h_isL3Circ_true hn hF hσ hg, ?_⟩
  intro κ hκ
  refine ⟨burnsideA315h_isPSU hn hF hκ, ?_, ?_, ?_⟩
  · intro a ha h3
    exact burnsideA315h_order_three_mem_inn hn hF hσ hg a (Subgroup.mem_inf.1 ha).1 h3
  · intro hodd
    exact ⟨burnsideA315h_odd_card hn hF hodd hσ hg hκ,
      burnsideA315h_isL3Circ_false hn hF hodd hσ hg hκ⟩
  · intro heven
    exact burnsideA315h_even_case hn hF heven hσ hg hκ

end CFSG.ASVolI

