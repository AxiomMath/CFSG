module

public import CFSG.Quasithin.Background.SimsG44Levi
public import CFSG.Quasithin.Background.SimsG45Basis
public import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

open Matrix CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

section Transvections

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] noncomputable def symplTransv (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (w : V) (μ : F) : V ≃ₗ[F] V :=
  LinearEquiv.transvection (f := μ • B.flip w) (v := w)
    (show μ • B w w = 0 by rw [halt, smul_zero])

variable (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)

theorem symplTransv_apply (w : V) (μ : F) (v : V) :
    symplTransv B halt w μ v = v + (μ * B v w) • w :=
  rfl

theorem symplTransv_mul (w : V) (μ ν : F) :
    symplTransv B halt w μ * symplTransv B halt w ν = symplTransv B halt w (μ + ν) := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, symplTransv_apply, symplTransv_apply, symplTransv_apply,
    LinearMap.map_add₂, LinearMap.map_smul₂, halt w, smul_eq_mul, mul_zero, add_zero]
  module

theorem symplTransv_coeff_zero (w : V) : symplTransv B halt w 0 = 1 :=
  LinearEquiv.ext fun v => by rw [symplTransv_apply, zero_mul, zero_smul, add_zero]; rfl

theorem symplTransv_center_zero (μ : F) : symplTransv B halt 0 μ = 1 :=
  LinearEquiv.ext fun v => by rw [symplTransv_apply, smul_zero, add_zero]; rfl

theorem symplTransv_inv (w : V) (μ : F) :
    (symplTransv B halt w μ)⁻¹ = symplTransv B halt w (-μ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [symplTransv_mul, add_neg_cancel, symplTransv_coeff_zero]

theorem symplTransv_mem_spGroup (w : V) (μ : F) : symplTransv B halt w μ ∈ spGroup B := by
  intro x y
  change B (symplTransv B halt w μ x) (symplTransv B halt w μ y) = B x y
  rw [symplTransv_apply, symplTransv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt w]
  rw [SimsG45.bilin_skew B halt w y]
  ring

variable (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include hnd

theorem commSpace_symplTransv {w : V} (hw : w ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    commSpace (symplTransv B halt w μ) = F ∙ w := by
  ext x
  change x ∈ LinearMap.range ((symplTransv B halt w μ : V →ₗ[F] V) - LinearMap.id) ↔ _
  simp only [LinearMap.mem_range, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    symplTransv_apply, add_sub_cancel_left, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y₀, hy₀⟩ := SimsG45.exists_pair_eq_one B halt hnd hw
    refine ⟨(a / μ) • y₀, ?_⟩
    rw [LinearMap.map_smul₂, hy₀, smul_eq_mul, mul_one]
    congr 1
    field_simp

theorem symplTransv_isTransv {w : V} (hw : w ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    IsTransv (symplTransv B halt w μ) := by
  refine ⟨?_, ?_⟩
  · have h := commSpace_symplTransv B halt hnd hw hμ
    rw [commSpace] at h
    rw [h, finrank_span_singleton hw]
  · refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      symplTransv_apply, add_sub_cancel_left, LinearMap.zero_apply, LinearMap.map_smul₂, halt w,
      smul_eq_mul, mul_zero, zero_smul]

end Transvections

section Stabilizer

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def vecStab (B : LinearMap.BilinForm F V) (u : V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ spGroup B ∧ g u = u}
  mul_mem' := fun {g h} hg hh =>
    ⟨(spGroup B).mul_mem hg.1 hh.1, by rw [LinearEquiv.mul_apply, hh.2, hg.2]⟩
  one_mem' := ⟨(spGroup B).one_mem, rfl⟩
  inv_mem' := fun {g} hg => ⟨(spGroup B).inv_mem hg.1, by
    have h : (g⁻¹ * g) u = u := by rw [inv_mul_cancel]; rfl
    rwa [LinearEquiv.mul_apply, hg.2] at h⟩

theorem mem_vecStab {B : LinearMap.BilinForm F V} {u : V} {g : V ≃ₗ[F] V} :
    g ∈ vecStab B u ↔ g ∈ spGroup B ∧ g u = u :=
  Iff.rfl

variable (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
  (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include halt hnd

theorem apply_eq_of_commute {d : V ≃ₗ[F] V} {u : V} {c : F} (hc : c ≠ 0)
    (hdv : ∀ v, d v = v + (c * B v u) • u) {e : V ≃ₗ[F] V} (he : e ∈ spGroup B)
    (heT : IsTransv e) (hed : e * d = d * e) : e u = u := by
  obtain ⟨w, hw, μ, hμ, hev, -⟩ := SimsG45.exists_transv_form B halt hnd e he heT.1
  have hwu : B w u = 0 := (SimsG45.transv_commute_iff B halt hnd hw hμ hc hev hdv).mp hed
  rw [hev, SimsG45.bilin_skew B halt u w, hwu, neg_zero, mul_zero, zero_smul, add_zero]

theorem xHat_le_vecStab {d : V ≃ₗ[F] V} {u : V} {c : F} (hc : c ≠ 0)
    (hdv : ∀ v, d v = v + (c * B v u) • u) : xHat B d ≤ vecStab B u := by
  rw [xHat, Subgroup.closure_le]
  rintro e ⟨he, heT, hed⟩
  exact ⟨he, apply_eq_of_commute B halt hnd hc hdv he heT hed⟩

theorem symplTransv_mem_xHat {d : V ≃ₗ[F] V} {u : V} {c : F} (hc : c ≠ 0)
    (hdv : ∀ v, d v = v + (c * B v u) • u) {w : V} (hwu : B w u = 0) (μ : F) :
    symplTransv B halt w μ ∈ xHat B d := by
  by_cases hw : w = 0
  · rw [hw, symplTransv_center_zero]
    exact one_mem _
  by_cases hμ : μ = 0
  · rw [hμ, symplTransv_coeff_zero]
    exact one_mem _
  exact Subgroup.subset_closure ⟨symplTransv_mem_spGroup B halt w μ,
    symplTransv_isTransv B halt hnd hw hμ,
    (SimsG45.transv_commute_iff B halt hnd hw hμ hc (symplTransv_apply B halt w μ) hdv).mpr hwu⟩

end Stabilizer

section Basis

open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (exists_symplectic_basis_prescribed_pair)

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include halt hnd

theorem exists_sympBasis_zero (hdim : Module.finrank F V = 4) {u : V} (hu : u ≠ 0) :
    ∃ b : Module.Basis (Fin 4) F V,
      (∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) ∧ b 0 = u := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  have halt' : LinearMap.IsAlt B := halt
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => halt'.eq_iff.mp (hy x)⟩
  have hsymm : ∀ x y, B y x = B x y := fun x y => by
    rw [← halt'.neg x y, CharTwo.neg_eq]
  obtain ⟨y, hy⟩ := SimsG45.exists_pair_eq_one B halt hnd hu
  have huy : B u y = 1 := by rw [hsymm]; exact hy
  obtain ⟨m, cb, hfin, h1, h2, h3, hc0, -⟩ :=
    exists_symplectic_basis_prescribed_pair B halt' hnd' u y huy
  have hm : m = 1 := by omega
  subst hm
  have h4 : ∀ i j, B (cb (Sum.inr i)) (cb (Sum.inl j)) = if j = i then 1 else 0 := fun i j => by
    rw [hsymm]
    exact h3 j i
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → V,
      e = ![cb (Sum.inl 0), cb (Sum.inl 1), cb (Sum.inr 1), cb (Sum.inr 0)] := ⟨_, rfl⟩
  have hgram : ∀ i j, B (e i) (e j) = if i.val + j.val = 3 then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he, h1, h2, h3, h4]
  have hli : LinearIndependent F e := SimsG45.linearIndependent_of_antidiag B hgram
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim]), fun i j => ?_, ?_⟩
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact hgram i j
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank, he]
    simpa using hc0

end Basis

section Matrices

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (b : Module.Basis (Fin 4) F V)
  (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0)

omit [CharP F 2] in
theorem symplTransv_mem_isometryGroup (w : V) (μ : F) :
    symplTransv B halt w μ ∈
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
  (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff B _).mpr
    (symplTransv_mem_spGroup B halt w μ)

omit [CharP F 2] in
theorem mat_isoAntiSp (g : V ≃ₗ[F] V)
    (hg : g ∈ CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B)
    (i j : Fin 4) : mat (SimsG45.isoAntiSp B b hb ⟨g, hg⟩) i j = b.repr (g (b j)) i := by
  change LinearMap.toMatrix b b g.toLinearMap i j = _
  rw [LinearMap.toMatrix_apply]
  rfl

omit [CharP F 2] in
theorem mat_isoAntiSp_symplTransv (w : V) (μ : F)
    (hI : symplTransv B halt w μ ∈
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B) (i j : Fin 4) :
    mat (SimsG45.isoAntiSp B b hb ⟨symplTransv B halt w μ, hI⟩) i j =
      (if j = i then 1 else 0) + μ * B (b j) w * b.repr w i := by
  rw [mat_isoAntiSp, symplTransv_apply, map_add, map_smul, b.repr_self, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]

theorem isoAntiSp_symplTransv_zero (μ : F) (hI) :
    SimsG45.isoAntiSp B b hb ⟨symplTransv B halt (b 0) μ, hI⟩ = aElt 0 μ := by
  refine antiSp_ext (Matrix.ext fun i j => ?_)
  change mat _ i j = mat _ i j
  rw [mat_isoAntiSp_symplTransv, mat_aElt]
  fin_cases i <;> fin_cases j <;> simp [hb, uMat, Finsupp.single_apply]

theorem isoAntiSp_symplTransv_one (μ : F) (hI) :
    SimsG45.isoAntiSp B b hb ⟨symplTransv B halt (b 1) μ, hI⟩ = sElt (slUpper μ) := by
  refine antiSp_ext (Matrix.ext fun i j => ?_)
  change mat _ i j = mat _ i j
  rw [mat_isoAntiSp_symplTransv, mat_sElt]
  fin_cases i <;> fin_cases j <;> simp [hb, sMat, slUpper, Finsupp.single_apply]

theorem isoAntiSp_symplTransv_two (μ : F) (hI) :
    SimsG45.isoAntiSp B b hb ⟨symplTransv B halt (b 2) μ, hI⟩ = sElt (slLower μ) := by
  refine antiSp_ext (Matrix.ext fun i j => ?_)
  change mat _ i j = mat _ i j
  rw [mat_isoAntiSp_symplTransv, mat_sElt]
  fin_cases i <;> fin_cases j <;> simp [hb, sMat, slLower, Finsupp.single_apply]

theorem isoAntiSp_symplTransv_zero_one (s : F) (hI) :
    SimsG45.isoAntiSp B b hb ⟨symplTransv B halt (b 0 + s • b 1) 1, hI⟩ =
      aElt ![s, 0] 1 * sElt (slUpper (s ^ 2)) := by
  refine antiSp_ext (Matrix.ext fun i j => ?_)
  change mat _ i j = mat _ i j
  rw [mat_isoAntiSp_symplTransv, mat_mul, mat_aElt, mat_sElt]
  fin_cases i <;> fin_cases j <;>
    simp [hb, uMat, sMat, slUpper, Finsupp.single_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem isoAntiSp_symplTransv_zero_two (s : F) (hI) :
    SimsG45.isoAntiSp B b hb ⟨symplTransv B halt (b 0 + s • b 2) 1, hI⟩ =
      aElt ![0, s] 1 * sElt (slLower (s ^ 2)) := by
  refine antiSp_ext (Matrix.ext fun i j => ?_)
  change mat _ i j = mat _ i j
  rw [mat_isoAntiSp_symplTransv, mat_mul, mat_aElt, mat_sElt]
  fin_cases i <;> fin_cases j <;>
    simp [hb, uMat, sMat, slLower, Finsupp.single_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem isoAntiSp_mem_rootC₂_iff (g : V ≃ₗ[F] V)
    (hg : g ∈ CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B) :
    SimsG45.isoAntiSp B b hb ⟨g, hg⟩ ∈ rootC₂ F ↔ g (b 0) = b 0 := by
  rw [mem_centralizer_rootU₂_iff]
  simp only [FirstCol, mat_isoAntiSp]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h0⟩
    refine b.ext_elem fun i => ?_
    rw [b.repr_self]
    fin_cases i <;> simp [h0, h1, h2, h3, Finsupp.single_apply]
  · intro h
    rw [h, b.repr_self]
    simp [Finsupp.single_apply]

end Matrices

section Generation

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
  (b : Module.Basis (Fin 4) F V)
  (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0)

include halt hnd hb in
theorem xHat_eq_vecStab {d : V ≃ₗ[F] V} {u : V} (hb0 : b 0 = u) {c : F} (hc : c ≠ 0)
    (hdv : ∀ v, d v = v + (c * B v u) • u) : xHat B d = vecStab B u := by
  refine le_antisymm (xHat_le_vecStab B halt hnd hc hdv) fun g hg => ?_
  obtain ⟨hgSp, hgu⟩ := mem_vecStab.mp hg
  have hgI : g ∈ CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff B g).mpr hgSp
  have hC : SimsG45.isoAntiSp B b hb ⟨g, hgI⟩ ∈ rootC₂ F :=
    (isoAntiSp_mem_rootC₂_iff B b hb g hgI).mpr (by rw [hb0]; exact hgu)
  have hmem : ∀ w : V, B w u = 0 → ∀ (μ : F) (A : antiSp F),
      SimsG45.isoAntiSp B b hb ⟨symplTransv B halt w μ, symplTransv_mem_isometryGroup B halt w μ⟩
        = A →
      A ∈ ((xHat B d).subgroupOf
        (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B)).map
          (SimsG45.isoAntiSp B b hb).toMonoidHom := by
    intro w hwu μ A hA
    exact ⟨⟨_, symplTransv_mem_isometryGroup B halt w μ⟩,
      symplTransv_mem_xHat B halt hnd hc hdv hwu μ, hA⟩
  have hB0 : B (b 0) u = 0 := by rw [← hb0, hb]; simp
  have hB1 : B (b 1) u = 0 := by rw [← hb0, hb]; simp
  have hB2 : B (b 2) u = 0 := by rw [← hb0, hb]; simp
  have hle := rootC₂_le_of_mem
    (H := ((xHat B d).subgroupOf
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B)).map
        (SimsG45.isoAntiSp B b hb).toMonoidHom)
    (fun μ => hmem _ hB0 μ _ (isoAntiSp_symplTransv_zero B halt b hb μ _))
    (fun μ => hmem _ hB1 μ _ (isoAntiSp_symplTransv_one B halt b hb μ _))
    (fun μ => hmem _ hB2 μ _ (isoAntiSp_symplTransv_two B halt b hb μ _))
    (fun s => hmem _ (by rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hB0,
      hB1, smul_zero, add_zero]) 1 _ (isoAntiSp_symplTransv_zero_one B halt b hb s _))
    (fun s => hmem _ (by rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hB0,
      hB2, smul_zero, add_zero]) 1 _ (isoAntiSp_symplTransv_zero_two B halt b hb s _))
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp (hle hC)
  have hyg' : y = ⟨g, hgI⟩ := (SimsG45.isoAntiSp B b hb).injective hyg
  rw [hyg'] at hy
  exact Subgroup.mem_subgroupOf.mp hy

end Generation

section Transport

@[expose] def subgroupEquivOfIff {G G' : Type*} [Group G] [Group G'] {I : Subgroup G}
    (e : ↥I ≃* G') {X : Subgroup G} {Y : Subgroup G'} (hXI : X ≤ I)
    (hXY : ∀ (g : G) (hg : g ∈ I), g ∈ X ↔ e ⟨g, hg⟩ ∈ Y) : ↥X ≃* ↥Y where
  toFun g := ⟨e ⟨g, hXI g.2⟩, (hXY g (hXI g.2)).mp g.2⟩
  invFun y := ⟨(e.symm y : G), (hXY _ (e.symm y).2).mpr (by simpa using y.2)⟩
  left_inv g := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change e ⟨(g : G) * h, _⟩ = e ⟨g, _⟩ * e ⟨h, _⟩
    rw [← map_mul]
    rfl)

theorem mem_center_iff_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    g ∈ Subgroup.center G ↔ e g ∈ Subgroup.center H := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h x]
  · intro h x
    apply e.injective
    rw [map_mul, map_mul, h (e x)]

end Transport

section RootGroup

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)

include hnd in
theorem mem_rootGroupHat_iff {d : V ≃ₗ[F] V} {u : V} (hu : u ≠ 0) (hcomm : commSpace d = F ∙ u)
    (g : V ≃ₗ[F] V) : g ∈ rootGroupHat B d ↔ ∃ μ : F, g = symplTransv B halt u μ := by
  let R : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {g | ∃ μ : F, g = symplTransv B halt u μ}
      mul_mem' := by
        rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
        exact ⟨μ + ν, symplTransv_mul B halt u μ ν⟩
      one_mem' := ⟨0, (symplTransv_coeff_zero B halt u).symm⟩
      inv_mem' := by
        rintro _ ⟨μ, rfl⟩
        exact ⟨-μ, symplTransv_inv B halt u μ⟩ }
  constructor
  · intro hg
    have hle : rootGroupHat B d ≤ R := by
      rw [rootGroupHat, Subgroup.closure_le]
      rintro e ⟨he, heT, hec⟩
      obtain ⟨w, -, μ, -, hev, hrange⟩ := SimsG45.exists_transv_form B halt hnd e he heT.1
      have hwu : F ∙ w = F ∙ u := hrange.symm.trans (hec.trans hcomm)
      have hw : w ∈ F ∙ u := hwu ▸ Submodule.mem_span_singleton_self w
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
      refine ⟨μ * a * a, LinearEquiv.ext fun v => ?_⟩
      rw [hev, symplTransv_apply, ← ha, LinearMap.map_smul, smul_eq_mul]
      module
    exact hle hg
  · rintro ⟨μ, rfl⟩
    by_cases hμ : μ = 0
    · rw [hμ, symplTransv_coeff_zero]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨symplTransv_mem_spGroup B halt u μ,
        symplTransv_isTransv B halt hnd hu hμ,
        by rw [commSpace_symplTransv B halt hnd hu hμ, hcomm]⟩

end RootGroup

section Parabolic

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def pointStab (B : LinearMap.BilinForm F V) (u : V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ spGroup B ∧ (F ∙ u).map (g : V →ₗ[F] V) = F ∙ u}
  mul_mem' := fun {g h} hg hh => ⟨(spGroup B).mul_mem hg.1 hh.1, by
    rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, hh.2, hg.2]⟩
  one_mem' := ⟨(spGroup B).one_mem, by rw [LinearEquiv.coe_toLinearMap_one, Submodule.map_id]⟩
  inv_mem' := fun {g} hg => ⟨(spGroup B).inv_mem hg.1, by
    conv_lhs => rw [← hg.2]
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← LinearEquiv.coe_toLinearMap_mul,
      inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]⟩

variable (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)

include halt in
theorem isMaximalSymplecticParabolic_pointStab {u : V} (hu : u ≠ 0) :
    IsMaximalSymplecticParabolic B (pointStab B u) := by
  refine ⟨F ∙ u, Or.inl (finrank_span_singleton hu), ?_, fun g => Iff.rfl⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [halt]

theorem pointStab_apply_self {u v₀ : V} (hv₀ : B v₀ u = 1) {g : V ≃ₗ[F] V}
    (hg : g ∈ pointStab B u) : g u = B v₀ (g u) • u := by
  obtain ⟨a, ha⟩ : ∃ a : F, a • u = g u := by
    have h : g u ∈ (F ∙ u).map (g : V →ₗ[F] V) :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u)
    rw [hg.2] at h
    exact Submodule.mem_span_singleton.mp h
  rw [← ha, map_smul, hv₀, smul_eq_mul, mul_one]

@[expose] noncomputable def pointScalar {u v₀ : V} (hv₀ : B v₀ u = 1) : ↥(pointStab B u) →* F where
  toFun g := B v₀ ((g : V ≃ₗ[F] V) u)
  map_one' := hv₀
  map_mul' g h := by
    change B v₀ ((g : V ≃ₗ[F] V) ((h : V ≃ₗ[F] V) u)) =
      B v₀ ((g : V ≃ₗ[F] V) u) * B v₀ ((h : V ≃ₗ[F] V) u)
    obtain ⟨a, ha⟩ : ∃ a : F, (h : V ≃ₗ[F] V) u = a • u := ⟨_, pointStab_apply_self B hv₀ h.2⟩
    obtain ⟨c, hc⟩ : ∃ c : F, (g : V ≃ₗ[F] V) u = c • u := ⟨_, pointStab_apply_self B hv₀ g.2⟩
    rw [ha, map_smul, hc, map_smul, map_smul, map_smul, hv₀]
    simp only [smul_eq_mul, mul_one, mul_comm]

theorem pointScalar_eq_one_iff {u v₀ : V} (hv₀ : B v₀ u = 1) (g : ↥(pointStab B u)) :
    pointScalar B hv₀ g = 1 ↔ (g : V ≃ₗ[F] V) u = u := by
  change B v₀ ((g : V ≃ₗ[F] V) u) = 1 ↔ _
  constructor
  · intro h
    rw [pointStab_apply_self B hv₀ g.2, h, one_smul]
  · intro h
    rw [h, hv₀]

theorem mem_pointStab_of_apply_eq {u : V} {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) (hgu : g u = u) :
    g ∈ pointStab B u := by
  refine ⟨hg, ?_⟩
  rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hgu]

variable [Finite F] [CharP F 2] (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
  (b : Module.Basis (Fin 4) F V) (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0)

include halt hnd hb in
theorem xHat_eq_twoPrimeResidualOf {d : V ≃ₗ[F] V} {u : V} (hu : u ≠ 0) (hb0 : b 0 = u) {c : F}
    (hc : c ≠ 0) (hdv : ∀ v, d v = v + (c * B v u) • u) :
    xHat B d = twoPrimeResidualOf (pointStab B u) := by
  have hX := xHat_eq_vecStab B halt hnd b hb hb0 hc hdv
  obtain ⟨v₀, hv₀⟩ := SimsG45.exists_pair_eq_one B halt hnd hu
  set χ := (pointScalar B hv₀).toHomUnits with hχ
  have hker : (xHat B d).subgroupOf (pointStab B u) = χ.ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, hX, mem_vecStab, MonoidHom.mem_ker, Units.ext_iff,
      MonoidHom.coe_toHomUnits, Units.val_one, pointScalar_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
  have hodd : Odd χ.ker.index := by
    rw [Subgroup.index_ker]
    have h1 : Nat.card χ.range ∣ Nat.card Fˣ := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_units] at h1
    refine Odd.of_dvd_nat ?_ h1
    have hpos : 0 < Nat.card F := Nat.card_pos
    obtain ⟨k, hk⟩ := two_dvd_natCard F
    exact ⟨k - 1, by omega⟩
  apply le_antisymm
  · rw [xHat, twoPrimeResidualOf, Subgroup.closure_le]
    rintro e ⟨he, heT, hed⟩
    have heQ : e ∈ pointStab B u :=
      mem_pointStab_of_apply_eq B he (apply_eq_of_commute B halt hnd hc hdv he heT hed)
    refine Subgroup.mem_map.mpr ⟨⟨e, heQ⟩, ?_, rfl⟩
    rw [twoPrimeResidual, Subgroup.mem_sInf]
    rintro N ⟨hN, k, hk⟩
    have hpow := Subgroup.pow_index_mem N ⟨e, heQ⟩
    obtain ⟨w, -, μ, -, hev, -⟩ := SimsG45.exists_transv_form B halt hnd e he heT.1
    have hee : e * e = 1 := SimsG45.transv_mul_self B halt hev
    have hee' : (⟨e, heQ⟩ : ↥(pointStab B u)) ^ 2 = 1 := Subtype.ext (by simp [pow_two, hee])
    rwa [hk, pow_succ, pow_mul, hee', one_pow, one_mul] at hpow
  · rw [twoPrimeResidualOf, Subgroup.map_le_iff_le_comap]
    apply sInf_le
    refine ⟨?_, ?_⟩
    · change ((xHat B d).subgroupOf (pointStab B u)).Normal
      rw [hker]
      exact χ.normal_ker
    · change Odd ((xHat B d).subgroupOf (pointStab B u)).index
      rw [hker]
      exact hodd

end Parabolic

section Main

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
  (b : Module.Basis (Fin 4) F V) (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0)

@[expose] noncomputable def xHatEquiv {d : V ≃ₗ[F] V} {u : V} (hb0 : b 0 = u) {c : F} (hc : c ≠ 0)
    (hdv : ∀ v, d v = v + (c * B v u) • u) : ↥(xHat B d) ≃* ↥(rootC₂ F) :=
  subgroupEquivOfIff (SimsG45.isoAntiSp B b hb) (X := xHat B d) (Y := rootC₂ F)
    (fun g hg => (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
      B g).mpr (xHat_le_vecStab B halt hnd hc hdv hg).1)
    (fun g hg => by
      rw [xHat_eq_vecStab B halt hnd b hb hb0 hc hdv, mem_vecStab,
        isoAntiSp_mem_rootC₂_iff B b hb g hg, hb0]
      exact ⟨fun h => h.2, fun h =>
        ⟨(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
          B g).mp hg, h⟩⟩)

include halt hnd hb in
theorem center_xHat {d : V ≃ₗ[F] V} {u : V} (hu : u ≠ 0) (hb0 : b 0 = u) {c : F} (hc : c ≠ 0)
    (hdv : ∀ v, d v = v + (c * B v u) • u) (hcomm : commSpace d = F ∙ u) :
    Subgroup.center ↥(xHat B d) = (rootGroupHat B d).subgroupOf (xHat B d) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_rootGroupHat_iff B halt hnd hu hcomm,
    mem_center_iff_of_mulEquiv (xHatEquiv B halt hnd b hb hb0 hc hdv), center_rootC₂,
    Subgroup.mem_subgroupOf]
  change SimsG45.isoAntiSp B b hb ⟨g, _⟩ ∈ rootU₂ F ↔ _
  have h1 : ∀ μ : F, SimsG45.isoAntiSp B b hb
      ⟨symplTransv B halt (b 0) μ, symplTransv_mem_isometryGroup B halt (b 0) μ⟩ =
        uElt 0 0 μ 0 := fun μ => by
    rw [isoAntiSp_symplTransv_zero, aElt_zero]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    have h2 := (SimsG45.isoAntiSp B b hb).injective (hμ.trans (h1 μ).symm)
    rw [← hb0]
    exact congrArg Subtype.val h2
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [← h1 μ]
    congr 1
    exact Subtype.ext (by rw [hμ, hb0])

end Main

theorem g44_xHat {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (d : V ≃ₗ[F] V) (hdSp : d ∈ spGroup B) (hdT : IsTransv d) :
    (∃ φ : ↥(xHat B d) →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 ↥(xHat B d) ∧
        ∃ ψ : ↥(CFSG.pCore 2 ↥(xHat B d)) ≃* Multiplicative (Fin 3 → F),
          ∀ (g : ↥(xHat B d)) (x y : ↥(CFSG.pCore 2 ↥(xHat B d))),
            g * (x : ↥(xHat B d)) * g⁻¹ = (y : ↥(xHat B d)) →
              Multiplicative.toAdd (ψ y) = orthAct (φ g) (Multiplicative.toAdd (ψ x))) ∧
      Subgroup.center ↥(xHat B d) = (rootGroupHat B d).subgroupOf (xHat B d) ∧
      ∃ Qhat : Subgroup (V ≃ₗ[F] V), IsMaximalSymplecticParabolic B Qhat ∧
        xHat B d = twoPrimeResidualOf Qhat := by
  obtain ⟨u, hu, c, hc, hdv, hcomm⟩ := SimsG45.exists_transv_form B halt hnd d hdSp hdT.1
  obtain ⟨b, hb, hb0⟩ := exists_sympBasis_zero B halt hnd hdim hu
  exact ⟨c2_levi_structure (xHatEquiv B halt hnd b hb hb0 hc hdv),
    center_xHat B halt hnd b hb hu hb0 hc hdv hcomm,
    pointStab B u, isMaximalSymplecticParabolic_pointStab B halt hu,
    xHat_eq_twoPrimeResidualOf B halt hnd b hb hu hb0 hc hdv⟩

end CFSG.Quasithin.SimsG4
