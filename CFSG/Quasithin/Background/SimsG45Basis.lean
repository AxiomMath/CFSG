module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.Quasithin.SimsG45

open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.UnbalancedCatalog

variable {F : Type} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem linearIndependent_pair_of_span_ne {u w : V} (huw : F ∙ u ≠ F ∙ w) (hu : u ≠ 0)
    (hw : w ≠ 0) : LinearIndependent F ![u, w] := by
  rw [LinearIndependent.pair_iff' hu]
  intro a ha
  refine huw ?_
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw (by rw [← ha, zero_smul])
  rw [← ha, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha0)]

theorem exists_pairing {ι : Type*} [Fintype ι] [FiniteDimensional F V] (B : BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {v : ι → V}
    (hv : LinearIndependent F v) (a : ι → F) : ∃ x, ∀ i, B x (v i) = a i := by
  have halt' : LinearMap.IsAlt B := halt
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => halt'.eq_iff.mp (hy x)⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr F a)
  refine ⟨(B.toDual hnd').symm g, fun i => ?_⟩
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  have h1 := LinearMap.congr_fun hg (Module.Basis.span hv i)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.constr_basis] at h1
  exact h1

theorem linearIndependent_of_antidiag (B : BilinForm F V) {e : Fin 4 → V}
    (hb : ∀ i j, B (e i) (e j) = if i.val + j.val = 3 then 1 else 0) :
    LinearIndependent F e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have key : ∀ j, ∑ i, g i * B (e i) (e j) = 0 := fun j => by
    simpa [map_sum, map_smul] using congrArg (fun x => B x (e j)) hg
  fin_cases i
  · simpa [Fin.sum_univ_four, hb] using key 3
  · simpa [Fin.sum_univ_four, hb] using key 2
  · simpa [Fin.sum_univ_four, hb] using key 1
  · simpa [Fin.sum_univ_four, hb] using key 0

theorem transv_prod_formula [CharP F 2] (B : BilinForm F V) {u w b₀ b₁ : V} {s r t c d : F}
    (ht : t * s = 1) (hc : c = s * s) (hd : d = r * r)
    (hu : u = t • b₀ + r • b₁) (hw : w = s • b₁) (v : V) :
    v + (c * B v u) • u + (d * B v w) • w =
      v + (B v b₀ + s * r * B v b₁) • b₀ + (s * r * B v b₀) • b₁ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  subst hu hw hc hd
  simp only [map_add, map_smul, smul_eq_mul]
  generalize B v b₀ = p
  generalize B v b₁ = q
  have e1 : s * s * (t * p + r * q) * t = p + s * r * q := by
    linear_combination (p * (t * s + 1) + s * r * q) * ht
  have e2 : s * s * (t * p + r * q) * r + r * r * (s * q) * s = s * r * p := by
    linear_combination (s * r * p) * ht + (s ^ 2 * r ^ 2 * q) * h2
  calc v + (s * s * (t * p + r * q)) • (t • b₀ + r • b₁) + (r * r * (s * q)) • (s • b₁)
      = v + (s * s * (t * p + r * q) * t) • b₀ +
          (s * s * (t * p + r * q) * r + r * r * (s * q) * s) • b₁ := by module
    _ = v + (p + s * r * q) • b₀ + (s * r * p) • b₁ := by rw [e1, e2]

theorem exists_adapted_basis [Finite F] [CharP F 2] (B : BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) {u w : V} (huw : F ∙ u ≠ F ∙ w) (hu : u ≠ 0) (hw : w ≠ 0)
    (hBuw : B u w = 0) {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ (b : Module.Basis (Fin 4) F V) (β : F), β ≠ 0 ∧
      (∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) ∧
      ∀ j, b j + (c * B (b j) u) • u + (d * B (b j) w) • w =
        ∑ i, (SpChain.uMat (0 : F) β 1 0) i j • b i := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have halt' : LinearMap.IsAlt B := halt
  have hsymm : ∀ x y, B y x = B x y := fun x y => by
    rw [← halt'.neg x y, CharTwo.neg_eq]
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' c
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' d
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hs)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hd (by simpa using hr)
  have ht : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : V, b₀ = s • u + r • w := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : V, b₁ = s⁻¹ • w := ⟨_, rfl⟩
  have hw' : w = s • b₁ := by rw [hb₁, smul_inv_smul₀ hs0]
  have hu' : u = s⁻¹ • b₀ + r • b₁ := by
    have : s⁻¹ • b₀ + r • b₁ = (s⁻¹ * s) • u + ((2 : F) * (s⁻¹ * r)) • w := by
      rw [hb₀, hb₁]
      module
    rw [this, ht, h2, zero_mul, zero_smul, add_zero, one_smul]
  have p01 : B b₀ b₁ = 0 := by simp [hb₀, hb₁, hBuw, halt]
  have hli01 : LinearIndependent F ![b₀, b₁] := by
    have hli := linearIndependent_pair_of_span_ne huw hu hw
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro a b hab
    have hab' : (a * s) • u + (a * r + b * s⁻¹) • w = 0 := by
      rw [hb₀, hb₁] at hab
      exact (by module : (a * s) • u + (a * r + b * s⁻¹) • w =
        a • (s • u + r • w) + b • s⁻¹ • w).trans hab
    obtain ⟨h1, h2'⟩ := hli _ _ hab'
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hs0
    refine ⟨ha, ?_⟩
    rw [ha, zero_mul, zero_add] at h2'
    rcases mul_eq_zero.mp h2' with h | h
    · exact h
    · exact absurd h (inv_ne_zero hs0)
  obtain ⟨b₃, hb₃⟩ := exists_pairing B halt hnd hli01 ![1, 0]
  have p30 : B b₃ b₀ = 1 := by simpa using hb₃ 0
  have p31 : B b₃ b₁ = 0 := by simpa using hb₃ 1
  obtain ⟨y, hy⟩ := exists_pairing B halt hnd hli01 ![0, 1]
  have py0 : B y b₀ = 0 := by simpa using hy 0
  have py1 : B y b₁ = 1 := by simpa using hy 1
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : V, b₂ = y + B y b₃ • b₀ := ⟨_, rfl⟩
  have p20 : B b₂ b₀ = 0 := by simp [hb₂, py0, halt]
  have p21 : B b₂ b₁ = 1 := by simp [hb₂, py1, p01]
  have p23 : B b₂ b₃ = 0 := by
    rw [hb₂, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hsymm b₃ b₀, p30, mul_one]
    exact CharTwo.add_self_eq_zero _
  have p02 : B b₀ b₂ = 0 := by rw [hsymm b₂ b₀, p20]
  have p03 : B b₀ b₃ = 1 := by rw [hsymm b₃ b₀, p30]
  have p10 : B b₁ b₀ = 0 := by rw [hsymm b₀ b₁, p01]
  have p12 : B b₁ b₂ = 1 := by rw [hsymm b₂ b₁, p21]
  have p13 : B b₁ b₃ = 0 := by rw [hsymm b₃ b₁, p31]
  have p32 : B b₃ b₂ = 0 := by rw [hsymm b₂ b₃, p23]
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → V, e = ![b₀, b₁, b₂, b₃] := ⟨_, rfl⟩
  have hgram : ∀ i j, B (e i) (e j) = if i.val + j.val = 3 then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [he, halt, p01, p02, p03, p10, p12, p13, p20, p21, p23, p30, p31, p32]
  have hli : LinearIndependent F e := linearIndependent_of_antidiag B hgram
  obtain ⟨b, hbe⟩ : ∃ b : Module.Basis (Fin 4) F V, ⇑b = e :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim]),
      coe_basisOfLinearIndependentOfCardEqFinrank hli _⟩
  refine ⟨b, s * r, mul_ne_zero hs0 hr0, fun i j => by rw [hbe]; exact hgram i j, fun j => ?_⟩
  rw [hbe, transv_prod_formula B ht hs hr hu' hw' (e j)]
  fin_cases j <;>
    simp [Fin.sum_univ_four, SpChain.uMat, he, halt, p01, p02, p03, p10, p12, p13, p20, p21, p23,
      p30, p31, p32] <;>
    first | abel | module

theorem toMatrix_eq_minorJ (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) :
    BilinForm.toMatrix b B = SpChain.minorJ F := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, hb, SpChain.minorJ_apply]

theorem mem_isometryGroup_iff_mem_antiSp (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (g : V ≃ₗ[F] V) :
    g ∈ isometryGroup B ↔ basisMatrixEquiv b g ∈ SpChain.antiSp F := by
  have h := isometry_iff_matrix b B g
  rw [toMatrix_eq_minorJ B b hb] at h
  exact h.trans SpChain.mem_antiSp.symm

@[expose] noncomputable def isoAntiSp (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) :
    isometryGroup B ≃* SpChain.antiSp F where
  toFun g := ⟨basisMatrixEquiv b g.1, (mem_isometryGroup_iff_mem_antiSp B b hb g.1).mp g.2⟩
  invFun A := ⟨(basisMatrixEquiv b).symm A.1,
    (mem_isometryGroup_iff_mem_antiSp B b hb _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact A.2)⟩
  left_inv g := Subtype.ext ((basisMatrixEquiv b).symm_apply_apply g.1)
  right_inv A := Subtype.ext ((basisMatrixEquiv b).apply_symm_apply A.1)
  map_mul' g h := Subtype.ext ((basisMatrixEquiv b).map_mul g.1 h.1)

@[simp]
theorem coe_isoAntiSp (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (g : isometryGroup B) :
    ((isoAntiSp B b hb g : SpChain.antiSp F) : Matrix.GeneralLinearGroup (Fin 4) F) =
      basisMatrixEquiv b (g : V ≃ₗ[F] V) := rfl

theorem isoAntiSp_eq_uElt [CharP F 2] (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) {u w : V} {c d β : F}
    (hT : ∀ j, b j + (c * B (b j) u) • u + (d * B (b j) w) • w =
      ∑ i, (SpChain.uMat (0 : F) β 1 0) i j • b i)
    (g : V ≃ₗ[F] V) (hg : g ∈ isometryGroup B)
    (hgv : ∀ v, g v = v + (c * B v u) • u + (d * B v w) • w) :
    isoAntiSp B b hb ⟨g, hg⟩ = SpChain.uElt 0 β 1 0 := by
  refine SpChain.antiSp_ext ?_
  rw [SpChain.glMat_uElt]
  have hmat : SpChain.glMat ((isoAntiSp B b hb ⟨g, hg⟩ : SpChain.antiSp F) :
      Matrix.GeneralLinearGroup (Fin 4) F) = LinearMap.toMatrix b b g.toLinearMap := rfl
  rw [hmat]
  ext i j
  rw [LinearMap.toMatrix_apply]
  have hj : g (b j) = ∑ i, (SpChain.uMat (0 : F) β 1 0) i j • b i := by rw [hgv, hT j]
  show b.repr (g (b j)) i = _
  rw [hj, Module.Basis.repr_sum_self]

theorem exists_isoAntiSp_eq_uElt [Finite F] [CharP F 2] (B : BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) {u w : V} (huw : F ∙ u ≠ F ∙ w) (hu : u ≠ 0) (hw : w ≠ 0)
    (hBuw : B u w = 0) {c d : F} (hc : c ≠ 0) (hd : d ≠ 0)
    (g : V ≃ₗ[F] V) (hg : g ∈ isometryGroup B)
    (hgv : ∀ v, g v = v + (c * B v u) • u + (d * B v w) • w) :
    ∃ (b : Module.Basis (Fin 4) F V)
      (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (β : F),
      β ≠ 0 ∧ isoAntiSp B b hb ⟨g, hg⟩ = SpChain.uElt 0 β 1 0 := by
  obtain ⟨b, β, hβ, hb, hT⟩ := exists_adapted_basis B halt hnd hdim huw hu hw hBuw hc hd
  exact ⟨b, hb, β, hβ, isoAntiSp_eq_uElt B b hb hT g hg hgv⟩

end CFSG.Quasithin.SimsG45
