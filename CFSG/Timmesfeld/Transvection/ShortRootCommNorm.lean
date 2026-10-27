module

public import CFSG.Timmesfeld.Transvection.ShortRootComm
public import CFSG.Timmesfeld.Transvection.QuadForm

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace SL2Coords

variable {A E D E' : Subgroup G} {k : ℕ} (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k)

@[expose] noncomputable def quadNorm (x : G) : GaloisField 2 k := φ₀.quadCoord φ₁ x 1

@[expose] noncomputable def quadPolar (x y : G) : GaloisField 2 k :=
  φ₁.lowerCoord ⁅x, φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹⁆

@[expose] noncomputable def normV (Δ : Set (Subgroup G))
    (v : Additive ↥(shortRootGroup Δ E A D E')) : GaloisField 2 k :=
  φ₀.quadNorm φ₁ ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G)

omit φ₁ in
@[simp] theorem quadPart_one_left (s : GaloisField 2 k) : φ₀.quadPart 1 s = 1 := by
  simp [quadPart]

omit φ₁ in
@[simp] theorem quadPart_zero (x : G) : φ₀.quadPart x 0 = 1 := by
  simp [quadPart, lowerElt_zero]

omit φ₀ in
@[simp] theorem lowerCoord_one : φ₁.lowerCoord 1 = 0 := by
  simp [lowerCoord, φ₁.mat_one]

@[simp] theorem quadNorm_one : φ₀.quadNorm φ₁ 1 = 0 := by
  simp [quadNorm, quadCoord]

@[simp] theorem quadCoord_zero (x : G) : φ₀.quadCoord φ₁ x 0 = 0 := by
  simp [quadCoord]

theorem Aligned.torusElt_conj_eq_smulG {A E D E' : Subgroup G} {k : ℕ} {φ₀ : SL2Coords A E k}
    {φ₁ : SL2Coords D E' k} (hal : φ₀.Aligned Δ φ₁) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (ν : (GaloisField 2 k)ˣ) :
    φ₁.torusElt ν * x * (φ₁.torusElt ν)⁻¹ =
      φ₀.smulG ((ν⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) x := by
  have h := (hal ν x hx).eq
  rw [φ₀.smulG_units, φ₀.torusElt_inv, inv_inv]
  calc φ₁.torusElt ν * x * (φ₁.torusElt ν)⁻¹ =
        (φ₀.torusElt ν)⁻¹ * ((φ₀.torusElt ν * φ₁.torusElt ν) * x) * (φ₁.torusElt ν)⁻¹ := by
        group
    _ = (φ₀.torusElt ν)⁻¹ * x * φ₀.torusElt ν := by
        rw [h]
        group

end SL2Coords

structure IsNormBase {A E D E' : Subgroup G} {k : ℕ} (Δ : Set (Subgroup G))
    (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k) {F : Type*} [Field F] (σ : F ≃+* F)
    (ι : GaloisField 2 k →+* F) (β : F → G) : Prop where
  add : ∀ s t, β (s + t) = β s * β t
  injective : Function.Injective β
  mem_iff : ∀ g, g ∈ shortRootGroup Δ E A D E' ↔ ∃ c, β c = g
  smul : ∀ (c : GaloisField 2 k) (z : F), β (ι c * z) = φ₀.smulG c (β z)
  norm : ∀ z, ι (φ₀.quadNorm φ₁ (β z)) = σ z * z

namespace PairFrame

variable [Finite G] {A E D E' : Subgroup G} (F : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
  {k : ℕ} (φ₀ : SL2Coords A E k) (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A)
  (hX : ShortRootFieldHyp Δ A E D E') (φ₁ : SL2Coords D E' k)
include F hΔ hpts hq hX

theorem quadCoord_mul (hal : φ₀.Aligned Δ φ₁) {x : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (c s : GaloisField 2 k) : φ₀.quadCoord φ₁ x (c * s) = c * φ₀.quadCoord φ₁ x s := by
  by_cases hc : c = 0
  · rw [hc, zero_mul, zero_mul, SL2Coords.quadCoord_zero]
  obtain ⟨r, hr⟩ := QuadForm.exists_mul_self_eq c
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hr, mul_zero])
  have h1 := F.quadCoord_torusElt hΔ φ₀ hpts hq hX φ₁ hx (Units.mk0 r hr0)⁻¹ s
  rw [hal.torusElt_conj_eq_smulG hx, inv_inv,
    F.quadCoord_smulG hΔ φ₀ hpts hq hX φ₁ hx (Units.mk0 r hr0)] at h1
  simp only [Units.val_mk0, hr] at h1
  exact h1

theorem quadCoord_eq_mul_quadNorm (hal : φ₀.Aligned Δ φ₁) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (s : GaloisField 2 k) :
    φ₀.quadCoord φ₁ x s = s * φ₀.quadNorm φ₁ x := by
  rw [SL2Coords.quadNorm, ← F.quadCoord_mul hΔ φ₀ hpts hq hX φ₁ hal hx, mul_one]

theorem commutator_eq_mul_elt (hal : φ₀.Aligned Δ φ₁) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (s : GaloisField 2 k) :
    ⁅x, φ₀.elt (lowerElt _ s)⁆ = φ₀.elt (weylElt _) * φ₀.smulG s x * (φ₀.elt (weylElt _))⁻¹ *
      φ₁.elt (lowerElt _ (s * φ₀.quadNorm φ₁ x)) := by
  rw [φ₀.commutator_eq_mul_quadPart, ← F.quadCoord_eq_mul_quadNorm hΔ φ₀ hpts hq hX φ₁ hal hx,
    SL2Coords.quadCoord, φ₁.elt_lowerElt_lowerCoord (F.quadPart_mem hΔ φ₀ hpts hq hX hx s)]

theorem quadNorm_smulG (hal : φ₀.Aligned Δ φ₁) {x : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (c : GaloisField 2 k) : φ₀.quadNorm φ₁ (φ₀.smulG c x) = c * c * φ₀.quadNorm φ₁ x := by
  by_cases hc : c = 0
  · rw [hc, SL2Coords.smulG_zero, SL2Coords.quadNorm_one, zero_mul, zero_mul]
  have h := F.quadCoord_smulG hΔ φ₀ hpts hq hX φ₁ hx (Units.mk0 c hc) 1
  rw [Units.val_mk0, F.quadCoord_mul hΔ φ₀ hpts hq hX φ₁ hal hx] at h
  rw [SL2Coords.quadNorm, h, SL2Coords.quadNorm]

theorem eq_one_of_quadNorm_eq_zero {x : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (h0 : φ₀.quadNorm φ₁ x = 0) : x = 1 :=
  F.eq_one_of_quadCoord_eq_zero hΔ φ₀ hpts hq hX φ₁ hx h0

omit hX in
theorem commutator_conj_weylElt_mem {x y : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (hy : y ∈ shortRootGroup Δ E A D E') :
    ⁅x, φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹⁆ ∈ D :=
  F.commutator_mem_of_mem_shortRootGroup hΔ hpts hq hx (F.conj_elt_weylElt_mem hΔ φ₀ hy)

omit [Finite G] hpts hq hX in
theorem commute_of_mem_D_of_mem_shortRootGroup {d x : G} (hd : d ∈ D)
    (hx : x ∈ shortRootGroup Δ E A D E') : Commute d x :=
  commute_of_mem_lineGroup hΔ F.memE F.memD F.commuting_ED
    (le_lineGroup (right_mem_lineOf F.memD) hd) hx.1.1

theorem quadNorm_mul {x y : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (hy : y ∈ shortRootGroup Δ E A D E') :
    φ₀.quadNorm φ₁ (x * y) = φ₀.quadNorm φ₁ x + φ₀.quadNorm φ₁ y + φ₀.quadPolar φ₁ x y := by
  set w := φ₀.elt (weylElt _) with hw
  set dx := φ₀.quadPart x 1
  set dy := φ₀.quadPart y 1
  set c := ⁅x, w * y * w⁻¹⁆ with hc
  have hdx : dx ∈ D := F.quadPart_mem hΔ φ₀ hpts hq hX hx 1
  have hdy : dy ∈ D := F.quadPart_mem hΔ φ₀ hpts hq hX hy 1
  have hcD : c ∈ D := F.commutator_conj_weylElt_mem hΔ φ₀ hpts hq hx hy
  have hU : ∀ {u : G}, u ∈ D → u ∈ lineGroup Δ A D := fun hu => F.D_le_lineGroup hu
  have hXU : ∀ {z : G}, z ∈ shortRootGroup Δ E A D E' → w * z * w⁻¹ ∈ lineGroup Δ A D :=
    fun hz => (inf_le_left.trans inf_le_left : shortRootGroup Δ A E D E' ≤ lineGroup Δ A D)
      (F.conj_elt_weylElt_mem hΔ φ₀ hz)
  have hxy : φ₀.quadPart (x * y) 1 = c * dx * dy := by
    refine φ₀.quadPart_eq_of_commutator_eq ?_
    have h1 : ⁅x * y, φ₀.elt (lowerElt _ 1)⁆ =
        x * ⁅y, φ₀.elt (lowerElt _ 1)⁆ * x⁻¹ * ⁅x, φ₀.elt (lowerElt _ 1)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1, φ₀.commutator_eq_mul_quadPart, φ₀.commutator_eq_mul_quadPart, SL2Coords.smulG_one,
      SL2Coords.smulG_one, SL2Coords.smulG_one]
    have hxd : x * dy * x⁻¹ = dy := by
      rw [(F.commute_of_mem_D_of_mem_shortRootGroup hΔ hdy hx).symm.eq, mul_inv_cancel_right]
    have hcu : x * (w * y * w⁻¹) * x⁻¹ = c * (w * y * w⁻¹) := by
      rw [hc, commutatorElement_def]
      group
    have h2 : x * (w * y * w⁻¹ * dy) * x⁻¹ = c * (w * y * w⁻¹) * dy := by
      calc x * (w * y * w⁻¹ * dy) * x⁻¹ = (x * (w * y * w⁻¹) * x⁻¹) * (x * dy * x⁻¹) := by group
        _ = c * (w * y * w⁻¹) * dy := by rw [hxd, hcu]
    rw [h2]
    have hc1 := F.commute_of_mem_lineGroup_AD hΔ (hU hcD) (hXU hy)
    have hc2 := F.commute_of_mem_lineGroup_AD hΔ (hU hdy) (hXU hx)
    have hc3 := F.commute_of_mem_lineGroup_AD hΔ (hU hcD) (hXU hx)
    have hc4 := F.commute_of_mem_lineGroup_AD hΔ (hU hdy) (hU hdx)
    have hxyc : w * (x * y) * w⁻¹ = w * y * w⁻¹ * (w * x * w⁻¹) := by
      rw [(F.commute_of_mem_shortRootGroup hΔ hx hy).eq]
      group
    rw [hxyc]
    calc c * (w * y * w⁻¹) * dy * (w * x * w⁻¹ * dx) =
          (w * y * w⁻¹) * c * (dy * (w * x * w⁻¹)) * dx := by
          rw [hc1.eq]
          group
      _ = (w * y * w⁻¹) * c * ((w * x * w⁻¹) * dy) * dx := by rw [hc2.eq]
      _ = (w * y * w⁻¹) * (c * (w * x * w⁻¹)) * (dy * dx) := by group
      _ = (w * y * w⁻¹) * ((w * x * w⁻¹) * c) * (dx * dy) := by rw [hc3.eq, hc4.eq]
      _ = w * y * w⁻¹ * (w * x * w⁻¹) * (c * dx * dy) := by group
  rw [SL2Coords.quadNorm, SL2Coords.quadCoord, hxy, φ₁.lowerCoord_mul (Subgroup.mul_mem _ hcD hdx)
    hdy, φ₁.lowerCoord_mul hcD hdx, SL2Coords.quadNorm, SL2Coords.quadNorm, SL2Coords.quadCoord,
    SL2Coords.quadCoord, SL2Coords.quadPolar]
  ring

omit hX in
theorem quadPolar_mul_left {x x' y : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (hx' : x' ∈ shortRootGroup Δ E A D E') (hy : y ∈ shortRootGroup Δ E A D E') :
    φ₀.quadPolar φ₁ (x * x') y = φ₀.quadPolar φ₁ x y + φ₀.quadPolar φ₁ x' y := by
  set u := φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹
  have h1 := F.commutator_conj_weylElt_mem hΔ φ₀ hpts hq hx hy
  have h2 := F.commutator_conj_weylElt_mem hΔ φ₀ hpts hq hx' hy
  have h3 : ⁅x * x', u⁆ = ⁅x', u⁆ * ⁅x, u⁆ := by
    have h4 : ⁅x * x', u⁆ = x * ⁅x', u⁆ * x⁻¹ * ⁅x, u⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h4, ← (F.commute_of_mem_D_of_mem_shortRootGroup hΔ h2 hx).eq, mul_inv_cancel_right]
  rw [SL2Coords.quadPolar, h3, φ₁.lowerCoord_mul h2 h1, add_comm]
  rfl

omit hX in
theorem quadPolar_smulG_smulG {x y : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (hy : y ∈ shortRootGroup Δ E A D E') (μ : (GaloisField 2 k)ˣ) :
    φ₀.quadPolar φ₁ (φ₀.smulG μ x) (φ₀.smulG ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) y) =
      φ₀.quadPolar φ₁ x y := by
  have hd := F.commutator_conj_weylElt_mem hΔ φ₀ hpts hq hx hy
  have hhd : Commute (φ₀.torusElt μ)
      ⁅x, φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹⁆ :=
    F.comm _ (φ₀.torusElt_mem μ) _ (Subgroup.mem_sup_left hd)
  have h1 : φ₀.torusElt μ * (φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹) *
      (φ₀.torusElt μ)⁻¹ = φ₀.elt (weylElt _) *
        φ₀.smulG ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) y * (φ₀.elt (weylElt _))⁻¹ := by
    rw [φ₀.smulG_units]
    calc φ₀.torusElt μ * (φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹) *
          (φ₀.torusElt μ)⁻¹ = (φ₀.torusElt μ * φ₀.elt (weylElt _)) * y *
            (φ₀.torusElt μ * φ₀.elt (weylElt _))⁻¹ := by group
      _ = _ := by
          rw [φ₀.torusElt_mul_elt_weylElt]
          group
  have h2 : ⁅φ₀.smulG μ x, φ₀.elt (weylElt _) *
      φ₀.smulG ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) y * (φ₀.elt (weylElt _))⁻¹⁆ =
      ⁅x, φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹⁆ := by
    rw [φ₀.smulG_units, ← h1]
    calc ⁅φ₀.torusElt μ * x * (φ₀.torusElt μ)⁻¹, φ₀.torusElt μ *
          (φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹) * (φ₀.torusElt μ)⁻¹⁆ =
          φ₀.torusElt μ * ⁅x, φ₀.elt (weylElt _) * y * (φ₀.elt (weylElt _))⁻¹⁆ *
            (φ₀.torusElt μ)⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = _ := by rw [hhd.eq, mul_inv_cancel_right]
  rw [SL2Coords.quadPolar, h2]
  rfl

omit hX in
theorem quadPolar_torusElt {x y : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (hy : y ∈ shortRootGroup Δ E A D E') (ν : (GaloisField 2 k)ˣ) :
    φ₀.quadPolar φ₁ (φ₁.torusElt ν * x * (φ₁.torusElt ν)⁻¹)
        (φ₁.torusElt ν * y * (φ₁.torusElt ν)⁻¹) =
      ((ν⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * ((ν⁻¹ : (GaloisField 2 k)ˣ) :
        GaloisField 2 k) * φ₀.quadPolar φ₁ x y := by
  set w := φ₀.elt (weylElt _)
  set h := φ₁.torusElt ν with hh
  have hd := F.commutator_conj_weylElt_mem hΔ φ₀ hpts hq hx hy
  have hhw : Commute h w := (F.comm _ (φ₀.elt_mem _) _ (φ₁.torusElt_mem ν)).symm
  have h2 : ⁅h * x * h⁻¹, w * (h * y * h⁻¹) * w⁻¹⁆ = h * ⁅x, w * y * w⁻¹⁆ * h⁻¹ := by
    calc ⁅h * x * h⁻¹, w * (h * y * h⁻¹) * w⁻¹⁆ =
          ⁅h * x * h⁻¹, (w * h) * y * (w * h)⁻¹⁆ := by group
      _ = ⁅h * x * h⁻¹, (h * w) * y * (h * w)⁻¹⁆ := by rw [hhw.eq]
      _ = h * ⁅x, w * y * w⁻¹⁆ * h⁻¹ := by
          simp only [commutatorElement_def]
          group
  rw [SL2Coords.quadPolar, h2, φ₁.lowerCoord_torusElt_conj ν hd, pow_two]
  rfl

omit hX in
theorem quadPolar_smulG_left (hal : φ₀.Aligned Δ φ₁) {x y : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (hy : y ∈ shortRootGroup Δ E A D E')
    (c : GaloisField 2 k) :
    φ₀.quadPolar φ₁ (φ₀.smulG c x) y = c * φ₀.quadPolar φ₁ x y := by
  by_cases hc : c = 0
  · rw [hc, SL2Coords.smulG_zero, zero_mul, SL2Coords.quadPolar]
    simp
  obtain ⟨r, hr⟩ := QuadForm.exists_mul_self_eq c
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hr, mul_zero])
  set μ : (GaloisField 2 k)ˣ := Units.mk0 r hr0 with hμ
  have hrx := F.smulG_mem hΔ φ₀ hx r
  have hry := F.smulG_mem hΔ φ₀ hy r
  have h1 := F.quadPolar_smulG_smulG hΔ φ₀ hpts hq φ₁ hrx hry μ
  have hμr : ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * r = 1 := by
    rw [hμ, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hr0]
  have hinv : φ₀.smulG ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) (φ₀.smulG r y) = y := by
    rw [← φ₀.smulG_mul, hμr, SL2Coords.smulG_one]
  rw [hinv, hμ, Units.val_mk0, ← φ₀.smulG_mul, hr] at h1
  rw [h1]
  have h2 := F.quadPolar_torusElt hΔ φ₀ hpts hq φ₁ hx hy μ⁻¹
  rw [hal.torusElt_conj_eq_smulG hx, hal.torusElt_conj_eq_smulG hy, inv_inv] at h2
  rw [hμ, Units.val_mk0, hr] at h2
  exact h2

theorem polar_normV (v w : Additive ↥(shortRootGroup Δ E A D E')) :
    letI := F.shortRootAddCommGroup hΔ
    QuadraticMap.polar (φ₀.normV φ₁ Δ) v w =
      φ₀.quadPolar φ₁ ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G)
        ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G) := by
  let _ := F.shortRootAddCommGroup hΔ
  change φ₀.quadNorm φ₁ (((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) *
      ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G)) -
    φ₀.quadNorm φ₁ ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) -
    φ₀.quadNorm φ₁ ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G) = _
  rw [F.quadNorm_mul hΔ φ₀ hpts hq hX φ₁ v.toMul.2 w.toMul.2]
  ring

theorem exists_normBase (hal : φ₀.Aligned Δ φ₁)
    (hX1 : ∃ x ∈ shortRootGroup Δ E A D E', x ≠ 1) :
    (Nat.card ↥(shortRootGroup Δ E A D E') = 2 ^ k ∧
      ∃ β : GaloisField 2 k → G, IsNormBase Δ φ₀ φ₁ (RingEquiv.refl _) (RingHom.id _) β) ∨
    (Nat.card ↥(shortRootGroup Δ E A D E') = (2 ^ k) ^ 2 ∧
      ∀ ι : GaloisField 2 k →+* GaloisField 2 (2 * k),
        (∀ z, unitaryInvolution (GaloisField 2 (2 * k)) 2 k z = z ↔ ∃ c, ι c = z) →
        ∃ β : GaloisField 2 (2 * k) → G,
          IsNormBase Δ φ₀ φ₁ (unitaryInvolution (GaloisField 2 (2 * k)) 2 k) ι β) := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX
  have hsm : ∀ (c : GaloisField 2 k) (v : Additive ↥(shortRootGroup Δ E A D E')),
      (((c • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) =
        φ₀.smulG c ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) :=
    fun c v => F.coe_smul_eq_smulG hΔ φ₀ hpts hq hX v c
  have hN : ∀ (c : GaloisField 2 k) (v : Additive ↥(shortRootGroup Δ E A D E')),
      φ₀.normV φ₁ Δ (c • v) = c * c * φ₀.normV φ₁ Δ v := by
    intro c v
    rw [SL2Coords.normV, hsm, F.quadNorm_smulG hΔ φ₀ hpts hq hX φ₁ hal v.toMul.2]
    rfl
  have hadd : ∀ x x' y : Additive ↥(shortRootGroup Δ E A D E'),
      QuadraticMap.polar (φ₀.normV φ₁ Δ) (x + x') y =
        QuadraticMap.polar (φ₀.normV φ₁ Δ) x y + QuadraticMap.polar (φ₀.normV φ₁ Δ) x' y := by
    intro x x' y
    rw [F.polar_normV hΔ φ₀ hpts hq hX φ₁, F.polar_normV hΔ φ₀ hpts hq hX φ₁,
      F.polar_normV hΔ φ₀ hpts hq hX φ₁]
    exact F.quadPolar_mul_left hΔ φ₀ hpts hq φ₁ x.toMul.2 x'.toMul.2 y.toMul.2
  have hsmul : ∀ (c : GaloisField 2 k) (x y : Additive ↥(shortRootGroup Δ E A D E')),
      QuadraticMap.polar (φ₀.normV φ₁ Δ) (c • x) y =
        c * QuadraticMap.polar (φ₀.normV φ₁ Δ) x y := by
    intro c x y
    rw [F.polar_normV hΔ φ₀ hpts hq hX φ₁, F.polar_normV hΔ φ₀ hpts hq hX φ₁, hsm]
    exact F.quadPolar_smulG_left hΔ φ₀ hpts hq φ₁ hal x.toMul.2 y.toMul.2 c
  have haniso' : ∀ x : Additive ↥(shortRootGroup Δ E A D E'), φ₀.normV φ₁ Δ x = 0 →
      ((x.toMul : ↥(shortRootGroup Δ E A D E')) : G) = 1 := fun x h0 =>
    F.eq_one_of_quadNorm_eq_zero hΔ φ₀ hpts hq hX φ₁ x.toMul.2 h0
  obtain ⟨x₁, hx₁, hx₁1⟩ := hX1
  have hnt : Nontrivial (Additive ↥(shortRootGroup Δ E A D E')) :=
    ⟨⟨Additive.ofMul ⟨x₁, hx₁⟩, 0, fun h => hx₁1 (congrArg (fun v :
      Additive ↥(shortRootGroup Δ E A D E') => ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G))
      h)⟩⟩
  obtain ⟨x₀, hx₀⟩ := QuadForm.exists_eq_one hN
    (fun x h0 => Additive.toMul.injective (Subtype.ext (haniso' x h0)))
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    have h := hN 0 0
    rw [zero_smul, zero_mul, zero_mul] at h
    rw [h] at hx₀
    exact zero_ne_one hx₀
  have hcard := F.card_shortRootGroup φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · have := φ₀.card_eq
      rw [h, pow_zero] at this
      omega
    · exact h
  have key : ∀ {F' : Type} [Field F'] (σ : F' ≃+* F') (ι' : GaloisField 2 k →+* F')
      (e : F' ≃+ Additive ↥(shortRootGroup Δ E A D E')),
      (∀ (c : GaloisField 2 k) (z : F'), e (ι' c * z) = c • e z) →
      (∀ z, ι' (φ₀.normV φ₁ Δ (e z)) = σ z * z) →
      IsNormBase Δ φ₀ φ₁ σ ι' fun z => (((e z).toMul : ↥(shortRootGroup Δ E A D E')) : G) := by
    intro F' _ σ ι' e he hn
    refine ⟨fun s t => ?_, fun s t h => e.injective (Additive.toMul.injective (Subtype.ext h)),
      fun g => ⟨fun hg => ⟨e.symm (Additive.ofMul ⟨g, hg⟩), by simp⟩, ?_⟩,
      fun c z => by rw [he, hsm], hn⟩
    · rw [map_add]
      rfl
    · rintro ⟨c, rfl⟩
      exact (e c).toMul.2
  rcases QuadForm.finrank_eq_one_or_two hN hadd hsmul
      (fun x h0 => Additive.toMul.injective (Subtype.ext (haniso' x h0))) with h1 | h2
  · left
    obtain ⟨e, -, he, hen⟩ := QuadForm.exists_addEquiv_of_finrank_eq_one hN h1 hx₀0
    refine ⟨by rw [hcard, h1, pow_one], _, key (RingEquiv.refl _) (RingHom.id _) e
      (fun c z => he c z) fun z => ?_⟩
    rw [hen, hx₀, one_mul]
    rfl
  · right
    refine ⟨by rw [hcard, h2], fun ι' hι' => ?_⟩
    have hF : Nat.card (GaloisField 2 (2 * k)) = (2 ^ k) ^ 2 := by
      rw [GaloisField.card 2 (2 * k) (by omega), ← pow_mul, mul_comm]
    obtain ⟨e, -, he, hen⟩ :=
      QuadForm.exists_addEquiv_of_finrank_eq_two_of_unitary hN hadd hsmul
        (fun x h0 => Additive.toMul.injective (Subtype.ext (haniso' x h0))) hF ι' hι' h2 hx₀0
    refine ⟨_, key _ ι' e he fun z => ?_⟩
    rw [hen, hx₀, map_one, one_mul]

end PairFrame

end CFSG.Timmesfeld.Transvection
