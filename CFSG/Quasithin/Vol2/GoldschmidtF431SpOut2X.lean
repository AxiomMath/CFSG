module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Frob

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open

open scoped commutatorElement

namespace SpOut2

section Coords

variable {F : Type} [Field F] [CharP F 2]

theorem eq_uElt_coords {y : antiSp F} (hy : y ∈ antiUnipotent F) :
    y = uElt (mat y 0 1) (mat y 0 2) (mat y 0 3) (mat y 1 2) := by
  obtain ⟨a, b, c, d, rfl⟩ := hy
  rfl

theorem mat_uElt_01 (a b c d : F) : mat (uElt a b c d) 0 1 = a := rfl
theorem mat_uElt_02 (a b c d : F) : mat (uElt a b c d) 0 2 = b := rfl
theorem mat_uElt_03 (a b c d : F) : mat (uElt a b c d) 0 3 = c := rfl
theorem mat_uElt_12 (a b c d : F) : mat (uElt a b c d) 1 2 = d := rfl

theorem commute_uElt_iff {a b c d a' b' c' d' : F}
    (h : uElt a' b' c' d' * uElt a b c d = uElt a b c d * uElt a' b' c' d') :
    a' * d = a * d' ∧ a * a' * d = a * a' * d' := by
  rw [uElt_mul, uElt_mul] at h
  obtain ⟨-, h2, h3, -⟩ := uElt_inj h
  exact ⟨by linear_combination h2, by linear_combination h3⟩

end Coords

section Count

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_abelian_le_of_noninvolution {A : Subgroup (antiSp F)} (hAU : A ≤ antiUnipotent F)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x : antiSp F} (hx : x ∈ A) (hx2 : x * x ≠ 1) :
    Nat.card A ≤ 2 * Nat.card F ^ 2 := by
  classical
  obtain ⟨a, b, c, d, rfl⟩ := hAU hx
  rw [uElt_mul_self] at hx2
  have had : a * d ≠ 0 := by
    intro h
    apply hx2
    rw [h, show a ^ 2 * d = a * (a * d) by ring, h, mul_zero, uElt_zero_eq_one]
  have ha : a ≠ 0 := left_ne_zero_of_mul had
  have hd : d ≠ 0 := right_ne_zero_of_mul had
  let f : A → Bool × F × F := fun y =>
    (decide (mat (y : antiSp F) 0 1 = 0), mat (y : antiSp F) 0 2, mat (y : antiSp F) 0 3)
  have key : ∀ y : A, (mat (y : antiSp F) 0 1 = 0 ∧ mat (y : antiSp F) 1 2 = 0) ∨
      (mat (y : antiSp F) 0 1 = a ∧ mat (y : antiSp F) 1 2 = d) := by
    intro y
    have hy := eq_uElt_coords (hAU y.2)
    obtain ⟨h2, h3⟩ := commute_uElt_iff (a := a) (b := b) (c := c) (d := d)
      (a' := mat (y : antiSp F) 0 1) (b' := mat (y : antiSp F) 0 2) (c' := mat (y : antiSp F) 0 3)
      (d' := mat (y : antiSp F) 1 2) (by rw [← hy]; exact hab _ y.2 _ hx)
    set a' := mat (y : antiSp F) 0 1
    set d' := mat (y : antiSp F) 1 2
    have h4 : a' * d * (a - a') = 0 := by linear_combination h3 - a' * h2
    rcases mul_eq_zero.mp h4 with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · left
        refine ⟨h6, ?_⟩
        rw [h6, zero_mul] at h2
        exact (mul_eq_zero.mp h2.symm).resolve_left ha
      · exact absurd h6 hd
    · right
      have h7 : a' = a := (sub_eq_zero.mp h5).symm
      refine ⟨h7, ?_⟩
      rw [h7] at h2
      exact (mul_right_injective₀ ha h2).symm
  have hf : Function.Injective f := by
    intro y y' hyy
    simp only [f, Prod.mk.injEq, decide_eq_decide] at hyy
    obtain ⟨h1, h2, h3⟩ := hyy
    have hcases : mat (y : antiSp F) 0 1 = mat (y' : antiSp F) 0 1 ∧
        mat (y : antiSp F) 1 2 = mat (y' : antiSp F) 1 2 := by
      rcases key y with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;> rcases key y' with ⟨hy1', hy2'⟩ | ⟨hy1', hy2'⟩
      · exact ⟨hy1.trans hy1'.symm, hy2.trans hy2'.symm⟩
      · exfalso
        rw [hy1, hy1'] at h1
        exact ha (by simpa using h1.symm)
      · exfalso
        rw [hy1, hy1'] at h1
        exact ha (by simpa using h1)
      · exact ⟨hy1.trans hy1'.symm, hy2.trans hy2'.symm⟩
    apply Subtype.ext
    rw [eq_uElt_coords (hAU y.2), eq_uElt_coords (hAU y'.2), hcases.1, hcases.2, h2, h3]
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, mul_assoc, pow_two] using this

end Count

section CentBasic

variable {F : Type} [Field F] [CharP F 2]

@[expose] def fixField (F : Type) [Field F] [CharP F 2] (s : ℕ) : Subfield F :=
  RingHom.eqLocusField (iterateFrobenius F 2 s) (RingHom.id F)

theorem mem_fixField {s : ℕ} {x : F} : x ∈ fixField F s ↔ x ^ 2 ^ s = x := by
  simp [fixField, RingHom.eqLocusField, iterateFrobenius_def]

theorem mat_mul_01 {x y : antiSp F} (hx : x ∈ antiUnipotent F) (hy : y ∈ antiUnipotent F) :
    mat (x * y) 0 1 = mat x 0 1 + mat y 0 1 := by
  rw [eq_uElt_coords hx, eq_uElt_coords hy, uElt_mul]
  rfl

theorem mat_mul_12 {x y : antiSp F} (hx : x ∈ antiUnipotent F) (hy : y ∈ antiUnipotent F) :
    mat (x * y) 1 2 = mat x 1 2 + mat y 1 2 := by
  rw [eq_uElt_coords hx, eq_uElt_coords hy, uElt_mul]
  rfl

theorem mat_inv_01 {x : antiSp F} (hx : x ∈ antiUnipotent F) : mat x⁻¹ 0 1 = mat x 0 1 := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  have h1 : mat (uElt a b c d)⁻¹ 0 1 = a := rfl
  rw [h1, mat_uElt_01]

theorem mat_inv_12 {x : antiSp F} (hx : x ∈ antiUnipotent F) : mat x⁻¹ 1 2 = mat x 1 2 := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  have h1 : mat (uElt a b c d)⁻¹ 1 2 = d := rfl
  rw [h1, mat_uElt_12]

theorem mat_conj_01 {u y : antiSp F} (hu : u ∈ antiUnipotent F) (hy : y ∈ antiUnipotent F) :
    mat (u * y * u⁻¹) 0 1 = mat y 0 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hui : u⁻¹ ∈ antiUnipotent F := inv_mem hu
  have key : ∀ p q : F, p + q + p = q := fun p q => by linear_combination p * h2
  rw [mat_mul_01 (mul_mem hu hy) hui, mat_mul_01 hu hy, mat_inv_01 hu]
  exact key _ _

theorem mat_conj_12 {u y : antiSp F} (hu : u ∈ antiUnipotent F) (hy : y ∈ antiUnipotent F) :
    mat (u * y * u⁻¹) 1 2 = mat y 1 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hui : u⁻¹ ∈ antiUnipotent F := inv_mem hu
  have key : ∀ p q : F, p + q + p = q := fun p q => by linear_combination p * h2
  rw [mat_mul_12 (mul_mem hu hy) hui, mat_mul_12 hu hy, mat_inv_12 hu]
  exact key _ _

theorem uElt_central (a₀ b₀ c₀ d₀ β γ : F) :
    uElt a₀ b₀ c₀ d₀ * uElt 0 β γ 0 = uElt 0 β γ 0 * uElt a₀ b₀ c₀ d₀ := by
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

end CentBasic

section Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem mat_frobAut_pow_01 (k : ℕ) {y : antiSp F} (hy : y ∈ antiUnipotent F) :
    mat ((frobAut F ^ k) y) 0 1 = mat y 0 1 ^ 2 ^ k := by
  rw [eq_uElt_coords hy, frobAut_pow_uElt]
  rfl

theorem mat_frobAut_pow_12 (k : ℕ) {y : antiSp F} (hy : y ∈ antiUnipotent F) :
    mat ((frobAut F ^ k) y) 1 2 = mat y 1 2 ^ 2 ^ k := by
  rw [eq_uElt_coords hy, frobAut_pow_uElt]
  rfl

theorem mat_frobAut_pow_02 (k : ℕ) {y : antiSp F} (hy : y ∈ antiUnipotent F) :
    mat ((frobAut F ^ k) y) 0 2 = mat y 0 2 ^ 2 ^ k := by
  rw [eq_uElt_coords hy, frobAut_pow_uElt]
  rfl

theorem mat_frobAut_pow_03 (k : ℕ) {y : antiSp F} (hy : y ∈ antiUnipotent F) :
    mat ((frobAut F ^ k) y) 0 3 = mat y 0 3 ^ 2 ^ k := by
  rw [eq_uElt_coords hy, frobAut_pow_uElt]
  rfl

theorem card_le_of_ker_range {G M X Y : Type*} [Group G] [Group M] [Finite G] [Finite X]
    [Finite Y] (φ : G →* M) (f : φ.ker → X) (hf : Function.Injective f) (g : φ.range → Y)
    (hg : Function.Injective g) : Nat.card G ≤ Nat.card X * Nat.card Y := by
  have h := Subgroup.card_ker_mul_card_range φ
  rw [← h]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective f hf) (Nat.card_le_card_of_injective g hg)

theorem card_centralized_le {s : ℕ} (hs : frobAut F ^ s ≠ 1) {u₀ : antiSp F}
    (hu₀ : u₀ ∈ antiUnipotent F) {B : Subgroup (antiSp F)} (hB : B ≤ antiUnipotent F)
    (hfix : ∀ b ∈ B, u₀ * (frobAut F ^ s) b * u₀⁻¹ = b) : Nat.card B ≤ Nat.card F ^ 2 := by
  classical
  have hFw : fixField F s ≠ ⊤ := by
    intro h
    apply hs
    refine MulEquiv.ext fun g => ?_
    apply mat_ext
    rw [mat_frobAut_pow]
    ext i j
    simp only [Matrix.map_apply]
    exact mem_fixField.mp (h ▸ Subfield.mem_top _)
  have hsq := card_sq_le_of_ne_top (fixField F s) hFw
  have hBa : ∀ b ∈ B, mat b 0 1 ∈ fixField F s := by
    intro b hb
    rw [mem_fixField]
    have h : mat (u₀ * (frobAut F ^ s) b * u₀⁻¹) 0 1 = mat b 0 1 := by rw [hfix b hb]
    rwa [mat_conj_01 hu₀ ((frobAut_pow_mem_antiUnipotent_iff s b).mpr (hB hb)),
      mat_frobAut_pow_01 s (hB hb)] at h
  have hBd : ∀ b ∈ B, mat b 1 2 ∈ fixField F s := by
    intro b hb
    rw [mem_fixField]
    have h : mat (u₀ * (frobAut F ^ s) b * u₀⁻¹) 1 2 = mat b 1 2 := by rw [hfix b hb]
    rwa [mat_conj_12 hu₀ ((frobAut_pow_mem_antiUnipotent_iff s b).mpr (hB hb)),
      mat_frobAut_pow_12 s (hB hb)] at h
  let φ : B →* Multiplicative (F × F) :=
    { toFun := fun b => Multiplicative.ofAdd (mat (b : antiSp F) 0 1, mat (b : antiSp F) 1 2)
      map_one' := by
        have h1 : mat (1 : antiSp F) 0 1 = 0 := by rw [mat_one]; rfl
        have h2 : mat (1 : antiSp F) 1 2 = 0 := by rw [mat_one]; rfl
        simp only [OneMemClass.coe_one, h1, h2]
        rfl
      map_mul' := by
        intro x y
        simp only [Subgroup.coe_mul, mat_mul_01 (hB x.2) (hB y.2), mat_mul_12 (hB x.2) (hB y.2)]
        rfl }
  have hker : ∀ b : B, b ∈ φ.ker → mat (b : antiSp F) 0 1 = 0 ∧ mat (b : antiSp F) 1 2 = 0 := by
    intro b hb
    have h : φ b = 1 := hb
    have h' : (mat (b : antiSp F) 0 1, mat (b : antiSp F) 1 2) = (0, 0) := h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hkerFix : ∀ b : B, b ∈ φ.ker → mat (b : antiSp F) 0 2 ∈ fixField F s ∧
      mat (b : antiSp F) 0 3 ∈ fixField F s := by
    intro b hb
    obtain ⟨ha, hd⟩ := hker b hb
    have hbU := hB b.2
    have hb' : (b : antiSp F) = uElt 0 (mat (b : antiSp F) 0 2) (mat (b : antiSp F) 0 3) 0 := by
      have := eq_uElt_coords hbU
      rwa [ha, hd] at this
    have hω : (frobAut F ^ s) (b : antiSp F) =
        uElt 0 (mat (b : antiSp F) 0 2 ^ 2 ^ s) (mat (b : antiSp F) 0 3 ^ 2 ^ s) 0 := by
      conv_lhs => rw [hb']
      rw [frobAut_pow_uElt]
      simp
    have hcomm := hfix b b.2
    rw [hω] at hcomm
    obtain ⟨a₁, b₁, c₁, d₁, hu⟩ := hu₀
    rw [hu, uElt_central, mul_inv_cancel_right] at hcomm
    have h2 : mat (uElt 0 (mat (b : antiSp F) 0 2 ^ 2 ^ s) (mat (b : antiSp F) 0 3 ^ 2 ^ s) 0) 0 2 =
        mat (b : antiSp F) 0 2 := by rw [hcomm]
    have h3 : mat (uElt 0 (mat (b : antiSp F) 0 2 ^ 2 ^ s) (mat (b : antiSp F) 0 3 ^ 2 ^ s) 0) 0 3 =
        mat (b : antiSp F) 0 3 := by rw [hcomm]
    exact ⟨mem_fixField.mpr h2, mem_fixField.mpr h3⟩
  let f : φ.ker → fixField F s × fixField F s := fun b =>
    (⟨mat (b.1 : antiSp F) 0 2, (hkerFix b.1 b.2).1⟩,
      ⟨mat (b.1 : antiSp F) 0 3, (hkerFix b.1 b.2).2⟩)
  have hf : Function.Injective f := by
    intro b b' h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h2, h3⟩ := h
    apply Subtype.ext
    apply Subtype.ext
    have e1 := eq_uElt_coords (hB b.1.2)
    have e2 := eq_uElt_coords (hB b'.1.2)
    rw [e1, e2, (hker b.1 b.2).1, (hker b.1 b.2).2, (hker b'.1 b'.2).1, (hker b'.1 b'.2).2, h2, h3]
  let g : φ.range → fixField F s × fixField F s := fun z =>
    (⟨(Multiplicative.toAdd z.1).1, by
        obtain ⟨⟨b, hb⟩, hz⟩ := z.2
        rw [← hz]
        exact hBa b hb⟩,
      ⟨(Multiplicative.toAdd z.1).2, by
        obtain ⟨⟨b, hb⟩, hz⟩ := z.2
        rw [← hz]
        exact hBd b hb⟩)
  have hg : Function.Injective g := by
    intro z z' h
    simp only [g, Prod.mk.injEq, Subtype.mk.injEq] at h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact Prod.ext h.1 h.2
  have hcard := card_le_of_ker_range φ f hf g hg
  have hprod : Nat.card (fixField F s × fixField F s) = Nat.card (fixField F s) ^ 2 := by
    rw [Nat.card_prod, pow_two]
  rw [hprod] at hcard
  calc Nat.card B ≤ Nat.card (fixField F s) ^ 2 * Nat.card (fixField F s) ^ 2 := hcard
    _ = (Nat.card (fixField F s) ^ 2) ^ 2 := by ring
    _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hsq 2

end Cent

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem frobAut_dHom (i : Axis) (l : Fˣ) : frobAut F (dHom F i l) = dHom F i (l ^ 2) := by
  cases i
  · show frobAut F (minorAut F (dHom₂ F l)) = minorAut F (dHom₂ F (l ^ 2))
    rw [frobAut_minorAut, dHom₂_apply, dHom₂_apply, frobAut_dElt]
  · show frobAut F (dHom₂ F l) = dHom₂ F (l ^ 2)
    rw [dHom₂_apply, dHom₂_apply, frobAut_dElt]

theorem frobAut_pow_dHom (i : Axis) (s : ℕ) (l : Fˣ) :
    (frobAut F ^ s) (dHom F i l) = dHom F i (l ^ 2 ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', MulAut.mul_apply, ih, frobAut_dHom, ← pow_mul, ← pow_succ]

theorem frobAut_pow_rootCoord (i : Axis) (s : ℕ) (x : F) :
    (frobAut F ^ s) (rootCoord F i x) = rootCoord F i (x ^ 2 ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', MulAut.mul_apply, ih, frobAut_rootCoord, ← pow_mul, ← pow_succ]

omit [Finite F] in
theorem eq_of_sq_eq_one {x : F} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have : (x - 1) ^ 2 = 0 := by linear_combination hx - (x - 1) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)

theorem frobAut_pow_eq_one_of_fix {s : ℕ} (h : ∀ x : F, x ^ 2 ^ s = x) : frobAut F ^ s = 1 := by
  refine MulEquiv.ext fun g => ?_
  apply mat_ext
  rw [mat_frobAut_pow]
  ext i j
  simp only [Matrix.map_apply]
  exact h _

theorem frobAut_pow_eq_one_of_torus {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2)
    (s : ℕ) {u : antiSp F} (hu : u ∈ antiUnipotent F)
    (h : ∀ x ∈ Subgroup.normalizer (Rrad F j : Set (antiSp F)),
      x * u * ((frobAut F ^ s) x)⁻¹ * u⁻¹ ∈ Rrad F j) : frobAut F ^ s = 1 := by
  have hS := hS_axis hn hF j
  have hd : ∀ l : Fˣ, dHom F (axisOf j) l ∈
      Subgroup.normalizer (Rrad F j : Set (antiSp F)) := by
    intro l
    have := hS.ds_mem_N l 1
    rw [map_one, mul_one, hS.N_eq, rootA_axisOf] at this
    exact this
  have hcen : ∀ x : F, u * rootCoord F (axisOf j) x = rootCoord F (axisOf j) x * u := by
    intro x
    have hz : rootCoord F (axisOf j) x ∈ centerOf (antiUnipotent F) :=
      rootU_le_center j (hS.coord_mem x)
    exact (mem_centerOf_iff.mp hz).2 u hu
  have key : ∀ μ : Fˣ, μ ^ 2 ^ s = μ := by
    intro μ
    set ν : Fˣ := μ ^ 2 ^ s with hν
    set D₁ := dHom F (axisOf j) μ with hD₁
    set D₂ := dHom F (axisOf j) ν with hD₂
    have hw := h D₁ (hd μ)
    rw [frobAut_pow_dHom] at hw
    set w := D₁ * u * D₂⁻¹ * u⁻¹ with hwdef
    have hwC := hS.A_le_C (by rwa [rootA_axisOf]) 
    have hz1 : rootCoord F (axisOf j) 1 * w = w * rootCoord F (axisOf j) 1 :=
      Subgroup.mem_centralizer_iff.mp hwC _ (hS.coord_mem 1)
    have h1 : u⁻¹ * rootCoord F (axisOf j) 1 * u = rootCoord F (axisOf j) 1 := by
      calc u⁻¹ * rootCoord F (axisOf j) 1 * u = u⁻¹ * (rootCoord F (axisOf j) 1 * u) :=
            mul_assoc _ _ _
        _ = u⁻¹ * (u * rootCoord F (axisOf j) 1) := by rw [hcen 1]
        _ = rootCoord F (axisOf j) 1 := inv_mul_cancel_left u _
    have h2 : D₂⁻¹ * rootCoord F (axisOf j) 1 * D₂ =
        rootCoord F (axisOf j) (((ν⁻¹ : Fˣ) : F) ^ 2 * 1) := by
      have := hS.d_coord ν⁻¹ 1
      rwa [map_inv, inv_inv] at this
    set e : F := ((ν⁻¹ : Fˣ) : F) ^ 2 * 1 with he
    have h3 : u * rootCoord F (axisOf j) e * u⁻¹ = rootCoord F (axisOf j) e := by
      rw [hcen e, mul_inv_cancel_right]
    have h4 : D₁ * rootCoord F (axisOf j) e * D₁⁻¹ =
        rootCoord F (axisOf j) ((μ : F) ^ 2 * e) := hS.d_coord μ e
    have h5 : w * rootCoord F (axisOf j) 1 * w⁻¹ = rootCoord F (axisOf j) ((μ : F) ^ 2 * e) := by
      calc w * rootCoord F (axisOf j) 1 * w⁻¹
          = D₁ * (u * (D₂⁻¹ * (u⁻¹ * rootCoord F (axisOf j) 1 * u) * D₂) * u⁻¹) * D₁⁻¹ := by
            rw [hwdef]; group
        _ = rootCoord F (axisOf j) ((μ : F) ^ 2 * e) := by rw [h1, h2, h3, h4]
    have h6 : w * rootCoord F (axisOf j) 1 * w⁻¹ = rootCoord F (axisOf j) 1 := by
      rw [← hz1, mul_inv_cancel_right]
    have h7 : (μ : F) ^ 2 * e = 1 :=
      rootCoord_injective' (axisOf j) (h5.symm.trans h6)
    have h8 : ((μ : F) * ((ν⁻¹ : Fˣ) : F)) ^ 2 = 1 := by
      rw [mul_pow]
      simpa [he] using h7
    have h9 := eq_of_sq_eq_one h8
    have h10 : (μ : F) = (ν : F) := by
      rw [Units.val_inv_eq_inv_val] at h9
      exact (mul_inv_eq_one₀ ν.ne_zero).mp h9
    exact (Units.ext h10).symm
  apply frobAut_pow_eq_one_of_fix
  intro x
  by_cases hx : x = 0
  · rw [hx]
    exact zero_pow (pow_ne_zero _ two_ne_zero)
  · have := congrArg (fun y : Fˣ => (y : F)) (key (Units.mk0 x hx))
    simpa using this

end Torus

section Gens

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem mem_centerOf_of_commute_gens {z : antiSp F} (hz : z ∈ antiUnipotent F)
    (h1 : z * uElt 1 0 0 0 = uElt 1 0 0 0 * z) (h2 : z * uElt 0 0 0 1 = uElt 0 0 0 1 * z) :
    z ∈ centerOf (antiUnipotent F) := by
  apply mem_centerOf_of_mem_Z₀
  obtain ⟨a, b, c, d, rfl⟩ := hz
  have e1 := (commute_uElt_iff (a := 1) (b := 0) (c := 0) (d := 0) (a' := a) (b' := b) (c' := c)
    (d' := d) h1).1
  have e2 := (commute_uElt_iff (a := 0) (b := 0) (c := 0) (d := 1) (a' := a) (b' := b) (c' := c)
    (d' := d) h2).1
  have hd : d = 0 := by linear_combination -e1
  have ha : a = 0 := by linear_combination e2
  exact ⟨b, c, by rw [ha, hd]⟩

theorem uElt_mem_U0 {m : ℕ} {a b c d : F} (ha : a ^ 2 ^ m = a) (hb : b ^ 2 ^ m = b)
    (hc : c ^ 2 ^ m = c) (hd : d ^ 2 ^ m = d) :
    uElt a b c d ∈ (antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) := by
  refine ⟨⟨a, b, c, d, rfl⟩, ?_⟩
  show (frobAut F ^ m) (uElt a b c d) = uElt a b c d
  rw [frobAut_pow_uElt, ha, hb, hc, hd]

theorem iRep_mem_commutator {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card F = 2 ^ (2 * m)) (k : Fin 3) :
    iRep F k ∈ ⁅(antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)),
      (antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨σ, hσ, -, -, hcard⟩ := card_descentField_frob (F := F) (by omega) hK
  obtain ⟨t, htσ, ht0, ht1⟩ := exists_fixed_ne hm hcard
  have hfix : ∀ x ∈ descentField σ, x ^ 2 ^ m = x := fun x hx => by
    rw [← hσ]
    exact mem_descentField.mp hx
  have htF : t ∈ descentField σ := mem_descentField.mpr htσ
  have h1F : (1 : F) ∈ descentField σ := Subfield.one_mem _
  have ht1' : t + 1 ≠ 0 := by
    intro h
    apply ht1
    linear_combination h - h2
  have hβ₁ : t / (t + 1) ∈ descentField σ :=
    Subfield.div_mem _ htF (Subfield.add_mem _ htF h1F)
  have hβ₂ : 1 / (t + 1) ∈ descentField σ :=
    Subfield.div_mem _ h1F (Subfield.add_mem _ htF h1F)
  have hβ₃ : 1 / (t + 1) / t ∈ descentField σ := Subfield.div_mem _ hβ₂ htF
  have hU0 : ∀ {a b c d : F}, a ∈ descentField σ → b ∈ descentField σ → c ∈ descentField σ →
      d ∈ descentField σ → uElt a b c d ∈
        (antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) :=
    fun ha hb hc hd => uElt_mem_U0 (hfix _ ha) (hfix _ hb) (hfix _ hc) (hfix _ hd)
  have h0F : (0 : F) ∈ descentField σ := Subfield.zero_mem _
  have hc1 : ⁅uElt (1 : F) 0 0 0, uElt (0 : F) 0 0 (t / (t + 1))⁆ ∈ ⁅(antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)), (antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆ :=
    Subgroup.commutator_mem_commutator (hU0 h1F h0F h0F h0F) (hU0 h0F h0F h0F hβ₁)
  have hc2 : ⁅uElt t 0 0 0, uElt (0 : F) 0 0 (1 / (t + 1) / t)⁆ ∈ ⁅(antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)), (antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆ :=
    Subgroup.commutator_mem_commutator (hU0 htF h0F h0F h0F) (hU0 h0F h0F h0F hβ₃)
  have hc3 : ⁅uElt (1 : F) 0 0 0, uElt (0 : F) 0 0 1⁆ ∈ ⁅(antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)), (antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆ :=
    Subgroup.commutator_mem_commutator (hU0 h1F h0F h0F h0F) (hU0 h0F h0F h0F h1F)
  have hi2 : uElt (0 : F) 1 1 0 ∈ ⁅(antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)), (antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆ := by
    have e : ⁅uElt (1 : F) 0 0 0, uElt (0 : F) 0 0 1⁆ = uElt 0 1 1 0 := by
      rw [commutator_uElt]
      congr 1 <;> ring
    rwa [e] at hc3
  have hi0 : uElt (0 : F) 1 0 0 ∈ ⁅(antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)), (antiUnipotent F ⊓
      fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆ := by
    have e : ⁅uElt (1 : F) 0 0 0, uElt (0 : F) 0 0 (t / (t + 1))⁆ *
        ⁅uElt t 0 0 0, uElt (0 : F) 0 0 (1 / (t + 1) / t)⁆ = uElt 0 1 0 0 := by
      rw [commutator_uElt, commutator_uElt, uElt_mul]
      have e1 : t / (t + 1) + 1 / (t + 1) = 1 := by
        rw [← add_div]
        exact div_self ht1'
      have e2 : t / (t + 1) + t * (1 / (t + 1)) = 0 := by
        rw [mul_one_div, ← two_mul, h2, zero_mul]
      have e3 : t * (1 / (t + 1) / t) = 1 / (t + 1) := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ ht0
      congr 1
      · ring
      · rw [e3]
        linear_combination e1
      · rw [show (t : F) ^ 2 * (1 / (t + 1) / t) = t * (1 / (t + 1)) by rw [sq, mul_assoc, e3]]
        linear_combination e2
      · ring
    rw [← e]
    exact mul_mem hc1 hc2
  fin_cases k
  · exact hi0
  · have e : uElt (0 : F) 1 0 0 * uElt 0 1 1 0 = uElt 0 0 1 0 := by
      rw [uElt_mul]
      congr 1 <;> first | ring1 | (linear_combination h2)
    show uElt (0 : F) 0 1 0 ∈ _
    rw [← e]
    exact mul_mem hi0 hi2
  · exact hi2

end Gens

section AutForm

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem aut_form_antiSp {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n) (α : MulAut (antiSp F))
    (h : (∀ x, α x ∈ Rrad F 0 ↔ x ∈ Rrad F 0) ∨ (∀ x, α x ∈ Rrad F 1 ↔ x ∈ Rrad F 1)) :
    ∃ (g : antiSp F) (k : ℕ), α = MulAut.conj g * frobAut F ^ k := by
  rcases h with h | h
  · obtain ⟨g, -, k, -, e⟩ := exists_conj_mul_frobAut_pow hn hK (axisOf 0) α
      (by rw [rootA_axisOf]; exact mem_autStab.mpr h)
    exact ⟨g, k, e⟩
  · obtain ⟨g, -, k, -, e⟩ := exists_conj_mul_frobAut_pow hn hK (axisOf 1) α
      (by rw [rootA_axisOf]; exact mem_autStab.mpr h)
    exact ⟨g, k, e⟩

end AutForm

section Data

variable {F : Type} [Field F] [Finite F] [CharP F 2]

structure SpOutXData (m : ℕ) (U : Subgroup (antiSp F)) (R : Fin 2 → Subgroup (antiSp F))
    (i : Fin 3 → antiSp F) : Prop where
  card_F : Nat.card F = 2 ^ (2 * m)
  U_fr : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ U ↔ x ∈ U
  R_fr : ∀ (j : Fin 2) (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ R j ↔ x ∈ R j
  i_fr : ∀ (k : ℕ) (a : Fin 3), (frobAut F ^ k) (i a) = i a
  aut_form : ∀ α : MulAut (antiSp F),
    ((∀ x, α x ∈ R 0 ↔ x ∈ R 0) ∨ (∀ x, α x ∈ R 1 ↔ x ∈ R 1)) →
      ∃ (g : antiSp F) (k : ℕ), α = MulAut.conj g * frobAut F ^ k
  card_R : ∀ j, Nat.card (R j) = Nat.card F ^ 3
  elem_le : ∀ A : Subgroup (antiSp F), A ≤ U → (∀ x ∈ A, x * x = 1) → A ≤ R 0 ∨ A ≤ R 1
  noninv : ∀ A : Subgroup (antiSp F), A ≤ U → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    (∃ x ∈ A, x * x ≠ 1) → Nat.card A ≤ 2 * Nat.card F ^ 2
  torus : ∀ (j : Fin 2) (s : ℕ), ∀ u ∈ U,
    (∀ x ∈ Subgroup.normalizer (R j : Set (antiSp F)),
      x * u * ((frobAut F ^ s) x)⁻¹ * u⁻¹ ∈ R j) → frobAut F ^ s = 1
  cent_bound : ∀ (s : ℕ), frobAut F ^ s ≠ 1 → ∀ u₀ ∈ U, ∀ B : Subgroup (antiSp F), B ≤ U →
    (∀ b ∈ B, u₀ * (frobAut F ^ s) b * u₀⁻¹ = b) → Nat.card B ≤ Nat.card F ^ 2
  moves : ∀ s : ℕ, frobAut F ^ s ≠ 1 → ∃ u ∈ U, (frobAut F ^ s) u ≠ u
  gens : ∃ a d : antiSp F, a ∈ U ∧ d ∈ U ∧ (∀ k, (frobAut F ^ k) a = a) ∧
    (∀ k, (frobAut F ^ k) d = d) ∧
    ∀ z ∈ U, z * a = a * z → z * d = d * z → z ∈ centerOf U
  fix_two : twoPart (fixedSubgroup (frobAut F ^ m)) = 2 ^ (4 * m)
  U0_ge : 2 ^ (4 * m) ≤ Nat.card (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))

theorem SpOutXData.swap {m : ℕ} {U : Subgroup (antiSp F)} {R : Fin 2 → Subgroup (antiSp F)}
    {i : Fin 3 → antiSp F} (h : SpOutXData m U R i) :
    SpOutXData m U ![R 1, R 0] ![i 1, i 0, i 2] where
  card_F := h.card_F
  U_fr := h.U_fr
  R_fr j k x := by
    fin_cases j
    · exact h.R_fr 1 k x
    · exact h.R_fr 0 k x
  i_fr k a := by
    fin_cases a
    · exact h.i_fr k 1
    · exact h.i_fr k 0
    · exact h.i_fr k 2
  aut_form α hα := h.aut_form α hα.symm
  card_R j := by
    fin_cases j
    · exact h.card_R 1
    · exact h.card_R 0
  elem_le A hA he := (h.elem_le A hA he).symm
  noninv := h.noninv
  torus j s u hu hx := by
    fin_cases j
    · exact h.torus 1 s u hu hx
    · exact h.torus 0 s u hu hx
  cent_bound := h.cent_bound
  moves := h.moves
  gens := h.gens
  fix_two := h.fix_two
  U0_ge := h.U0_ge

theorem spOutXData_antiSp {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card F = 2 ^ (2 * m)) :
    SpOutXData m (antiUnipotent F) (Rrad F) (iRep F) := by
  have hn : 2 ≤ 2 * m := by omega
  refine
    { card_F := hK
      U_fr := frobAut_pow_mem_antiUnipotent_iff
      R_fr := ?_
      i_fr := fun k a => frobAut_pow_iRep k a
      aut_form := ?_
      card_R := ?_
      elem_le := fun A hA he => elementary_le_radA1_or_radA2 hA he
      noninv := ?_
      torus := fun j s u hu h => frobAut_pow_eq_one_of_torus hn hK j s hu h
      cent_bound := ?_
      moves := ?_
      gens := ?_
      fix_two := twoPart_fixedSubgroup_frob hm hK
      U0_ge := card_U0_ge hm hK }
  · intro j k x
    fin_cases j
    · exact frobAut_pow_mem_iff frobAut_mem_radA1_iff k x
    · exact frobAut_pow_mem_iff frobAut_mem_radA2_iff k x
  · intro α hα
    exact aut_form_antiSp hn hK α hα
  · intro j
    obtain ⟨-, h1, h2, -⟩ := card_radicals (K := F)
    fin_cases j
    · exact h1
    · exact h2
  · intro A hAU hab ⟨x, hx, hx2⟩
    exact card_abelian_le_of_noninvolution hAU hab hx hx2
  · intro s hs u₀ hu₀ B hB hfix
    exact card_centralized_le hs hu₀ hB hfix
  · intro s hs
    have : ∃ x : F, x ^ 2 ^ s ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hs (frobAut_pow_eq_one_of_fix hcon)
    obtain ⟨x, hx⟩ := this
    refine ⟨uElt x 0 0 0, ⟨x, 0, 0, 0, rfl⟩, fun h => hx ?_⟩
    rw [frobAut_pow_uElt] at h
    have := (uElt_inj h).1
    simpa using this
  · refine ⟨uElt 1 0 0 0, uElt 0 0 0 1, ⟨1, 0, 0, 0, rfl⟩, ⟨0, 0, 0, 1, rfl⟩, fun k => ?_,
      fun k => ?_, fun z hz h1 h2 => mem_centerOf_of_commute_gens hz h1 h2⟩
    · rw [frobAut_pow_uElt]
      simp
    · rw [frobAut_pow_uElt]
      simp

end Data

end SpOut2

end CFSG.Quasithin.H13.F431
