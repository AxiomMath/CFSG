module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefs

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

private abbrev a8lmF : Type := GaloisField 2 3

private theorem a8lm_card_units : Nat.card a8lmFˣ = 7 := by
  rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]
  norm_num

private theorem a8lm_units_pow_seven (u : a8lmFˣ) : u ^ 7 = 1 := by
  have h := orderOf_dvd_natCard u
  rw [a8lm_card_units] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

private theorem a8lm_center_eq_bot :
    Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) a8lmF) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at ha
  obtain ⟨r, hr, hrA⟩ := ha
  have hr4 : r ^ 4 = 1 := by
    simpa using hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 4 ≠ 0)] at hr4
    exact one_ne_zero hr4.symm
  have hr7 : r ^ 7 = 1 := by
    have h := a8lm_units_pow_seven (Units.mk0 r hr0)
    have h' := congrArg (fun z : a8lmFˣ => (z : a8lmF)) h
    simpa [Units.val_pow_eq_pow_val] using h'
  have hr1 : r = 1 := by
    have h := (pow_gcd_eq_one (a := r) (m := 4) (n := 7)).mpr ⟨hr4, hr7⟩
    simpa using h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  have hcoe : (↑a : Matrix (Fin (3 + 1)) (Fin (3 + 1)) a8lmF) = 1 := by
    rw [← hrA, hr1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  rw [hcoe]

private theorem a8lm_phi_injective {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G)
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) a8lmF)) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro a ha
  have hc := hker ha
  rw [a8lm_center_eq_bot, Subgroup.mem_bot] at hc
  exact hc

private noncomputable def a8lmdiagSL (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1) :
    SpecialLinearGroup (Fin (3 + 1)) a8lmF :=
  ⟨diagonal (fun i => (u i : a8lmF)), by
    rw [det_diagonal]
    simpa using congrArg (fun z : a8lmFˣ => (z : a8lmF)) h⟩

private theorem a8lm_coe_diagSL (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1) :
    (↑(a8lmdiagSL u h) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) a8lmF) =
      diagonal (fun i => (u i : a8lmF)) := rfl

private theorem a8lmdiagSL_conj_comm (w : Fin 4 → a8lmFˣ) (u : Fin 4 → a8lmFˣ)
    (h : ∏ i, u i = 1) : ggDiagConj w (a8lmdiagSL u h) = a8lmdiagSL u h := by
  apply Subtype.ext
  ext i j
  rw [ggDiagConj_apply, a8lm_coe_diagSL]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rw [Units.val_inv_eq_inv_val]
    field_simp
  · rw [Matrix.diagonal_apply_ne _ hij, mul_zero, zero_mul]

private theorem a8lmdiagSL_pow_seven (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1) :
    (a8lmdiagSL u h) ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, a8lm_coe_diagSL, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
  congr 1
  funext i
  rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, a8lm_units_pow_seven, Units.val_one]

private theorem a8lmdiagSL_conj (d : Fin 4 → a8lmFˣ) (hd : ∏ i, d i = 1)
    (s : SpecialLinearGroup (Fin (3 + 1)) a8lmF) :
    a8lmdiagSL d hd * s * (a8lmdiagSL d hd)⁻¹ = ggDiagConj d s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, a8lm_coe_diagSL,
    coe_ggDiagConj, TypeA.coe_inv_SL_of_diagonal (a8lm_coe_diagSL d hd)]
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]

private theorem a8lmdiagSL_inv (d : Fin 4 → a8lmFˣ) (hd : ∏ i, d i = 1)
    (hd' : ∏ i, d⁻¹ i = 1) :
    (a8lmdiagSL d hd)⁻¹ = a8lmdiagSL d⁻¹ hd' := by
  apply Subtype.ext
  rw [TypeA.coe_inv_SL_of_diagonal (a8lm_coe_diagSL d hd), a8lm_coe_diagSL]
  congr 1
  funext i
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]

private theorem a8lmdiagSL_congr {u u' : Fin 4 → a8lmFˣ} (h : u = u')
    (hu : ∏ i, u i = 1) (hu' : ∏ i, u' i = 1) : a8lmdiagSL u hu = a8lmdiagSL u' hu' := by
  subst h; rfl

private theorem a8lmdiagSL_conj_inv (d : Fin 4 → a8lmFˣ) (hd : ∏ i, d i = 1)
    (hd' : ∏ i, d⁻¹ i = 1) (s : SpecialLinearGroup (Fin (3 + 1)) a8lmF) :
    (a8lmdiagSL d hd)⁻¹ * s * a8lmdiagSL d hd = ggDiagConj d⁻¹ s := by
  have h2 : a8lmdiagSL d hd = (a8lmdiagSL d⁻¹ hd')⁻¹ := by
    rw [← inv_inv (a8lmdiagSL d hd), a8lmdiagSL_inv d hd hd']
  rw [a8lmdiagSL_inv d hd hd', h2]
  exact a8lmdiagSL_conj d⁻¹ hd' s

private theorem a8lm_diag_mem_Bs {G : Type} [Group G] {Bs : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G}
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1) : φ (a8lmdiagSL u h) ∈ Bs := by
  apply hSC _ _ _
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨w, hw⟩ := hdiag b hb
    calc b * φ (a8lmdiagSL u h) = b * φ (a8lmdiagSL u h) * b⁻¹ * b := by group
      _ = φ (ggDiagConj w (a8lmdiagSL u h)) * b := by rw [hw]
      _ = φ (a8lmdiagSL u h) * b := by rw [a8lmdiagSL_conj_comm]
  · rw [← map_pow, a8lmdiagSL_pow_seven, map_one]

private noncomputable def a8lmchi (g : a8lmFˣ)
    (hg : ∀ x : a8lmFˣ, x ∈ Subgroup.zpowers g) : ZMod 7 → a8lmFˣ :=
  fun n => (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units) (Multiplicative.ofAdd n)

private theorem a8lmchi_zero (g : a8lmFˣ) (hg : ∀ x : a8lmFˣ, x ∈ Subgroup.zpowers g) :
    a8lmchi g hg 0 = 1 := by
  show (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units) (Multiplicative.ofAdd 0) = 1
  rw [show Multiplicative.ofAdd (0 : ZMod 7) = 1 from rfl, map_one]

private theorem a8lmchi_add (g : a8lmFˣ) (hg : ∀ x : a8lmFˣ, x ∈ Subgroup.zpowers g)
    (a b : ZMod 7) : a8lmchi g hg (a + b) = a8lmchi g hg a * a8lmchi g hg b := by
  show (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units) (Multiplicative.ofAdd (a + b)) =
    (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units) (Multiplicative.ofAdd a) *
      (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units) (Multiplicative.ofAdd b)
  rw [← map_mul]
  rfl

private theorem a8lmchi_injective (g : a8lmFˣ)
    (hg : ∀ x : a8lmFˣ, x ∈ Subgroup.zpowers g) : Function.Injective (a8lmchi g hg) := by
  intro a b hab
  have h : Multiplicative.ofAdd a = Multiplicative.ofAdd b :=
    (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units).injective hab
  exact Multiplicative.ofAdd.injective h

private theorem a8lmchi_sum {ι : Type} (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (s : Finset ι)
    (f : ι → ZMod 7) : (∏ i ∈ s, χ (f i)) = χ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hχ0]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, hχadd, ih]

private noncomputable def a8lmxPowSub {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    ZMod 7 → Subgroup.zpowers x := fun n =>
  (zmodMulEquivOfGenerator (g := (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x))
      (fun y => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩)
      (by rw [Nat.card_zpowers, hord])) (Multiplicative.ofAdd n)

private noncomputable def a8lmxPow {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    ZMod 7 → G := fun n => (a8lmxPowSub x hord n : G)

private theorem a8lmxPow_zero {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    a8lmxPow x hord 0 = 1 := by
  simp only [a8lmxPow, a8lmxPowSub]
  rw [show Multiplicative.ofAdd (0 : ZMod 7) = 1 from rfl, map_one]
  rfl

private theorem a8lmxPow_add {G : Type} [Group G] (x : G) (hord : orderOf x = 7)
    (a b : ZMod 7) : a8lmxPow x hord (a + b) = a8lmxPow x hord a * a8lmxPow x hord b := by
  simp only [a8lmxPow, a8lmxPowSub]
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

private theorem a8lmxPow_injective {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    Function.Injective (a8lmxPow x hord) := by
  intro a b hab
  have h : a8lmxPowSub x hord a = a8lmxPowSub x hord b := Subtype.ext hab
  have h2 := (zmodMulEquivOfGenerator (g := (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x))
      (fun y => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩)
      (by rw [Nat.card_zpowers, hord])).injective h
  exact Multiplicative.ofAdd.injective h2

private theorem a8lmxPow_mem {G : Type} [Group G] (x : G) (hord : orderOf x = 7)
    (m : ZMod 7) : a8lmxPow x hord m ∈ Subgroup.zpowers x :=
  (a8lmxPowSub x hord m).2

private def a8lmM (v : Fin 4 → ZMod 7) : ZMod 7 := 2 * ∑ i, v i

private theorem a8lmchi_prod_univ {ι : Type} [Fintype ι] (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (f : ι → ZMod 7) :
    (∏ i, χ (f i)) = χ (∑ i, f i) := by
  have h := a8lmchi_sum χ hχadd hχ0 (Finset.univ : Finset ι) f
  simpa using h

private noncomputable def a8lmdiagVec (χ : ZMod 7 → a8lmFˣ) (v : Fin 4 → ZMod 7) :
    Fin 4 → a8lmFˣ := fun i => χ (v i - a8lmM v)

private theorem a8lmM_add (v w : Fin 4 → ZMod 7) : a8lmM (v + w) = a8lmM v + a8lmM w := by
  simp only [a8lmM, Pi.add_apply, Finset.sum_add_distrib]
  ring

private theorem a8lmdiagVec_prod (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (v : Fin 4 → ZMod 7) :
    ∏ i, a8lmdiagVec χ v i = 1 := by
  have h := a8lmchi_prod_univ χ hχadd hχ0 (fun i => v i - a8lmM v)
  simp only [a8lmdiagVec]
  rw [h]
  have hsum : (∑ i : Fin 4, (v i - a8lmM v)) = 0 := by
    have hsplit : (∑ i : Fin 4, (v i - a8lmM v)) =
        (∑ i : Fin 4, v i) - (∑ i : Fin 4, a8lmM v) :=
      Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i => v i) (g := fun _ => a8lmM v)
    have hconst : (∑ i : Fin 4, a8lmM v) = (4 : ℕ) • a8lmM v := by
      have h := Finset.sum_const (s := (Finset.univ : Finset (Fin 4))) (b := a8lmM v)
      simpa using h
    rw [hsplit, hconst]
    simp only [a8lmM, nsmul_eq_mul]
    ring_nf
    rw [show (7 : ZMod 7) = 0 from rfl]
    ring
  rw [hsum, hχ0]

private theorem a8lmdiagVec_add (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (v w : Fin 4 → ZMod 7) :
    a8lmdiagVec χ (v + w) = a8lmdiagVec χ v * a8lmdiagVec χ w := by
  funext i
  have harg : (v + w) i - a8lmM (v + w) = (v i - a8lmM v) + (w i - a8lmM w) := by
    rw [a8lmM_add, Pi.add_apply]; ring
  simp only [a8lmdiagVec, harg, hχadd, Pi.mul_apply]

private theorem a8lmdiagVec_mul_prod (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (v w : Fin 4 → ZMod 7) :
    ∏ i, (a8lmdiagVec χ v * a8lmdiagVec χ w) i = 1 := by
  simp only [Pi.mul_apply]
  rw [Finset.prod_mul_distrib, a8lmdiagVec_prod χ hχadd hχ0 v,
    a8lmdiagVec_prod χ hχadd hχ0 w, mul_one]

private theorem a8lmdiagSL_mul (u v : Fin 4 → a8lmFˣ) (hu : ∏ i, u i = 1)
    (hv : ∏ i, v i = 1) (huv : ∏ i, (u * v) i = 1) :
    a8lmdiagSL (u * v) huv = a8lmdiagSL u hu * a8lmdiagSL v hv := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, a8lm_coe_diagSL, a8lm_coe_diagSL, a8lm_coe_diagSL,
    Matrix.diagonal_mul_diagonal]
  rfl

private noncomputable def a8lmModelFun {G : Type} [Group G] {Bs : Subgroup G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G)
    (χ : ZMod 7 → a8lmFˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1), φ (a8lmdiagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs) (v : Fin 4 → ZMod 7) : ↥Bs :=
  ⟨φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) * xPow (a8lmM v),
    Bs.mul_mem (hdmem _ _) (hxmem _)⟩

private theorem a8lmModelFun_add {G : Type} [Group G] {Bs : Subgroup G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G)
    (χ : ZMod 7 → a8lmFˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1), φ (a8lmdiagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs)
    (hxadd : ∀ a b, xPow (a + b) = xPow a * xPow b)
    (hxcomm : ∀ (m : ZMod 7) (s : SpecialLinearGroup (Fin (3 + 1)) a8lmF),
      xPow m * φ s = φ s * xPow m)
    (v w : Fin 4 → ZMod 7) :
    a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v + w) =
      a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v *
        a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem w := by
  apply Subtype.ext
  simp only [a8lmModelFun, Subgroup.coe_mul]
  have hdiag : a8lmdiagSL (a8lmdiagVec χ (v + w)) (a8lmdiagVec_prod χ hχadd hχ0 (v + w)) =
      a8lmdiagSL (a8lmdiagVec χ v * a8lmdiagVec χ w)
        (a8lmdiagVec_mul_prod χ hχadd hχ0 v w) := by
    apply Subtype.ext
    rw [a8lm_coe_diagSL, a8lm_coe_diagSL]
    exact congrArg (fun u : Fin 4 → a8lmFˣ => diagonal (fun i => (u i : a8lmF)))
      (a8lmdiagVec_add χ hχadd v w)
  have hmul : a8lmdiagSL (a8lmdiagVec χ v * a8lmdiagVec χ w)
        (a8lmdiagVec_mul_prod χ hχadd hχ0 v w) =
      a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v) *
        a8lmdiagSL (a8lmdiagVec χ w) (a8lmdiagVec_prod χ hχadd hχ0 w) :=
    a8lmdiagSL_mul _ _ _ _ _
  rw [hdiag, hmul, map_mul, a8lmM_add, hxadd]
  set A := φ (a8lmdiagSL (a8lmdiagVec χ v) _) with hA
  set B := φ (a8lmdiagSL (a8lmdiagVec χ w) _) with hB
  set X := xPow (a8lmM v) with hX
  set Y := xPow (a8lmM w) with hY
  change A * B * (X * Y) = A * X * (B * Y)
  rw [mul_assoc, ← mul_assoc B X Y, ← hxcomm (a8lmM v) (a8lmdiagSL (a8lmdiagVec χ w) _)]
  rw [← hX, ← hB]
  group

private theorem a8lmchi_nsmul (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (n : ℕ) (a : ZMod 7) :
    (χ a) ^ n = χ (n • a) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, hχ0]
  | succ n ih => rw [pow_succ, ih, ← hχadd, succ_nsmul]

private theorem a8lmchi_neg (χ : ZMod 7 → a8lmFˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (c : ZMod 7) :
    χ (-c) = (χ c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hχadd, show -c + c = 0 from neg_add_cancel c, hχ0]

private theorem a8lmchi_surjective (g : a8lmFˣ)
    (hg : ∀ x : a8lmFˣ, x ∈ Subgroup.zpowers g) : Function.Surjective (a8lmchi g hg) := by
  intro y
  obtain ⟨m, hm⟩ := (zmodMulEquivOfGenerator (g := g) hg a8lm_card_units).surjective y
  obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective m
  exact ⟨n, hm⟩

private theorem a8lmxPow_surjective {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    ∀ c ∈ Subgroup.zpowers x, ∃ m, a8lmxPow x hord m = c := by
  intro c hc
  have hsurj : Function.Surjective (a8lmxPowSub x hord) := by
    intro y
    obtain ⟨m, hm⟩ := (zmodMulEquivOfGenerator
        (g := (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x))
        (fun y => by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
          exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩)
        (by rw [Nat.card_zpowers, hord])).surjective y
    obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective m
    exact ⟨n, hm⟩
  obtain ⟨m, hm⟩ := hsurj ⟨c, hc⟩
  exact ⟨m, congrArg Subtype.val hm⟩

private theorem a8lmdiagSL_one :
    a8lmdiagSL (1 : Fin 4 → a8lmFˣ) (by simp) = 1 := by
  apply Subtype.ext
  rw [a8lm_coe_diagSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.diagonal_apply_eq, Matrix.one_apply]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

private theorem a8lmModelFun_zero {G : Type} [Group G] {Bs : Subgroup G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G)
    (χ : ZMod 7 → a8lmFˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1), φ (a8lmdiagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs) (hx0 : xPow 0 = 1) :
    a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem 0 = 1 := by
  apply Subtype.ext
  simp only [a8lmModelFun, Subtype.coe_mk, Subgroup.coe_one]
  have hM0 : a8lmM (0 : Fin 4 → ZMod 7) = 0 := by simp [a8lmM]
  have hu0 : a8lmdiagVec χ (0 : Fin 4 → ZMod 7) = 1 := by
    funext i
    simp [a8lmdiagVec, hM0, hχ0]
  rw [hM0, hx0]
  have hd1 : a8lmdiagSL (a8lmdiagVec χ (0 : Fin 4 → ZMod 7))
      (a8lmdiagVec_prod χ hχadd hχ0 0) = 1 := by
    have hh : a8lmdiagSL (a8lmdiagVec χ (0 : Fin 4 → ZMod 7))
        (a8lmdiagVec_prod χ hχadd hχ0 0) = a8lmdiagSL (1 : Fin 4 → a8lmFˣ) (by simp) :=
      a8lmdiagSL_congr hu0 _ _
    rw [hh, a8lmdiagSL_one]
  rw [hd1, map_one, one_mul]

private theorem a8lmModelFun_surjective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G) (hrange : φ.range = L)
    (χ : ZMod 7 → a8lmFˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (hχsurj : Function.Surjective χ) (hχinj : Function.Injective χ)
    (xPow : ZMod 7 → G)
    (hxsurj : ∀ c ∈ Subgroup.zpowers x, ∃ m, xPow m = c)
    (hdmem : ∀ (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1), φ (a8lmdiagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs)
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hz : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (b : ↥Bs) : ∃ v : Fin 4 → ZMod 7, a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v = b := by
  obtain ⟨h, hh⟩ := hdiag b b.2
  set p : a8lmFˣ := ∏ i, h i with hp
  obtain ⟨c, hc⟩ := hχsurj p
  set lam : a8lmFˣ := χ (-(2 * c)) with hlam
  have hlam_pow : lam ^ 4 = p⁻¹ := by
    rw [hlam, a8lmchi_nsmul χ hχadd hχ0 4 (-(2 * c))]
    have h4 : (4 : ℕ) • (-(2 * c) : ZMod 7) = -c := by
      rw [nsmul_eq_mul]
      have h8 : (8 : ZMod 7) = 1 := by decide
      calc
        (4 : ZMod 7) * (-(2 * c)) = -((8 : ZMod 7) * c) := by ring
        _ = -(1 * c) := by rw [h8]
        _ = -c := by ring
    rw [h4, a8lmchi_neg χ hχadd hχ0 c, hc]
  set d : Fin 4 → a8lmFˣ := (fun _ => lam) * h with hd
  have hdprod : ∏ i, d i = 1 := by
    simp only [hd, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← hp, hlam_pow, inv_mul_cancel]
  have hd' : ∏ i, d⁻¹ i = 1 := by
    simp only [Pi.inv_apply, Finset.prod_inv_distrib, hdprod, inv_one]
  set D : SpecialLinearGroup (Fin (3 + 1)) a8lmF := a8lmdiagSL d hdprod with hD
  have hDmem : φ D ∈ Bs := hdmem d hdprod
  set c0 : G := (φ D)⁻¹ * (b : G) with hc0
  have hc0Bs : c0 ∈ Bs := Bs.mul_mem (Bs.inv_mem hDmem) b.2
  have hc0C : c0 ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← hrange] at hs
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hs
    have hconj : c0 * φ t * c0⁻¹ = φ t := by
      rw [hc0]
      calc (φ D)⁻¹ * (b : G) * φ t * ((φ D)⁻¹ * (b : G))⁻¹
          = (φ D)⁻¹ * ((b : G) * φ t * (b : G)⁻¹) * φ D := by group
        _ = (φ D)⁻¹ * φ (ggDiagConj h t) * φ D := by rw [hh t]
        _ = φ ((a8lmdiagSL d hdprod)⁻¹ * ggDiagConj h t * a8lmdiagSL d hdprod) := by
              rw [hD, ← map_inv, ← map_mul, ← map_mul]
        _ = φ (ggDiagConj d⁻¹ (ggDiagConj h t)) := by
              rw [a8lmdiagSL_conj_inv d hdprod hd' (ggDiagConj h t)]
        _ = φ (ggDiagConj (d⁻¹ * h) t) := by rw [ggDiagConj_ggDiagConj]
        _ = φ t := by
              have hconst : d⁻¹ * h = (fun _ : Fin 4 => lam⁻¹) := by
                funext i
                simp only [hd, Pi.mul_apply, Pi.inv_apply]
                rw [_root_.mul_inv_rev]
                rw [mul_comm ((h i)⁻¹) (lam⁻¹), mul_assoc, inv_mul_cancel, mul_one]
              rw [hconst, ggDiagConj_eq_self_of_const (fun _ _ => rfl)]
    have hconj_inv : c0⁻¹ * φ t * c0 = φ t := by
      have h := congrArg (fun z => c0⁻¹ * z * c0) hconj
      rw [show c0⁻¹ * (c0 * φ t * c0⁻¹) * c0 = φ t from by group] at h
      exact h.symm
    calc φ t * c0 = c0 * (c0⁻¹ * φ t * c0) := by group
      _ = c0 * φ t := by rw [hconj_inv]
  have hc0z : c0 ∈ Subgroup.zpowers x := by
    have hmem := Subgroup.mem_inf.mpr ⟨hc0Bs, hc0C⟩
    rwa [hz] at hmem
  obtain ⟨m, hm⟩ := hxsurj c0 hc0z
  choose a ha using fun i => hχsurj (d i)
  have hprod : (∏ i, χ (a i)) = 1 := by
    rw [Finset.prod_congr rfl (fun i _ => ha i), hdprod]
  have hsum : (∑ i, a i) = 0 := by
    have h1 : χ (∑ i, a i) = χ 0 := by
      rw [← a8lmchi_prod_univ χ hχadd hχ0 a, hprod, hχ0]
    exact hχinj h1
  let v : Fin 4 → ZMod 7 := fun i => a i + m
  have hMv : a8lmM v = m := by
    simp only [a8lmM, v, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsum, mul_zero, zero_add]
    ring_nf
    rw [show (8 : ZMod 7) = 1 by decide, mul_one]
  have hdv : a8lmdiagVec χ v = d := by
    funext i
    simp only [a8lmdiagVec, v]
    rw [show a i + m - a8lmM v = a i by rw [hMv]; ring]
    exact ha i
  have hdiag_eq : a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v) = D := by
    rw [hD]
    apply Subtype.ext
    rw [a8lm_coe_diagSL, a8lm_coe_diagSL]
    congr 1
    funext i
    rw [hdv]
  refine ⟨v, ?_⟩
  apply Subtype.ext
  simp only [a8lmModelFun, Subtype.coe_mk]
  rw [hdiag_eq, hMv, hm, hc0]
  group

private theorem a8lmModelFun_injective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) a8lmF →* G) (hφinj : Function.Injective φ)
    (hrange : φ.range = L)
    (χ : ZMod 7 → a8lmFˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (hχinj : Function.Injective χ)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1), φ (a8lmdiagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs)
    (hxzer : ∀ m, xPow m = 1 → m = 0)
    (hxmz : ∀ m, xPow m ∈ Subgroup.zpowers x)
    (hLdisj : Subgroup.zpowers x ⊓ L = ⊥) {v : Fin 4 → ZMod 7}
    (hv : a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v = 1) : v = 0 := by
  have hcoe : φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) *
      xPow (a8lmM v) = 1 := by
    simpa only [a8lmModelFun, Subtype.coe_mk, Subgroup.coe_one] using
      congrArg (fun b : ↥Bs => (b : G)) hv
  have hAeq : φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) =
      (xPow (a8lmM v))⁻¹ := (eq_inv_iff_mul_eq_one).mpr hcoe
  have hAL : φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) ∈ L := by
    rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hAz : φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) ∈
      Subgroup.zpowers x := by
    rw [hAeq]; exact Subgroup.inv_mem _ (hxmz _)
  have hA1 : φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) = 1 := by
    have hmem := Subgroup.mem_inf.mpr ⟨hAz, hAL⟩
    rw [hLdisj, Subgroup.mem_bot] at hmem
    exact hmem
  have hX1 : xPow (a8lmM v) = 1 := by
    rw [hA1, one_mul] at hcoe
    exact hcoe
  have hm0 : a8lmM v = 0 := hxzer _ hX1
  have hdiag1 : a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v) = 1 := by
    apply hφinj
    rw [hA1, map_one]
  have hu1 : a8lmdiagVec χ v = 1 := by
    have hm : (fun i => (a8lmdiagVec χ v i : a8lmF)) = (fun _ => (1 : a8lmF)) := by
      have h2 : (↑(a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) a8lmF) = 1 := by
        rw [congrArg Subtype.val hdiag1, Matrix.SpecialLinearGroup.coe_one]
      rw [a8lm_coe_diagSL] at h2
      funext i
      have := congrFun (congrFun h2 i) i
      simpa [Matrix.one_apply] using this
    funext i
    apply Units.ext
    have := congrFun hm i
    simpa using this
  funext i
  have hχ1 : χ (v i - a8lmM v) = 1 := by
    simpa [a8lmdiagVec] using congrFun hu1 i
  have hz : v i - a8lmM v = 0 := hχinj (by rw [hχ1, hχ0])
  rw [hm0] at hz
  have hz' : v i - 0 = v i := sub_zero (v i)
  rw [hz'] at hz
  exact hz

private theorem a8lmxPow_one {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    a8lmxPow x hord 1 = x := by
  simp only [a8lmxPow, a8lmxPowSub]
  rw [zmodMulEquivOfGenerator_apply_ofAdd_one]

private theorem a8lm_vecMul_permMat (v : Fin 4 → ZMod 7) (σ : Equiv.Perm (Fin 4)) :
    vecMul v (a8PermMat σ) = v ∘ σ.symm := by
  funext j
  rw [Matrix.vecMul_apply_eq_sum]
  simp only [a8PermMat, Matrix.of_apply, Function.comp_apply]
  have hsingle : (∑ i : Fin 4, v i * (if σ i = j then 1 else 0)) = v (σ.symm j) := by
    refine (Finset.sum_eq_single (σ.symm j) ?_ ?_).trans ?_
    · intro i _ hi
      have hne : σ i ≠ j := by
        intro hij
        apply hi
        rw [← Equiv.symm_apply_apply σ i, hij]
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ (σ.symm j)) h
    · simp
  exact hsingle

private theorem a8lm_perm_zero_cases (σ : Equiv.Perm (Fin 4)) (h : σ 0 = 0) :
    σ = 1 ∨ σ = Equiv.swap (1 : Fin 4) 2 ∨ σ = Equiv.swap (2 : Fin 4) 3 ∨
      σ = Equiv.swap (1 : Fin 4) 2 * Equiv.swap (2 : Fin 4) 3 ∨
      σ = Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 ∨
      σ = Equiv.swap (1 : Fin 4) 2 * Equiv.swap (2 : Fin 4) 3 *
        Equiv.swap (1 : Fin 4) 2 := by
  revert σ h
  decide

theorem ggA8Nbr_lModel [Fact (Nat.Prime 7)] {G : Type} [Group G]
    {Bs L J : Subgroup G} {x : G} (hBs : IsElemAbelian 7 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    (hz : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) (hx : x ≠ 1)
    (hxBs : x ∈ Bs)
    (φ : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G) (hrange : φ.range = L)
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3)))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hJ : (φ.comp (slLowerBlockHom 3 (GaloisField 2 3))).range = J) :
    ∃ ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7),
      ι (Additive.ofMul ⟨x, hxBs⟩) = (fun _ => 1) ∧
        (∀ σ : Equiv.Perm (Fin 4), ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
          ι (Additive.ofMul (ψ b)) = vecMul (ι (Additive.ofMul b)) (a8PermMat σ)) ∧
        (∀ σ : Equiv.Perm (Fin 4), σ 0 = 0 → ∃ ψ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
          ι (Additive.ofMul (ψ b)) = vecMul (ι (Additive.ofMul b)) (a8PermMat σ)) := by
  haveI : IsCyclic a8lmFˣ := instIsCyclicUnitsOfFinite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := a8lmFˣ)
  let χ : ZMod 7 → a8lmFˣ := a8lmchi g hg
  have hχadd : ∀ a b, χ (a + b) = χ a * χ b := a8lmchi_add g hg
  have hχ0 : χ 0 = 1 := a8lmchi_zero g hg
  have hχinj : Function.Injective χ := a8lmchi_injective g hg
  have hχsurj : Function.Surjective χ := a8lmchi_surjective g hg
  have hφinj : Function.Injective φ := a8lm_phi_injective φ hker
  have hxInf : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hz]; exact Subgroup.mem_zpowers x
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hxInf).2
  have hord : orderOf x = 7 := (orderOf_eq_prime_iff).mpr ⟨hBs.2 x hxBs, hx⟩
  let xPow : ZMod 7 → G := a8lmxPow x hord
  have hxadd : ∀ a b, xPow (a + b) = xPow a * xPow b := a8lmxPow_add x hord
  have hxzer : ∀ m, xPow m = 1 → m = 0 := by
    intro m hm
    exact a8lmxPow_injective x hord (by
      rw [show a8lmxPow x hord m = 1 from hm, a8lmxPow_zero x hord])
  have hxmz : ∀ m, xPow m ∈ Subgroup.zpowers x := a8lmxPow_mem x hord
  have hxsurj : ∀ c ∈ Subgroup.zpowers x, ∃ m, xPow m = c := a8lmxPow_surjective x hord
  have hx0 : xPow 0 = 1 := a8lmxPow_zero x hord
  have hxmem : ∀ m, xPow m ∈ Bs := fun m => Subgroup.zpowers_le.mpr hxBs (hxmz m)
  have hxL : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hxC
  have hxcomm : ∀ (m : ZMod 7) (s : SpecialLinearGroup (Fin (3 + 1)) a8lmF),
      xPow m * φ s = φ s * xPow m := by
    intro m s
    exact (Subgroup.mem_centralizer_iff.mp (hxL (hxmz m)) (φ s)
      (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨s, rfl⟩)).symm
  have hdmem : ∀ (u : Fin 4 → a8lmFˣ) (h : ∏ i, u i = 1), φ (a8lmdiagSL u h) ∈ Bs :=
    fun u h => a8lm_diag_mem_Bs hSC hdiag u h
  have hZL : L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [← hrange] at hyL
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hyL
    have hsZ : s ∈ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) a8lmF) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply hφinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hyC (φ t)
        (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨t, rfl⟩)
    rw [a8lm_center_eq_bot, Subgroup.mem_bot] at hsZ
    rw [hsZ, map_one]
  have hLdisj : Subgroup.zpowers x ⊓ L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyx, hyL⟩ := Subgroup.mem_inf.mp hy
    have hmem := Subgroup.mem_inf.mpr ⟨hyL, hxL hyx⟩
    rwa [hZL, Subgroup.mem_bot] at hmem
  let Ffun : (Fin 4 → ZMod 7) → Additive ↥Bs := fun v =>
    Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v)
  have Fzero : Ffun 0 = 0 := by
    change Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem 0) = 0
    rw [a8lmModelFun_zero φ χ hχadd hχ0 xPow hdmem hxmem hx0]
    rfl
  have Fadd : ∀ v w, Ffun (v + w) = Ffun v + Ffun w := by
    intro v w
    change Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v + w)) =
      Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) +
        Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem w)
    rw [a8lmModelFun_add φ χ hχadd hχ0 xPow hdmem hxmem hxadd hxcomm v w]
    rfl
  let Fhom : (Fin 4 → ZMod 7) →+ Additive ↥Bs :=
    { toFun := Ffun, map_zero' := Fzero, map_add' := Fadd }
  have hFinj : Function.Injective Fhom := by
    intro v w hvw
    have h1 : a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v =
        a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem w := Additive.ofMul.injective hvw
    have hneg : a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (-w) =
        (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem w)⁻¹ := by
      have h := a8lmModelFun_add φ χ hχadd hχ0 xPow hdmem hxmem hxadd hxcomm (-w) w
      have h0 : -w + w = (0 : Fin 4 → ZMod 7) := by funext i; exact neg_add_cancel (w i)
      rw [h0, a8lmModelFun_zero φ χ hχadd hχ0 xPow hdmem hxmem hx0] at h
      exact (eq_inv_iff_mul_eq_one).mpr h.symm
    have hzero : a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v - w) = 1 := by
      have h := a8lmModelFun_add φ χ hχadd hχ0 xPow hdmem hxmem hxadd hxcomm v (-w)
      rw [hneg, h1, mul_inv_cancel] at h
      rw [sub_eq_add_neg]
      exact h
    exact sub_eq_zero.mp (a8lmModelFun_injective φ hφinj hrange χ hχadd hχ0 hχinj xPow
      hdmem hxmem hxzer hxmz hLdisj hzero)
  have hFsurj : Function.Surjective Fhom := by
    intro y
    obtain ⟨v, hv⟩ := a8lmModelFun_surjective φ hrange χ hχadd hχ0 hχsurj hχinj xPow
      hxsurj hdmem hxmem hdiag hz (Additive.toMul y)
    refine ⟨v, ?_⟩
    change Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) = y
    rw [hv]
    rfl
  let model : Additive ↥Bs ≃+ (Fin 4 → ZMod 7) :=
    (AddEquiv.ofBijective Fhom ⟨hFinj, hFsurj⟩).symm
  have hmodel_fun : ∀ v : Fin 4 → ZMod 7,
      model (Additive.ofMul (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v)) = v := by
    intro v
    change (AddEquiv.ofBijective Fhom ⟨hFinj, hFsurj⟩).symm (Fhom v) = v
    exact AddEquiv.symm_apply_apply (AddEquiv.ofBijective Fhom ⟨hFinj, hFsurj⟩) v
  have h2 : (2 : a8lmF) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 3 (by norm_num)) (by norm_num)
  have hslPerm_eq' : ∀ π : Equiv.Perm (Fin 4), slPerm h2 π = TypeA.permSL π.symm := by
    intro π
    apply Subtype.ext
    rw [coe_slPerm, TypeA.coe_permSL, signedPerm_one_eq_permMatrix]
    rfl
  have hslPerm_diag : ∀ (π : Equiv.Perm (Fin 4)) (u : Fin 4 → a8lmFˣ)
      (hu : ∏ k, u k = 1) (hu' : ∏ k, (u ∘ ⇑π) k = 1),
      slPerm h2 π.symm * a8lmdiagSL u hu * (slPerm h2 π.symm)⁻¹ =
        a8lmdiagSL (u ∘ ⇑π) hu' := by
    intro π u hu hu'
    apply Subtype.ext
    rw [hslPerm_eq' π.symm, Equiv.symm_symm]
    rw [TypeA.coe_permSL_conj (D := a8lmdiagSL u hu) (t := fun k => (u k : a8lmF))
      (a8lm_coe_diagSL u hu) π]
    rw [a8lm_coe_diagSL]
    rfl
  have hslPerm_mem : ∀ π : Equiv.Perm (Fin 4),
      φ (slPerm h2 π) ∈ Subgroup.normalizer (Bs : Set G) :=
    fun π => slPerm_mem_normalizer_of_actsDiag h2 hBs.2 hSC hker hdiag π
  let Ψ : Equiv.Perm (Fin 4) →* MulAut ↥Bs :=
    { toFun := fun π => ggConjAut Bs (hslPerm_mem π)
      map_one' := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        rw [ggConjAut_apply]
        simp
      map_mul' := by
        intro π π'
        refine MulEquiv.ext fun b => Subtype.ext ?_
        rw [MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, ggConjAut_apply]
        simp only [map_mul]
        group }
  have hMπ : ∀ (π : Equiv.Perm (Fin 4)) (v : Fin 4 → ZMod 7),
      a8lmM (v ∘ π) = a8lmM v := by
    intro π v
    simp only [a8lmM, Function.comp_apply]
    congr 1
    exact Equiv.sum_comp π v
  have keyΨ : ∀ (π : Equiv.Perm (Fin 4)) (v : Fin 4 → ZMod 7),
      ((Ψ π⁻¹ (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) : ↥Bs) : G) =
        ((a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ π) : ↥Bs) : G) := by
    intro π v
    change ((ggConjAut Bs (hslPerm_mem π.symm)
      (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) : ↥Bs) : G) = _
    rw [ggConjAut_apply]
    simp only [a8lmModelFun, Subtype.coe_mk]
    have hcomp : a8lmdiagVec χ v ∘ π = a8lmdiagVec χ (v ∘ π) := by
      funext k; simp only [Function.comp_apply, a8lmdiagVec]; rw [hMπ π v]
    calc φ (slPerm h2 π.symm) * (φ (a8lmdiagSL (a8lmdiagVec χ v)
          (a8lmdiagVec_prod χ hχadd hχ0 v)) * xPow (a8lmM v)) * (φ (slPerm h2 π.symm))⁻¹
        = φ (slPerm h2 π.symm) *
            φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) *
            (xPow (a8lmM v) * (φ (slPerm h2 π.symm))⁻¹) := by group
      _ = φ (slPerm h2 π.symm) *
            φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) *
            ((φ (slPerm h2 π.symm))⁻¹ * xPow (a8lmM v)) := by
            rw [show xPow (a8lmM v) * (φ (slPerm h2 π.symm))⁻¹ =
              (φ (slPerm h2 π.symm))⁻¹ * xPow (a8lmM v) from by
              rw [← map_inv]; exact hxcomm (a8lmM v) (slPerm h2 π.symm)⁻¹]
      _ = φ (slPerm h2 π.symm) *
            φ (a8lmdiagSL (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)) *
            (φ (slPerm h2 π.symm))⁻¹ * xPow (a8lmM v) := by group
      _ = φ (slPerm h2 π.symm * a8lmdiagSL (a8lmdiagVec χ v)
            (a8lmdiagVec_prod χ hχadd hχ0 v) * (slPerm h2 π.symm)⁻¹) * xPow (a8lmM v) := by
            simp only [← map_mul, ← map_inv]
      _ = φ (a8lmdiagSL (a8lmdiagVec χ (v ∘ π))
            (a8lmdiagVec_prod χ hχadd hχ0 (v ∘ π))) * xPow (a8lmM v) := by
            rw [hslPerm_diag π (a8lmdiagVec χ v) (a8lmdiagVec_prod χ hχadd hχ0 v)
              (by rw [hcomp]; exact a8lmdiagVec_prod χ hχadd hχ0 (v ∘ π))]
            rw [a8lmdiagSL_congr hcomp _ _]
      _ = ((a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ π) : ↥Bs) : G) := by
            simp only [a8lmModelFun, Subtype.coe_mk, hMπ π v]
  have hcoord : ∀ (σ : Equiv.Perm (Fin 4)) (b : ↥Bs),
      model (Additive.ofMul (Ψ σ b)) =
        vecMul (model (Additive.ofMul b)) (a8PermMat σ) := by
    intro σ b
    obtain ⟨v, hv⟩ := a8lmModelFun_surjective φ hrange χ hχadd hχ0 hχsurj hχinj xPow
      hxsurj hdmem hxmem hdiag hz b
    rw [← hv, hmodel_fun]
    have hsub : Ψ σ (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) =
        a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ σ.symm) := by
      apply Subtype.ext
      have hk := keyΨ σ.symm v
      have hσ : (σ.symm)⁻¹ = σ := Equiv.symm_symm σ
      rw [hσ] at hk
      exact hk
    calc model (Additive.ofMul (Ψ σ (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem v)))
        = model (Additive.ofMul
            (a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ σ.symm))) := by rw [hsub]
      _ = v ∘ σ.symm := hmodel_fun _
      _ = vecMul v (a8PermMat σ) := by rw [a8lm_vecMul_permMat]
  have hxval : model (Additive.ofMul ⟨x, hxBs⟩) = (fun _ => 1) := by
    have hM1 : a8lmM (fun _ : Fin 4 => (1 : ZMod 7)) = 1 := by
      rw [a8lmM]
      have hsum : (∑ i : Fin 4, (1 : ZMod 7)) = 4 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
      rw [hsum]
      norm_num
      change ((8 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
      exact (ZMod.natCast_eq_natCast_iff' 8 1 7).mpr (by norm_num)
    have hdiag1 : a8lmdiagVec χ (fun _ : Fin 4 => (1 : ZMod 7)) = 1 := by
      funext i
      simp only [a8lmdiagVec, hM1, sub_self, hχ0, Pi.one_apply]
    have hD1 : a8lmdiagSL (a8lmdiagVec χ (fun _ : Fin 4 => (1 : ZMod 7)))
        (a8lmdiagVec_prod χ hχadd hχ0 _) = 1 := by
      have h := a8lmdiagSL_congr hdiag1
        (a8lmdiagVec_prod χ hχadd hχ0 (fun _ : Fin 4 => (1 : ZMod 7))) (by simp)
      rw [h, a8lmdiagSL_one]
    have hfun1 : a8lmModelFun φ χ hχadd hχ0 xPow hdmem hxmem (fun _ => 1) = ⟨x, hxBs⟩ := by
      apply Subtype.ext
      simp only [a8lmModelFun, Subtype.coe_mk]
      rw [hM1, hD1, map_one, one_mul]
      exact a8lmxPow_one x hord
    rw [← hfun1]
    exact hmodel_fun (fun _ => 1)
  have hJmem : ∀ σ : Equiv.Perm (Fin 4), σ 0 = 0 → φ (slPerm h2 σ) ∈ J := by
    intro σ hσ0
    rcases a8lm_perm_zero_cases σ hσ0 with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← hJ]
      exact MonoidHom.mem_range.mpr ⟨1, by simp⟩
    · rw [← hJ]
      exact MonoidHom.mem_range.mpr ⟨slPerm h2 (Equiv.swap (0 : Fin 3) 1), by
        rw [MonoidHom.comp_apply, slLowerBlockHom_slPerm_swap]; rfl⟩
    · rw [← hJ]
      exact MonoidHom.mem_range.mpr ⟨slPerm h2 (Equiv.swap (1 : Fin 3) 2), by
        rw [MonoidHom.comp_apply, slLowerBlockHom_slPerm_swap]; rfl⟩
    · rw [← hJ]
      refine MonoidHom.mem_range.mpr
        ⟨slPerm h2 (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2), ?_⟩
      simp only [MonoidHom.comp_apply, map_mul, slLowerBlockHom_slPerm_swap]
      rfl
    · rw [← hJ]
      refine MonoidHom.mem_range.mpr
        ⟨slPerm h2 (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1), ?_⟩
      simp only [MonoidHom.comp_apply, map_mul, slLowerBlockHom_slPerm_swap]
      rfl
    · rw [← hJ]
      refine MonoidHom.mem_range.mpr
        ⟨slPerm h2 (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 *
          Equiv.swap (0 : Fin 3) 1), ?_⟩
      simp only [MonoidHom.comp_apply, map_mul, slLowerBlockHom_slPerm_swap]
      rfl
  refine ⟨model, hxval, ?_, ?_⟩
  · intro σ
    refine ⟨Ψ σ, ?_, hcoord σ⟩
    exact ggConjAut_mem_ggAutomizer (H := L) (Bs := Bs)
      (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (hslPerm_mem σ)
  · intro σ hσ0
    refine ⟨Ψ σ, ?_, hcoord σ⟩
    exact ggConjAut_mem_ggAutomizer (H := J) (Bs := Bs) (hJmem σ hσ0) (hslPerm_mem σ)

end CFSG.StandardType.A8Coord

end
