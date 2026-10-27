module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

set_option synthInstance.maxSize 512

namespace CFSG.StandardType

open CFSG.Assembly Matrix Module

private abbrev A11F : Type := GaloisField 2 3

private theorem a11_card_units : Nat.card A11Fˣ = 7 := by
  rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]
  norm_num

private theorem a11_units_pow_seven (u : A11Fˣ) : u ^ 7 = 1 := by
  have h := orderOf_dvd_natCard u
  rw [a11_card_units] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

private theorem a11_center_eq_bot :
    Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) A11F) = ⊥ := by
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
    have h := a11_units_pow_seven (Units.mk0 r hr0)
    have h' := congrArg (fun z : A11Fˣ => (z : A11F)) h
    simpa [Units.val_pow_eq_pow_val] using h'
  have hr1 : r = 1 := by
    have h := (pow_gcd_eq_one (a := r) (m := 4) (n := 7)).mpr ⟨hr4, hr7⟩
    simpa using h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  have hcoe : (↑a : Matrix (Fin (3 + 1)) (Fin (3 + 1)) A11F) = 1 := by
    rw [← hrA, hr1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  rw [hcoe]

private theorem a11_phi_injective {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G)
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) A11F)) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro a ha
  have hc := hker ha
  rw [a11_center_eq_bot, Subgroup.mem_bot] at hc
  exact hc

private noncomputable def a11diagSL (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1) :
    SpecialLinearGroup (Fin (3 + 1)) A11F :=
  ⟨diagonal (fun i => (u i : A11F)), by
    rw [det_diagonal]
    simpa using congrArg (fun z : A11Fˣ => (z : A11F)) h⟩

private theorem coe_a11diagSL (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1) :
    (↑(a11diagSL u h) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) A11F) =
      diagonal (fun i => (u i : A11F)) := rfl

private theorem a11diagSL_conj_comm (w : Fin 4 → A11Fˣ) (u : Fin 4 → A11Fˣ)
    (h : ∏ i, u i = 1) : ggDiagConj w (a11diagSL u h) = a11diagSL u h := by
  apply Subtype.ext
  ext i j
  rw [ggDiagConj_apply, coe_a11diagSL]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rw [Units.val_inv_eq_inv_val]
    field_simp
  · rw [Matrix.diagonal_apply_ne _ hij, mul_zero, zero_mul]

private theorem a11diagSL_pow_seven (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1) :
    (a11diagSL u h) ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_a11diagSL, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
  congr 1
  funext i
  rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, a11_units_pow_seven, Units.val_one]

private theorem a11diagSL_conj (d : Fin 4 → A11Fˣ) (hd : ∏ i, d i = 1)
    (s : SpecialLinearGroup (Fin (3 + 1)) A11F) :
    a11diagSL d hd * s * (a11diagSL d hd)⁻¹ = ggDiagConj d s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_a11diagSL,
    coe_ggDiagConj, TypeA.coe_inv_SL_of_diagonal (coe_a11diagSL d hd)]
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]

private theorem a11diagSL_inv (d : Fin 4 → A11Fˣ) (hd : ∏ i, d i = 1)
    (hd' : ∏ i, d⁻¹ i = 1) :
    (a11diagSL d hd)⁻¹ = a11diagSL d⁻¹ hd' := by
  apply Subtype.ext
  rw [TypeA.coe_inv_SL_of_diagonal (coe_a11diagSL d hd), coe_a11diagSL]
  congr 1
  funext i
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]

private theorem a11diagSL_congr {u u' : Fin 4 → A11Fˣ} (h : u = u')
    (hu : ∏ i, u i = 1) (hu' : ∏ i, u' i = 1) : a11diagSL u hu = a11diagSL u' hu' := by
  subst h; rfl

private theorem a11diagSL_conj_inv (d : Fin 4 → A11Fˣ) (hd : ∏ i, d i = 1)
    (hd' : ∏ i, d⁻¹ i = 1) (s : SpecialLinearGroup (Fin (3 + 1)) A11F) :
    (a11diagSL d hd)⁻¹ * s * a11diagSL d hd = ggDiagConj d⁻¹ s := by
  have h2 : a11diagSL d hd = (a11diagSL d⁻¹ hd')⁻¹ := by
    rw [← inv_inv (a11diagSL d hd), a11diagSL_inv d hd hd']
  rw [a11diagSL_inv d hd hd', h2]
  exact a11diagSL_conj d⁻¹ hd' s

private theorem a11_diag_mem_Bs {G : Type} [Group G] {Bs : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G}
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1) : φ (a11diagSL u h) ∈ Bs := by
  apply hSC _ _ _
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨w, hw⟩ := hdiag b hb
    calc b * φ (a11diagSL u h) = b * φ (a11diagSL u h) * b⁻¹ * b := by group
      _ = φ (ggDiagConj w (a11diagSL u h)) * b := by rw [hw]
      _ = φ (a11diagSL u h) * b := by rw [a11diagSL_conj_comm]
  · rw [← map_pow, a11diagSL_pow_seven, map_one]

private noncomputable def a11chi (g : A11Fˣ)
    (hg : ∀ x : A11Fˣ, x ∈ Subgroup.zpowers g) : ZMod 7 → A11Fˣ :=
  fun n => (zmodMulEquivOfGenerator (g := g) hg a11_card_units) (Multiplicative.ofAdd n)

private theorem a11chi_zero (g : A11Fˣ) (hg : ∀ x : A11Fˣ, x ∈ Subgroup.zpowers g) :
    a11chi g hg 0 = 1 := by
  show (zmodMulEquivOfGenerator (g := g) hg a11_card_units) (Multiplicative.ofAdd 0) = 1
  rw [show Multiplicative.ofAdd (0 : ZMod 7) = 1 from rfl, map_one]

private theorem a11chi_add (g : A11Fˣ) (hg : ∀ x : A11Fˣ, x ∈ Subgroup.zpowers g)
    (a b : ZMod 7) : a11chi g hg (a + b) = a11chi g hg a * a11chi g hg b := by
  show (zmodMulEquivOfGenerator (g := g) hg a11_card_units) (Multiplicative.ofAdd (a + b)) =
    (zmodMulEquivOfGenerator (g := g) hg a11_card_units) (Multiplicative.ofAdd a) *
      (zmodMulEquivOfGenerator (g := g) hg a11_card_units) (Multiplicative.ofAdd b)
  rw [← map_mul]
  rfl

private theorem a11chi_injective (g : A11Fˣ)
    (hg : ∀ x : A11Fˣ, x ∈ Subgroup.zpowers g) : Function.Injective (a11chi g hg) := by
  intro a b hab
  have h : Multiplicative.ofAdd a = Multiplicative.ofAdd b :=
    (zmodMulEquivOfGenerator (g := g) hg a11_card_units).injective hab
  exact Multiplicative.ofAdd.injective h

private theorem a11chi_sum {ι : Type} (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (s : Finset ι)
    (f : ι → ZMod 7) : (∏ i ∈ s, χ (f i)) = χ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hχ0]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, hχadd, ih]

private noncomputable def a11xPowSub {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    ZMod 7 → Subgroup.zpowers x := fun n =>
  (zmodMulEquivOfGenerator (g := (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x))
      (fun y => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩)
      (by rw [Nat.card_zpowers, hord])) (Multiplicative.ofAdd n)

private noncomputable def a11xPow {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    ZMod 7 → G := fun n => (a11xPowSub x hord n : G)

private theorem a11xPow_zero {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    a11xPow x hord 0 = 1 := by
  simp only [a11xPow, a11xPowSub]
  rw [show Multiplicative.ofAdd (0 : ZMod 7) = 1 from rfl, map_one]
  rfl

private theorem a11xPow_add {G : Type} [Group G] (x : G) (hord : orderOf x = 7)
    (a b : ZMod 7) : a11xPow x hord (a + b) = a11xPow x hord a * a11xPow x hord b := by
  simp only [a11xPow, a11xPowSub]
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

private theorem a11xPow_injective {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    Function.Injective (a11xPow x hord) := by
  intro a b hab
  have h : a11xPowSub x hord a = a11xPowSub x hord b := Subtype.ext hab
  have h2 := (zmodMulEquivOfGenerator (g := (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x))
      (fun y => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩)
      (by rw [Nat.card_zpowers, hord])).injective h
  exact Multiplicative.ofAdd.injective h2

private theorem a11xPow_mem {G : Type} [Group G] (x : G) (hord : orderOf x = 7)
    (m : ZMod 7) : a11xPow x hord m ∈ Subgroup.zpowers x :=
  (a11xPowSub x hord m).2

private def a11M (v : Fin 4 → ZMod 7) : ZMod 7 := 2 * ∑ i, v i

private theorem a11chi_prod_univ {ι : Type} [Fintype ι] (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (f : ι → ZMod 7) :
    (∏ i, χ (f i)) = χ (∑ i, f i) := by
  have h := a11chi_sum χ hχadd hχ0 (Finset.univ : Finset ι) f
  simpa using h

private noncomputable def a11diagVec (χ : ZMod 7 → A11Fˣ) (v : Fin 4 → ZMod 7) :
    Fin 4 → A11Fˣ := fun i => χ (v i - a11M v)

private theorem a11M_add (v w : Fin 4 → ZMod 7) : a11M (v + w) = a11M v + a11M w := by
  simp only [a11M, Pi.add_apply, Finset.sum_add_distrib]
  ring

private theorem a11diagVec_prod (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (v : Fin 4 → ZMod 7) :
    ∏ i, a11diagVec χ v i = 1 := by
  have h := a11chi_prod_univ χ hχadd hχ0 (fun i => v i - a11M v)
  simp only [a11diagVec]
  rw [h]
  have hsum : (∑ i : Fin 4, (v i - a11M v)) = 0 := by
    simp only [a11M, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    calc
      _ = (∑ i : Fin 4, v i) - (∑ i : Fin 4, v i) * ((4 : ZMod 7) * 2) := by ring
      _ = 0 := by rw [show (4 : ZMod 7) * 2 = 1 by decide, _root_.mul_one, _root_.sub_self]
  rw [hsum, hχ0]

private theorem a11diagVec_add (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (v w : Fin 4 → ZMod 7) :
    a11diagVec χ (v + w) = a11diagVec χ v * a11diagVec χ w := by
  funext i
  have harg : (v + w) i - a11M (v + w) = (v i - a11M v) + (w i - a11M w) := by
    rw [a11M_add, Pi.add_apply]; ring
  simp only [a11diagVec, harg, hχadd, Pi.mul_apply]

private theorem a11diagVec_mul_prod (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (v w : Fin 4 → ZMod 7) :
    ∏ i, (a11diagVec χ v * a11diagVec χ w) i = 1 := by
  simp only [Pi.mul_apply]
  rw [Finset.prod_mul_distrib, a11diagVec_prod χ hχadd hχ0 v,
    a11diagVec_prod χ hχadd hχ0 w, mul_one]

private theorem a11diagSL_mul (u v : Fin 4 → A11Fˣ) (hu : ∏ i, u i = 1)
    (hv : ∏ i, v i = 1) (huv : ∏ i, (u * v) i = 1) :
    a11diagSL (u * v) huv = a11diagSL u hu * a11diagSL v hv := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_a11diagSL, coe_a11diagSL, coe_a11diagSL,
    Matrix.diagonal_mul_diagonal]
  rfl

private noncomputable def a11ModelFun {G : Type} [Group G] {Bs : Subgroup G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G)
    (χ : ZMod 7 → A11Fˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1), φ (a11diagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs) (v : Fin 4 → ZMod 7) : ↥Bs :=
  ⟨φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) * xPow (a11M v),
    Bs.mul_mem (hdmem _ _) (hxmem _)⟩

private theorem a11ModelFun_add {G : Type} [Group G] {Bs : Subgroup G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G)
    (χ : ZMod 7 → A11Fˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1), φ (a11diagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs)
    (hxadd : ∀ a b, xPow (a + b) = xPow a * xPow b)
    (hxcomm : ∀ (m : ZMod 7) (s : SpecialLinearGroup (Fin (3 + 1)) A11F),
      xPow m * φ s = φ s * xPow m)
    (v w : Fin 4 → ZMod 7) :
    a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v + w) =
      a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v *
        a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem w := by
  apply Subtype.ext
  simp only [a11ModelFun, Subgroup.coe_mul]
  have hdiag : a11diagSL (a11diagVec χ (v + w)) (a11diagVec_prod χ hχadd hχ0 (v + w)) =
      a11diagSL (a11diagVec χ v * a11diagVec χ w)
        (a11diagVec_mul_prod χ hχadd hχ0 v w) := by
    apply Subtype.ext
    rw [coe_a11diagSL, coe_a11diagSL]
    exact congrArg (fun u : Fin 4 → A11Fˣ => diagonal (fun i => (u i : A11F)))
      (a11diagVec_add χ hχadd v w)
  have hmul : a11diagSL (a11diagVec χ v * a11diagVec χ w)
        (a11diagVec_mul_prod χ hχadd hχ0 v w) =
      a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) *
        a11diagSL (a11diagVec χ w) (a11diagVec_prod χ hχadd hχ0 w) :=
    a11diagSL_mul _ _ _ _ _
  rw [hdiag, hmul, map_mul, a11M_add, hxadd]
  set A := φ (a11diagSL (a11diagVec χ v) _) with hA
  set B := φ (a11diagSL (a11diagVec χ w) _) with hB
  set X := xPow (a11M v) with hX
  set Y := xPow (a11M w) with hY
  change A * B * (X * Y) = A * X * (B * Y)
  rw [mul_assoc, ← mul_assoc B X Y, ← hxcomm (a11M v) (a11diagSL (a11diagVec χ w) _)]
  rw [← hX, ← hB]
  group

private theorem a11chi_nsmul (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (n : ℕ) (a : ZMod 7) :
    (χ a) ^ n = χ (n • a) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, hχ0]
  | succ n ih => rw [pow_succ, ih, ← hχadd, succ_nsmul]

private theorem a11chi_neg (χ : ZMod 7 → A11Fˣ)
    (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1) (c : ZMod 7) :
    χ (-c) = (χ c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hχadd, _root_.neg_add_cancel, hχ0]

private theorem a11ggDiagConj_const_mul (t : A11Fˣ) (h : Fin 4 → A11Fˣ) :
    ggDiagConj ((fun _ : Fin 4 => t) * h) = ggDiagConj h := by
  apply MonoidHom.ext
  intro s
  rw [← ggDiagConj_ggDiagConj, ggDiagConj_eq_self_of_const (fun _ _ => rfl)]

private theorem a11chi_surjective (g : A11Fˣ)
    (hg : ∀ x : A11Fˣ, x ∈ Subgroup.zpowers g) : Function.Surjective (a11chi g hg) := by
  intro y
  obtain ⟨m, hm⟩ := (zmodMulEquivOfGenerator (g := g) hg a11_card_units).surjective y
  obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective m
  exact ⟨n, hm⟩

private theorem a11xPow_surjective {G : Type} [Group G] (x : G) (hord : orderOf x = 7) :
    ∀ c ∈ Subgroup.zpowers x, ∃ m, a11xPow x hord m = c := by
  intro c hc
  have hsurj : Function.Surjective (a11xPowSub x hord) := by
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

private theorem a11diagSL_one :
    a11diagSL (1 : Fin 4 → A11Fˣ) (by simp) = 1 := by
  apply Subtype.ext
  rw [coe_a11diagSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.diagonal_apply_eq, Matrix.one_apply]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

private theorem a11ModelFun_zero {G : Type} [Group G] {Bs : Subgroup G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G)
    (χ : ZMod 7 → A11Fˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (xPow : ZMod 7 → G)
    (hdmem : ∀ (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1), φ (a11diagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs) (hx0 : xPow 0 = 1) :
    a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem 0 = 1 := by
  apply Subtype.ext
  simp only [a11ModelFun, Subtype.coe_mk, Subgroup.coe_one]
  have hM0 : a11M (0 : Fin 4 → ZMod 7) = 0 := by simp [a11M]
  have hu0 : a11diagVec χ (0 : Fin 4 → ZMod 7) = 1 := by
    funext i
    simp [a11diagVec, hM0, hχ0]
  rw [hM0, hx0]
  have hd1 : a11diagSL (a11diagVec χ (0 : Fin 4 → ZMod 7))
      (a11diagVec_prod χ hχadd hχ0 0) = 1 := by
    have hh : a11diagSL (a11diagVec χ (0 : Fin 4 → ZMod 7))
        (a11diagVec_prod χ hχadd hχ0 0) = a11diagSL (1 : Fin 4 → A11Fˣ) (by simp) :=
      a11diagSL_congr hu0 _ _
    rw [hh, a11diagSL_one]
  rw [hd1, map_one, one_mul]

private theorem a11ModelFun_surjective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G) (hrange : φ.range = L)
    (χ : ZMod 7 → A11Fˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (hχsurj : Function.Surjective χ) (hχinj : Function.Injective χ)
    (xPow : ZMod 7 → G) (hxadd : ∀ a b, xPow (a + b) = xPow a * xPow b)
    (hxsurj : ∀ c ∈ Subgroup.zpowers x, ∃ m, xPow m = c)
    (hdmem : ∀ (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1), φ (a11diagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs)
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hz : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZL : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (b : ↥Bs) : ∃ v : Fin 4 → ZMod 7, a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v = b := by
  obtain ⟨h, hh⟩ := hdiag b b.2
  set p : A11Fˣ := ∏ i, h i with hp
  obtain ⟨c, hc⟩ := hχsurj p
  set lam : A11Fˣ := χ (-(2 * c)) with hlam
  have hlam_pow : lam ^ 4 = p⁻¹ := by
    rw [hlam, a11chi_nsmul χ hχadd hχ0 4 (-(2 * c))]
    have h4 : (4 : ℕ) • (-(2 * c) : ZMod 7) = -c := by
      calc
        _ = -c * ((4 : ZMod 7) * 2) := by rw [_root_.nsmul_eq_mul]; ring
        _ = -c := by rw [show (4 : ZMod 7) * 2 = 1 by decide, _root_.mul_one]
    rw [h4, a11chi_neg χ hχadd hχ0 c, hc]
  set d : Fin 4 → A11Fˣ := (fun _ => lam) * h with hd
  have hdprod : ∏ i, d i = 1 := by
    simp only [hd, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← hp, hlam_pow, inv_mul_cancel]
  have hd' : ∏ i, d⁻¹ i = 1 := by
    simp only [Pi.inv_apply, Finset.prod_inv_distrib, hdprod, inv_one]
  set D : SpecialLinearGroup (Fin (3 + 1)) A11F := a11diagSL d hdprod with hD
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
        _ = φ ((a11diagSL d hdprod)⁻¹ * ggDiagConj h t * a11diagSL d hdprod) := by
              rw [hD, ← map_inv, ← map_mul, ← map_mul]
        _ = φ (ggDiagConj d⁻¹ (ggDiagConj h t)) := by
              rw [a11diagSL_conj_inv d hdprod hd' (ggDiagConj h t)]
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
      rw [← a11chi_prod_univ χ hχadd hχ0 a, hprod, hχ0]
    exact hχinj h1
  let v : Fin 4 → ZMod 7 := fun i => a i + m
  have hMv : a11M v = m := by
    simp only [a11M, v, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsum, mul_zero, zero_add]
    ring_nf
    rw [show (8 : ZMod 7) = 1 by decide, mul_one]
  have hdv : a11diagVec χ v = d := by
    funext i
    simp only [a11diagVec, v]
    rw [show a i + m - a11M v = a i by rw [hMv]; ring]
    exact ha i
  have hdiag_eq : a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) = D := by
    rw [hD]
    apply Subtype.ext
    rw [coe_a11diagSL, coe_a11diagSL]
    congr 1
    funext i
    rw [hdv]
  refine ⟨v, ?_⟩
  apply Subtype.ext
  simp only [a11ModelFun, Subtype.coe_mk]
  rw [hdiag_eq, hMv, hm, hc0]
  group

private theorem a11ModelFun_injective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (φ : SpecialLinearGroup (Fin (3 + 1)) A11F →* G) (hφinj : Function.Injective φ)
    (hrange : φ.range = L)
    (χ : ZMod 7 → A11Fˣ) (hχadd : ∀ a b, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (hχinj : Function.Injective χ)
    (xPow : ZMod 7 → G) (hxadd : ∀ a b, xPow (a + b) = xPow a * xPow b)
    (hdmem : ∀ (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1), φ (a11diagSL u h) ∈ Bs)
    (hxmem : ∀ m, xPow m ∈ Bs)
    (hxzer : ∀ m, xPow m = 1 → m = 0)
    (hxmz : ∀ m, xPow m ∈ Subgroup.zpowers x)
    (hLdisj : Subgroup.zpowers x ⊓ L = ⊥) {v : Fin 4 → ZMod 7}
    (hv : a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v = 1) : v = 0 := by
  have hcoe : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
      xPow (a11M v) = 1 := by
    simpa only [a11ModelFun, Subtype.coe_mk, Subgroup.coe_one] using
      congrArg (fun b : ↥Bs => (b : G)) hv
  have hAeq : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) =
      (xPow (a11M v))⁻¹ := (eq_inv_iff_mul_eq_one).mpr hcoe
  have hAL : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) ∈ L := by
    rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hAz : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) ∈
      Subgroup.zpowers x := by
    rw [hAeq]; exact Subgroup.inv_mem _ (hxmz _)
  have hA1 : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) = 1 := by
    have hmem := Subgroup.mem_inf.mpr ⟨hAz, hAL⟩
    rw [hLdisj, Subgroup.mem_bot] at hmem
    exact hmem
  have hX1 : xPow (a11M v) = 1 := by
    rw [hA1, one_mul] at hcoe
    exact hcoe
  have hm0 : a11M v = 0 := hxzer _ hX1
  have hdiag1 : a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) = 1 := by
    apply hφinj
    rw [hA1, map_one]
  have hu1 : a11diagVec χ v = 1 := by
    have hm : (fun i => (a11diagVec χ v i : A11F)) = (fun _ => (1 : A11F)) := by
      have h2 : (↑(a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) A11F) = 1 := by
        rw [congrArg Subtype.val hdiag1, Matrix.SpecialLinearGroup.coe_one]
      rw [coe_a11diagSL] at h2
      funext i
      have := congrFun (congrFun h2 i) i
      simpa [Matrix.one_apply] using this
    funext i
    apply Units.ext
    have := congrFun hm i
    simpa using this
  funext i
  have hχ1 : χ (v i - a11M v) = 1 := by
    simpa [a11diagVec] using congrFun hu1 i
  have hz : v i - a11M v = 0 := hχinj (by rw [hχ1, hχ0])
  rw [hm0] at hz
  simpa using hz

private theorem a11chi_ne_inv {χ : ZMod 7 → A11Fˣ}
    (hχadd : ∀ a b : ZMod 7, χ (a + b) = χ a * χ b) (hχ0 : χ 0 = 1)
    (hχinj : Function.Injective χ) : (χ 1 : A11F) ≠ (χ 1 : A11F)⁻¹ := by
  intro h
  have hχneg : χ (-1) = (χ 1)⁻¹ := by
    have hsum : (-1 : ZMod 7) + 1 = (0 : ZMod 7) := neg_add_cancel 1
    exact eq_inv_of_mul_eq_one_left (by rw [← hχadd, hsum, hχ0])
  have h1 : χ 1 = χ (-1) := by
    apply Units.ext
    rw [h, ← Units.val_inv_eq_inv_val, hχneg]
  have hthis : (1 : ZMod 7) = (-1 : ZMod 7) := hχinj h1
  exact (by decide : ¬ ((1 : ZMod 7) = (-1 : ZMod 7))) hthis

theorem ggExcReflTBData_of_slFourLift [Fact (Nat.Prime 7)] {G : Type} [Group G] [Finite G]
    {Bs L J : Subgroup G} {x : G} (hBs : IsElemAbelian 7 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    (hz : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) (hx : x ≠ 1)
    (φ : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G) (hrange : φ.range = L)
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3)))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hJ : (φ.comp (slLowerBlockHom 3 (GaloisField 2 3))).range = J) :
    Nonempty (GGExcReflTBData 7 Bs L J) := by
  haveI : IsCyclic A11Fˣ := instIsCyclicUnitsOfFinite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A11Fˣ)
  let χ : ZMod 7 → A11Fˣ := a11chi g hg
  have hχadd : ∀ a b, χ (a + b) = χ a * χ b := a11chi_add g hg
  have hχ0 : χ 0 = 1 := a11chi_zero g hg
  have hχinj : Function.Injective χ := a11chi_injective g hg
  have hχsurj : Function.Surjective χ := a11chi_surjective g hg
  have hφinj : Function.Injective φ := a11_phi_injective φ hker
  have hxInf : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hz]; exact Subgroup.mem_zpowers x
  have hxBs : x ∈ Bs := (Subgroup.mem_inf.mp hxInf).1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hxInf).2
  have hord : orderOf x = 7 := (orderOf_eq_prime_iff).mpr ⟨hBs.2 x hxBs, hx⟩
  let xPow : ZMod 7 → G := a11xPow x hord
  have hxadd : ∀ a b, xPow (a + b) = xPow a * xPow b := a11xPow_add x hord
  have hxzer : ∀ m, xPow m = 1 → m = 0 := by
    intro m hm
    exact a11xPow_injective x hord (by
      rw [show a11xPow x hord m = 1 from hm, a11xPow_zero x hord])
  have hxmz : ∀ m, xPow m ∈ Subgroup.zpowers x := a11xPow_mem x hord
  have hxsurj : ∀ c ∈ Subgroup.zpowers x, ∃ m, xPow m = c := a11xPow_surjective x hord
  have hx0 : xPow 0 = 1 := a11xPow_zero x hord
  have hxmem : ∀ m, xPow m ∈ Bs := fun m => Subgroup.zpowers_le.mpr hxBs (hxmz m)
  have hxL : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hxC
  have hxcomm : ∀ (m : ZMod 7) (s : SpecialLinearGroup (Fin (3 + 1)) A11F),
      xPow m * φ s = φ s * xPow m := by
    intro m s
    exact (Subgroup.mem_centralizer_iff.mp (hxL (hxmz m)) (φ s)
      (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨s, rfl⟩)).symm
  have hdmem : ∀ (u : Fin 4 → A11Fˣ) (h : ∏ i, u i = 1), φ (a11diagSL u h) ∈ Bs :=
    fun u h => a11_diag_mem_Bs hSC hdiag u h
  have hZL : L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [← hrange] at hyL
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hyL
    have hsZ : s ∈ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) A11F) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply hφinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hyC (φ t)
        (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨t, rfl⟩)
    rw [a11_center_eq_bot, Subgroup.mem_bot] at hsZ
    rw [hsZ, map_one]
  have hLdisj : Subgroup.zpowers x ⊓ L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyx, hyL⟩ := Subgroup.mem_inf.mp hy
    have hmem := Subgroup.mem_inf.mpr ⟨hyL, hxL hyx⟩
    rwa [hZL, Subgroup.mem_bot] at hmem
  let Ffun : (Fin 4 → ZMod 7) → Additive ↥Bs := fun v =>
    Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v)
  have Fzero : Ffun 0 = 0 := by
    change Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem 0) = 0
    rw [a11ModelFun_zero φ χ hχadd hχ0 xPow hdmem hxmem hx0]
    rfl
  have Fadd : ∀ v w, Ffun (v + w) = Ffun v + Ffun w := by
    intro v w
    change Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v + w)) =
      Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) +
        Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem w)
    rw [a11ModelFun_add φ χ hχadd hχ0 xPow hdmem hxmem hxadd hxcomm v w]
    rfl
  let Fhom : (Fin 4 → ZMod 7) →+ Additive ↥Bs :=
    { toFun := Ffun, map_zero' := Fzero, map_add' := Fadd }
  have hFinj : Function.Injective Fhom := by
    intro v w hvw
    have h1 : a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v =
        a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem w := Additive.ofMul.injective hvw
    have hneg : a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (-w) =
        (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem w)⁻¹ := by
      have h := a11ModelFun_add φ χ hχadd hχ0 xPow hdmem hxmem hxadd hxcomm (-w) w
      have h0 : -w + w = (0 : Fin 4 → ZMod 7) := by funext i; exact neg_add_cancel (w i)
      rw [h0, a11ModelFun_zero φ χ hχadd hχ0 xPow hdmem hxmem hx0] at h
      exact (eq_inv_iff_mul_eq_one).mpr h.symm
    have hzero : a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v - w) = 1 := by
      have h := a11ModelFun_add φ χ hχadd hχ0 xPow hdmem hxmem hxadd hxcomm v (-w)
      rw [hneg, h1, mul_inv_cancel] at h
      rw [sub_eq_add_neg]
      exact h
    exact sub_eq_zero.mp (a11ModelFun_injective φ hφinj hrange χ hχadd hχ0 hχinj xPow hxadd
      hdmem hxmem hxzer hxmz hLdisj hzero)
  have hFsurj : Function.Surjective Fhom := by
    intro y
    obtain ⟨v, hv⟩ := a11ModelFun_surjective φ hrange χ hχadd hχ0 hχsurj hχinj xPow hxadd
      hxsurj hdmem hxmem hdiag hz hZL (Additive.toMul y)
    refine ⟨v, ?_⟩
    change Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) = y
    rw [hv]
    rfl
  let model : Additive ↥Bs ≃+ (Fin 4 → ZMod 7) :=
    (AddEquiv.ofBijective Fhom ⟨hFinj, hFsurj⟩).symm
  have h2 : (2 : A11F) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 3 (by norm_num)) (by norm_num)
  have hnorm : ∀ i : Fin 3, φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) ∈
      Subgroup.normalizer (Bs : Set G) := fun i =>
    slPerm_mem_normalizer_of_actsDiag h2 hBs.2 hSC hker hdiag _
  let simple : Fin 3 → MulAut ↥Bs := fun i => ggConjAut Bs (hnorm i)
  have hslPerm_eq : ∀ i : Fin 3, slPerm h2 (Equiv.swap i.castSucc i.succ) =
      TypeA.permSL (Equiv.swap i.castSucc i.succ) := by
    intro i
    apply Subtype.ext
    rw [coe_slPerm, TypeA.coe_permSL, signedPerm_one_eq_permMatrix]
    rw [show (Equiv.swap i.castSucc i.succ)⁻¹ = Equiv.swap i.castSucc i.succ from
      inv_eq_of_mul_eq_one_right (Equiv.swap_mul_self i.castSucc i.succ)]
  have hslPerm_swap_diag : ∀ (i : Fin 3) (u : Fin 4 → A11Fˣ)
      (hu : ∏ k, u k = 1) (hu' : ∏ k, (u ∘ Equiv.swap i.castSucc i.succ) k = 1),
      slPerm h2 (Equiv.swap i.castSucc i.succ) * a11diagSL u hu *
        (slPerm h2 (Equiv.swap i.castSucc i.succ))⁻¹ =
        a11diagSL (u ∘ Equiv.swap i.castSucc i.succ) hu' := by
    intro i u hu hu'
    apply Subtype.ext
    rw [hslPerm_eq i]
    rw [TypeA.coe_permSL_conj (D := a11diagSL u hu) (t := fun k => (u k : A11F))
      (coe_a11diagSL u hu) (Equiv.swap i.castSucc i.succ)]
    rw [coe_a11diagSL]
    rfl
  have hMcomp : ∀ (i : Fin 3) (v : Fin 4 → ZMod 7),
      a11M (v ∘ Equiv.swap i.castSucc i.succ) = a11M v := by
    intro i v
    simp only [a11M, Function.comp_apply]
    congr 1
    exact Equiv.sum_comp (Equiv.swap i.castSucc i.succ) v
  have hsimple_model : ∀ (i : Fin 3) (v : Fin 4 → ZMod 7),
      simple i (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) =
        a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ Equiv.swap i.castSucc i.succ) := by
    intro i v
    have hM := hMcomp i v
    have hveq : a11diagVec χ v ∘ Equiv.swap i.castSucc i.succ =
        a11diagVec χ (v ∘ Equiv.swap i.castSucc i.succ) := by
      funext k
      simp only [Function.comp_apply, a11diagVec]
      rw [hM]
    have hsl := hslPerm_swap_diag i (a11diagVec χ v)
      (a11diagVec_prod χ hχadd hχ0 v)
      (by rw [hveq]; exact a11diagVec_prod χ hχadd hχ0 (v ∘ Equiv.swap i.castSucc i.succ))
    have hsl' : φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
        φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
        (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹ =
        φ (a11diagSL (a11diagVec χ (v ∘ Equiv.swap i.castSucc i.succ))
          (a11diagVec_prod χ hχadd hχ0 (v ∘ Equiv.swap i.castSucc i.succ))) := by
      rw [← map_mul, ← map_inv, ← map_mul]
      exact congrArg φ (hsl.trans (a11diagSL_congr hveq _ _))
    apply Subtype.ext
    simp only [simple, ggConjAut_apply, a11ModelFun, Subtype.coe_mk]
    rw [hM]
    have hc : Commute (xPow (a11M v)) (φ (slPerm h2 (Equiv.swap i.castSucc i.succ))) :=
      hxcomm (a11M v) (slPerm h2 (Equiv.swap i.castSucc i.succ))
    have hxinv : xPow (a11M v) * (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹ =
        (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹ * xPow (a11M v) :=
      (hc.inv_right).eq
    calc φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
          (φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
            xPow (a11M v)) * (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹
        = (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
            φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
            (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹) * xPow (a11M v) := by
          calc φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
                (φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  xPow (a11M v)) * (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹
              = (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
                  φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v))) *
                  (xPow (a11M v) * (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹) := by
                group
            _ = (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
                  φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v))) *
                  ((φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹ * xPow (a11M v)) := by
                rw [hxinv]
            _ = (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)) *
                  φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  (φ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹) * xPow (a11M v) := by
                group
      _ = φ (a11diagSL (a11diagVec χ (v ∘ Equiv.swap i.castSucc i.succ))
            (a11diagVec_prod χ hχadd hχ0 (v ∘ Equiv.swap i.castSucc i.succ))) *
            xPow (a11M v) := by rw [hsl']
  have hmodel_fun : ∀ v : Fin 4 → ZMod 7,
      model (Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v)) = v := by
    intro v
    change (AddEquiv.ofBijective Fhom ⟨hFinj, hFsurj⟩).symm (Fhom v) = v
    exact AddEquiv.symm_apply_apply (AddEquiv.ofBijective Fhom ⟨hFinj, hFsurj⟩) v
  have ha11inj : Function.Injective
      (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem) := by
    intro v w h
    apply hFinj
    change Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) =
      Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem w)
    rw [h]
  have hweyl : GGIsWeylMatrix (CoxeterMatrix.A 3) := by
    refine Or.inl ⟨3, Equiv.refl _, by norm_num, Or.inl ?_⟩
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl
  let coroot : Fin 3 → (Fin 4 → ZMod 7) := fun i =>
    Pi.single i.castSucc 1 - Pi.single i.succ 1
  let root : Fin 3 → Module.Dual (ZMod 7) (Fin 4 → ZMod 7) := fun i =>
    { toFun := fun w => w i.castSucc - w i.succ
      map_add' := fun a b => by simp [Pi.add_apply]; ring
      map_smul' := fun c a => by
        change c • a i.castSucc - c • a i.succ = c * (a i.castSucc - a i.succ)
        rw [smul_eq_mul, smul_eq_mul, mul_sub] }
  have hroot_apply : ∀ (i : Fin 3) (w : Fin 4 → ZMod 7),
      root i w = w i.castSucc - w i.succ := by
    intro i w
    rfl
  have hcoord : ∀ (i : Fin 3) (v : Fin 4 → ZMod 7),
      v ∘ Equiv.swap i.castSucc i.succ = v - root i v • coroot i := by
    intro i v
    funext k
    fin_cases i <;> fin_cases k <;>
      simp [hroot_apply, coroot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne] <;> ring_nf
  have hJ1 : φ (slPerm h2 (Equiv.swap 1 2)) ∈ J := by
    rw [← hJ]
    exact MonoidHom.mem_range.mpr ⟨slPerm h2 (Equiv.swap 0 1), by
      rw [MonoidHom.comp_apply, slLowerBlockHom_slPerm_swap]
      rfl⟩
  have hJ2 : φ (slPerm h2 (Equiv.swap 2 3)) ∈ J := by
    rw [← hJ]
    exact MonoidHom.mem_range.mpr ⟨slPerm h2 (Equiv.swap 1 2), by
      rw [MonoidHom.comp_apply, slLowerBlockHom_slPerm_swap]
      rfl⟩
  let Sdiag : Subgroup G := Subgroup.closure
    (Set.range fun u : {u : Fin 4 → A11Fˣ // ∏ i, u i = 1} => φ (a11diagSL u.1 u.2))
  have hSdiag_range : ∀ x ∈ Sdiag, ∃ u : {u : Fin 4 → A11Fˣ // ∏ i, u i = 1},
      x = φ (a11diagSL u.1 u.2) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => obtain ⟨u, rfl⟩ := hy; exact ⟨u, rfl⟩
    | one => exact ⟨⟨1, by simp⟩, by rw [a11diagSL_one, map_one]⟩
    | mul a b ha hb iha ihb =>
        obtain ⟨u, rfl⟩ := iha
        obtain ⟨v, rfl⟩ := ihb
        exact ⟨⟨u.1 * v.1, by
          change ∏ i, u.1 i * v.1 i = 1
          rw [Finset.prod_mul_distrib, u.2, v.2, mul_one]⟩,
          by rw [← map_mul, a11diagSL_mul]⟩
    | inv a ha iha =>
        obtain ⟨u, rfl⟩ := iha
        exact ⟨⟨u.1⁻¹, by simp only [Pi.inv_apply, Finset.prod_inv_distrib, u.2, inv_one]⟩,
          by rw [← map_inv, a11diagSL_inv]⟩
  have hSdiag_le : Sdiag ≤ Bs ⊓ L := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨hdmem u.1 u.2, by
      rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  have hBs_le_Sdiag : Bs ⊓ L ≤ Sdiag := by
    intro b hb
    obtain ⟨hbB, hbL⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨v, hv⟩ := a11ModelFun_surjective φ hrange χ hχadd hχ0 hχsurj hχinj xPow hxadd
      hxsurj hdmem hxmem hdiag hz hZL ⟨b, hbB⟩
    have hvG : (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v : G) = b :=
      congrArg Subtype.val hv
    have hD : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) ∈ L := by
      rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hxL : xPow (a11M v) ∈ L := by
      have hbL' : φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
          xPow (a11M v) ∈ L := by
        have h := hbL
        rw [← hvG] at h
        simpa only [a11ModelFun, Subtype.coe_mk] using h
      simpa using L.mul_mem (L.inv_mem hD) hbL'
    have hxbot : xPow (a11M v) = 1 := by
      have hmem : xPow (a11M v) ∈ Subgroup.zpowers x ⊓ L :=
        Subgroup.mem_inf.mpr ⟨hxmz _, hxL⟩
      rwa [hLdisj, Subgroup.mem_bot] at hmem
    rw [← hvG]
    change (φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
      xPow (a11M v) : G) ∈ Sdiag
    rw [hxbot, mul_one]
    exact Subgroup.subset_closure ⟨⟨a11diagVec χ v, a11diagVec_prod χ hχadd hχ0 v⟩, rfl⟩
  have hBsL : Bs ⊓ L = Sdiag := le_antisymm hBs_le_Sdiag hSdiag_le
  refine ⟨GGExcReflTBData.mk (Λ := Fin 3) (coxeter := CoxeterMatrix.A 3)
    (cartan := CartanMatrix.A 3) (V := Fin 4 → ZMod 7)
    (instModule := Pi.Function.module (Fin 4) (ZMod 7) (ZMod 7))
    (model := model) (simple := simple)
    (coroot := coroot) (root := root) (isWeyl := hweyl) (isCartan := ggIntCartan_A 3)
    (three_le_card := by decide) (pairing := ?_) (simple_apply := ?_) (automizer_eq := ?_)
    (tbHyp := ?_) (noncomm := ?_)⟩
  · intro i j
    show (Pi.single j.castSucc 1 - Pi.single j.succ 1 : Fin 4 → ZMod 7) i.castSucc -
      (Pi.single j.castSucc 1 - Pi.single j.succ 1 : Fin 4 → ZMod 7) i.succ =
      (CartanMatrix.A 3 i j : ZMod 7)
    fin_cases i <;> fin_cases j <;>
      norm_num [CartanMatrix.A, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne]
  · intro i w
    obtain ⟨b, rfl⟩ := model.surjective w
    rw [@ggLin_apply 7 _ ↥Bs _ (Fin 4 → ZMod 7) _
        (Pi.Function.module (Fin 4) (ZMod 7) (ZMod 7)) model (simple i) (model b)]
    erw [AddEquiv.symm_apply_apply model b]
    obtain ⟨v, hv⟩ := a11ModelFun_surjective φ hrange χ hχadd hχ0 hχsurj hχinj xPow hxadd
      hxsurj hdmem hxmem hdiag hz hZL (Additive.toMul b)
    have hb : b = Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) := by
      rw [hv]; rfl
    rw [hb]
    change model (Additive.ofMul (simple i
        (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v))) =
      model (Additive.ofMul (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v)) -
        root i (model (Additive.ofMul
          (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v))) • coroot i
    rw [hsimple_model i v, hmodel_fun, hcoord i v, hmodel_fun]
  ·
    have hslPerm_eq' : ∀ π : Equiv.Perm (Fin 4), slPerm h2 π = TypeA.permSL π.symm := by
      intro π
      apply Subtype.ext
      rw [coe_slPerm, TypeA.coe_permSL, signedPerm_one_eq_permMatrix]
      rfl
    have hslPerm_diag : ∀ (π : Equiv.Perm (Fin 4)) (u : Fin 4 → A11Fˣ)
        (hu : ∏ k, u k = 1) (hu' : ∏ k, (u ∘ ⇑π) k = 1),
        slPerm h2 π.symm * a11diagSL u hu * (slPerm h2 π.symm)⁻¹ = a11diagSL (u ∘ ⇑π) hu' := by
      intro π u hu hu'
      apply Subtype.ext
      rw [hslPerm_eq' π.symm, Equiv.symm_symm]
      rw [TypeA.coe_permSL_conj (D := a11diagSL u hu) (t := fun k => (u k : A11F))
        (coe_a11diagSL u hu) π]
      rw [coe_a11diagSL]
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
    have hsimple_eq : ∀ i : Fin 3, simple i = Ψ (Equiv.swap i.castSucc i.succ) := fun i => rfl
    have hcl : Subgroup.closure (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) = ⊤ := by
      apply top_le_iff.mp
      intro x _
      have hx : x ∈ Submonoid.closure
          (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ 3]; exact Submonoid.mem_top x
      exact (Submonoid.closure_le.mpr (fun y hy => Subgroup.subset_closure hy)) hx
    have hrange_Ψ : Ψ.range = Subgroup.closure (Set.range simple) := by
      apply le_antisymm
      · rintro _ ⟨π, rfl⟩
        have hπ : π ∈ Subgroup.closure
            (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) := by
          rw [hcl]; trivial
        induction hπ using Subgroup.closure_induction with
        | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact Subgroup.subset_closure ⟨i, (hsimple_eq i).symm⟩
        | one => rw [map_one]; exact Subgroup.one_mem _
        | mul a b ha hb iha ihb => rw [map_mul]; exact Subgroup.mul_mem _ iha ihb
        | inv a ha iha => rw [map_inv]; exact Subgroup.inv_mem _ iha
      · rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨Equiv.swap i.castSucc i.succ, (hsimple_eq i).symm⟩
    have hζ : (χ 1 : A11F) ≠ (χ 1 : A11F)⁻¹ := a11chi_ne_inv hχadd hχ0 hχinj
    apply le_antisymm
    · rintro ψ hψ
      rw [← hrange_Ψ]
      obtain ⟨g, hgL, hgN, hgact⟩ := mem_ggAutomizer_iff.mp hψ
      obtain ⟨M, hMφ⟩ := MonoidHom.mem_range.mp (hrange ▸ hgL)
      have hMdiag : ∀ (u : Fin 4 → A11Fˣ) (hu : ∏ i, u i = 1),
          ∃ (u' : Fin 4 → A11Fˣ) (hu' : ∏ i, u' i = 1),
          M * a11diagSL u hu * M⁻¹ = a11diagSL u' hu' := by
        intro u hu
        have hDmem : φ (a11diagSL u hu) ∈ L := by
          rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
        have hconjB : g * φ (a11diagSL u hu) * g⁻¹ ∈ Bs :=
          (Subgroup.mem_normalizer_iff.mp hgN _).mp (hdmem u hu)
        have hconjL : g * φ (a11diagSL u hu) * g⁻¹ ∈ L :=
          L.mul_mem (L.mul_mem hgL hDmem) (L.inv_mem hgL)
        have hmem : g * φ (a11diagSL u hu) * g⁻¹ ∈ Sdiag := by
          rw [← hBsL]; exact Subgroup.mem_inf.mpr ⟨hconjB, hconjL⟩
        obtain ⟨u', hu_eq⟩ := hSdiag_range _ hmem
        refine ⟨u'.1, u'.2, hφinj ?_⟩
        rw [map_mul, map_mul, map_inv, hMφ]
        exact hu_eq
      have hA : ∀ i j : Fin 4, i ≠ j → ∃ D : Fin 4 → A11F,
          (M : Matrix (Fin 4) (Fin 4) A11F) * diagonal (TypeA.rootT (χ 1 : A11F) i j) =
            diagonal D * (M : Matrix (Fin 4) (Fin 4) A11F) := by
        intro i j hij
        let u : Fin 4 → A11Fˣ := fun k => Units.mk0 (TypeA.rootT (χ 1 : A11F) i j k) (by
          by_cases hki : k = i
          · rw [hki, TypeA.rootT_left]; exact Units.ne_zero (χ 1)
          · by_cases hkj : k = j
            · rw [hkj, TypeA.rootT_right (χ 1 : A11F) hij]
              exact inv_ne_zero (Units.ne_zero (χ 1))
            · rw [TypeA.rootT_other (ζ := (χ 1 : A11F)) (i := i) (j := j) hki hkj]
              exact one_ne_zero)
        have hu : ∏ k, u k = 1 := by
          apply Units.ext
          rw [Units.val_one]
          rw [show (↑(∏ k, u k) : A11F) = ∏ k, (↑(u k) : A11F) from
            map_prod (Units.coeHom A11F) u Finset.univ]
          rw [show (∏ k, (↑(u k) : A11F)) = ∏ k, TypeA.rootT (χ 1 : A11F) i j k from by
            apply Finset.prod_congr rfl; intro k _; rfl]
          exact TypeA.prod_rootT (Units.ne_zero (χ 1)) hij
        obtain ⟨u', hu', hconj⟩ := hMdiag u hu
        have hm : M * a11diagSL u hu = a11diagSL u' hu' * M := by
          have h := congrArg (fun x : SpecialLinearGroup (Fin 4) A11F => x * M) hconj
          simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
        have huf : (fun k => (u k : A11F)) = TypeA.rootT (χ 1 : A11F) i j := by
          funext k; rfl
        refine ⟨fun k => (u' k : A11F), ?_⟩
        have hm' := congrArg (fun s : SpecialLinearGroup (Fin 4) A11F =>
          (s : Matrix (Fin 4) (Fin 4) A11F)) hm
        simp only [Matrix.SpecialLinearGroup.coe_mul, coe_a11diagSL] at hm'
        rw [huf] at hm'
        exact hm'
      obtain ⟨π, hπ⟩ := TypeA.exists_perm_mul_diagonal hζ (M : GL (Fin 4) A11F) hA
      have hMπ : ∀ v : Fin 4 → ZMod 7, a11M (v ∘ π) = a11M v := by
        intro v
        simp only [a11M, Function.comp_apply]
        congr 1
        exact Equiv.sum_comp π v
      have hMD : ∀ v : Fin 4 → ZMod 7,
          M * a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) * M⁻¹ =
          a11diagSL (a11diagVec χ (v ∘ π)) (a11diagVec_prod χ hχadd hχ0 (v ∘ π)) := by
        intro v
        obtain ⟨u'', hu'', hconj''⟩ :=
          hMdiag (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)
        have hm'' : M * a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) =
            a11diagSL u'' hu'' * M := by
          have h := congrArg (fun x : SpecialLinearGroup (Fin 4) A11F => x * M) hconj''
          simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
        have hfun : (fun k => (a11diagVec χ v k : A11F)) ∘ π =
            (fun k => (a11diagVec χ (v ∘ π) k : A11F)) := by
          funext k
          simp only [Function.comp_apply, a11diagVec]
          rw [hMπ v]
        have hmπ : (M : Matrix (Fin 4) (Fin 4) A11F) *
            diagonal (fun k => (a11diagVec χ v k : A11F)) =
            diagonal (fun k => (a11diagVec χ (v ∘ π) k : A11F)) *
              (M : Matrix (Fin 4) (Fin 4) A11F) := by
          have h := hπ (fun k => (a11diagVec χ v k : A11F))
          rwa [hfun] at h
        have hmπ_SL : M * a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) =
            a11diagSL (a11diagVec χ (v ∘ π)) (a11diagVec_prod χ hχadd hχ0 (v ∘ π)) * M := by
          apply Subtype.ext
          simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_a11diagSL] using hmπ
        have hD_eq : a11diagSL u'' hu'' =
            a11diagSL (a11diagVec χ (v ∘ π)) (a11diagVec_prod χ hχadd hχ0 (v ∘ π)) := by
          have h2 : a11diagSL u'' hu'' * M =
              a11diagSL (a11diagVec χ (v ∘ π))
                (a11diagVec_prod χ hχadd hχ0 (v ∘ π)) * M := by
            rw [← hm'', hmπ_SL]
          exact mul_right_cancel h2
        rw [← hD_eq]
        exact hconj''
      have hψ_eq : ψ = Ψ π⁻¹ := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        obtain ⟨v, hv⟩ := a11ModelFun_surjective φ hrange χ hχadd hχ0 hχsurj hχinj xPow
          hxadd hxsurj hdmem hxmem hdiag hz hZL b
        rw [← hv]
        have keyψ : ((ψ (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) : ↥Bs) : G) =
            ((a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ π) : ↥Bs) : G) := by
          rw [hgact, ← hMφ]
          simp only [a11ModelFun, Subtype.coe_mk]
          calc φ M * (φ (a11diagSL (a11diagVec χ v)
                (a11diagVec_prod χ hχadd hχ0 v)) * xPow (a11M v)) * (φ M)⁻¹
              = φ M * φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  (xPow (a11M v) * (φ M)⁻¹) := by group
            _ = φ M * φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  ((φ M)⁻¹ * xPow (a11M v)) := by
                  rw [show xPow (a11M v) * (φ M)⁻¹ = (φ M)⁻¹ * xPow (a11M v) from by
                    rw [← map_inv]; exact hxcomm (a11M v) M⁻¹]
            _ = φ M * φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  (φ M)⁻¹ * xPow (a11M v) := by group
            _ = φ (M * a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) * M⁻¹) *
                  xPow (a11M v) := by simp only [← map_mul, ← map_inv]
            _ = φ (a11diagSL (a11diagVec χ (v ∘ π))
                  (a11diagVec_prod χ hχadd hχ0 (v ∘ π))) * xPow (a11M v) := by rw [hMD v]
            _ = ((a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ π) : ↥Bs) : G) := by
                  simp only [a11ModelFun, Subtype.coe_mk, hMπ v]
        have keyΨ : ((Ψ π⁻¹ (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) : ↥Bs) : G) =
            ((a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ π) : ↥Bs) : G) := by
          change ((ggConjAut Bs (hslPerm_mem π.symm)
            (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem v) : ↥Bs) : G) = _
          rw [ggConjAut_apply]
          simp only [a11ModelFun, Subtype.coe_mk]
          have hcomp : a11diagVec χ v ∘ π = a11diagVec χ (v ∘ π) := by
            funext k; simp only [Function.comp_apply, a11diagVec]; rw [hMπ v]
          calc φ (slPerm h2 π.symm) * (φ (a11diagSL (a11diagVec χ v)
                (a11diagVec_prod χ hχadd hχ0 v)) * xPow (a11M v)) * (φ (slPerm h2 π.symm))⁻¹
              = φ (slPerm h2 π.symm) *
                  φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  (xPow (a11M v) * (φ (slPerm h2 π.symm))⁻¹) := by group
            _ = φ (slPerm h2 π.symm) *
                  φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  ((φ (slPerm h2 π.symm))⁻¹ * xPow (a11M v)) := by
                  rw [show xPow (a11M v) * (φ (slPerm h2 π.symm))⁻¹ =
                    (φ (slPerm h2 π.symm))⁻¹ * xPow (a11M v) from by
                    rw [← map_inv]; exact hxcomm (a11M v) (slPerm h2 π.symm)⁻¹]
            _ = φ (slPerm h2 π.symm) *
                  φ (a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)) *
                  (φ (slPerm h2 π.symm))⁻¹ * xPow (a11M v) := by group
            _ = φ (slPerm h2 π.symm * a11diagSL (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v) *
                  (slPerm h2 π.symm)⁻¹) * xPow (a11M v) := by simp only [← map_mul, ← map_inv]
            _ = φ (a11diagSL (a11diagVec χ (v ∘ π))
                  (a11diagVec_prod χ hχadd hχ0 (v ∘ π))) * xPow (a11M v) := by
                  rw [hslPerm_diag π (a11diagVec χ v) (a11diagVec_prod χ hχadd hχ0 v)
                    (by rw [hcomp]; exact a11diagVec_prod χ hχadd hχ0 (v ∘ π))]
                  rw [a11diagSL_congr hcomp _ _]
            _ = ((a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (v ∘ π) : ↥Bs) : G) := by
                  simp only [a11ModelFun, Subtype.coe_mk, hMπ v]
        rw [keyψ, keyΨ]
      rw [hψ_eq]
      exact ⟨π⁻¹, rfl⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ggConjAut_mem_ggAutomizer (H := L) (Bs := Bs)
        (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
        (hslPerm_mem (Equiv.swap i.castSucc i.succ))

  · left
    have hli : LinearIndependent (ZMod 7) coroot := by
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg
      have e3 := congrFun hfg (3 : Fin 4)
      have e2 := congrFun hfg (2 : Fin 4)
      have e1 := congrFun hfg (1 : Fin 4)
      have e0 := congrFun hfg (0 : Fin 4)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coroot, Pi.sub_apply,
        Fin.sum_univ_three] at e3 e2 e1 e0
      simp at e3 e2 e1 e0
      norm_num at e3 e2 e1 e0
      intro i
      fin_cases i
      · exact e0
      · have h0 := e0
        rw [h0] at e1
        exact add_left_cancel e1
      · have h0 := e0
        have h1 : f 1 = g 1 := by
          rw [h0] at e1
          exact add_left_cancel e1
        rw [h1] at e2
        exact add_left_cancel e2
    have hspan : Module.finrank (ZMod 7) (Submodule.span (ZMod 7) (Set.range coroot)) =
        Fintype.card (Fin 3) := finrank_span_eq_card hli
    have hV : Module.finrank (ZMod 7) (Fin 4 → ZMod 7) = 4 := Module.finrank_fin_fun (ZMod 7)
    calc Module.finrank (ZMod 7) (Fin 4 → ZMod 7)
        = 4 := hV
      _ ≤ Module.finrank (ZMod 7) (Submodule.span (ZMod 7) (Set.range coroot)) + 1 := by
          rw [hspan, Fintype.card_fin]
  · refine ⟨1, 2, 1, 1, Subgroup.one_mem _, Subgroup.one_mem _, ?_, ?_, ?_⟩
    · simpa [simple] using ggConjAut_mem_ggAutomizer hJ1 (hnorm 1)
    · simpa [simple] using ggConjAut_mem_ggAutomizer hJ2 (hnorm 2)
    · intro hcomm
      have h := congrArg (fun ψ : MulAut ↥Bs =>
        ψ (a11ModelFun φ χ hχadd hχ0 xPow hdmem hxmem (Pi.single (2 : Fin 4) 1))) hcomm
      simp only [MulAut.mul_apply, MulAut.one_apply, inv_one] at h
      rw [hsimple_model 2 (Pi.single (2 : Fin 4) 1)] at h
      rw [hsimple_model 1 ((Pi.single (2 : Fin 4) 1) ∘
        Equiv.swap (Fin.castSucc (2 : Fin 3)) (Fin.succ (2 : Fin 3)))] at h
      rw [hsimple_model 1 (Pi.single (2 : Fin 4) 1)] at h
      rw [hsimple_model 2 ((Pi.single (2 : Fin 4) 1) ∘
        Equiv.swap (Fin.castSucc (1 : Fin 3)) (Fin.succ (1 : Fin 3)))] at h
      have h1 : ((Pi.single (2 : Fin 4) 1 : Fin 4 → ZMod 7) ∘
            Equiv.swap (Fin.castSucc (2 : Fin 3)) (Fin.succ (2 : Fin 3))) ∘
            Equiv.swap (Fin.castSucc (1 : Fin 3)) (Fin.succ (1 : Fin 3)) = Pi.single 3 1 := by
        funext k
        fin_cases k <;> simp [Function.comp_apply, Pi.single_eq_same, Pi.single_eq_of_ne,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
      have h2 : ((Pi.single (2 : Fin 4) 1 : Fin 4 → ZMod 7) ∘
            Equiv.swap (Fin.castSucc (1 : Fin 3)) (Fin.succ (1 : Fin 3))) ∘
            Equiv.swap (Fin.castSucc (2 : Fin 3)) (Fin.succ (2 : Fin 3)) = Pi.single 1 1 := by
        funext k
        fin_cases k <;> simp [Function.comp_apply, Pi.single_eq_same, Pi.single_eq_of_ne,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
      rw [h1, h2] at h
      exact one_ne_zero (congrFun (ha11inj h) (3 : Fin 4))

end CFSG.StandardType

end
