module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CH
public import CFSG.Quasithin.Vol2.Ch3E213MP6BB
public import CFSG.Quasithin.Vol2.E2StatementsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.E2.KG7

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open Ch3E213M CFSG.QuasithinUnique
open CFSG.Quasithin.ASInputs (twoGen rootGroupOf)

variable {k : Type} [Field k]

@[expose] def lineStab (k : Type) [Field k] : Subgroup (antiSp k) where
  carrier := {g | ∀ i : Fin 4, i ≠ 0 → glMat (g : GL (Fin 4) k) i 0 = 0}
  one_mem' := by
    intro i hi
    change (1 : Matrix (Fin 4) (Fin 4) k) i 0 = 0
    rw [Matrix.one_apply_ne hi]
  mul_mem' := by
    intro g h hg hh i hi
    change (glMat (g : GL (Fin 4) k) * glMat (h : GL (Fin 4) k)) i 0 = 0
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hg i hi, zero_mul]
    · intro l _ hl
      rw [hh l hl, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ 0) h0
  inv_mem' := by
    intro g hg i hi
    have h1 : glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) * glMat (g : GL (Fin 4) k) = 1 :=
      (g : GL (Fin 4) k).inv_mul
    have e0 := congrFun (congrFun h1 i) 0
    have e00 := congrFun (congrFun h1 0) 0
    rw [Matrix.mul_apply, Finset.sum_eq_single 0, Matrix.one_apply_ne hi] at e0
    · rw [Matrix.mul_apply, Finset.sum_eq_single 0, Matrix.one_apply_eq] at e00
      · have h00 : glMat (g : GL (Fin 4) k) 0 0 ≠ 0 := right_ne_zero_of_mul_eq_one e00
        exact (mul_eq_zero.mp e0).resolve_right h00
      · intro l _ hl
        rw [hg l hl, mul_zero]
      · intro h0
        exact absurd (Finset.mem_univ 0) h0
    · intro l _ hl
      rw [hg l hl, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ 0) h0

theorem mem_lineStab_of_isUpper {g : antiSp k} (hg : IsUpper g) : g ∈ lineStab k :=
  fun i hi => hg i 0 (Fin.pos_of_ne_zero hi)

@[expose] def sMat (k : Type) [Field k] : Matrix (Fin 4) (Fin 4) k :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

theorem sMat_mul_self : sMat k * sMat k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def sElt (k : Type) [Field k] : antiSp k :=
  ⟨⟨sMat k, sMat k, sMat_mul_self, sMat_mul_self⟩, by
    rw [mem_antiSp]
    ext i j
    change ((sMat k).transpose * minorJ k * sMat k) i j = minorJ k i j
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
    fin_cases i <;> fin_cases j <;> simp [sMat]⟩

theorem glMat_sElt : glMat ((sElt k : antiSp k) : GL (Fin 4) k) = sMat k := rfl

theorem sElt_mem_lineStab : sElt k ∈ lineStab k := by
  intro i hi
  rw [glMat_sElt]
  fin_cases i <;> simp_all [sMat]

theorem sElt_mem_subfieldSp (F₀ : Subfield k) : sElt k ∈ subfieldSp F₀ := by
  intro i j
  rw [glMat_sElt]
  fin_cases i <;> fin_cases j <;> simp [sMat, F₀.zero_mem, F₀.one_mem]

theorem not_isUpper_sElt : ¬ IsUpper (sElt k) := by
  intro h
  have := h 2 1 (by decide)
  rw [glMat_sElt] at this
  simp [sMat] at this

theorem wLong_not_mem_lineStab : (wLong : antiSp k) ∉ lineStab k := by
  intro h
  have := h 3 (by decide)
  rw [glMat_wLong, minorJ_apply] at this
  simp at this

variable [CharP k 2]

theorem isUpper_of_commute_zl_zs {g : antiSp k} {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : g * uElt 0 0 a 0 = uElt 0 0 a 0 * g) (hs : g * uElt 0 b 0 0 = uElt 0 b 0 0 * g) :
    IsUpper g := by
  have hl' : glMat (g : GL (Fin 4) k) * uMat 0 0 a 0 =
      uMat 0 0 a 0 * glMat (g : GL (Fin 4) k) := by
    have := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) hl
    simpa [glMat_uElt] using this
  have hs' : glMat (g : GL (Fin 4) k) * uMat 0 b 0 0 =
      uMat 0 b 0 0 * glMat (g : GL (Fin 4) k) := by
    have := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) hs
    simpa [glMat_uElt] using this
  have e13 := congrFun (congrFun hl' 1) 3
  have e23 := congrFun (congrFun hl' 2) 3
  have e33 := congrFun (congrFun hl' 3) 3
  have e01 := congrFun (congrFun hl' 0) 1
  have f23 := congrFun (congrFun hs' 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at e13 e23 e33 e01 f23
  refine isUpper_of_flag ?_ ?_ ?_ ?_ ?_
  · simpa [ha] using e13
  · simpa [ha] using e23
  · simpa [ha] using e33
  · simpa [hb] using f23
  · simpa [ha] using e01

theorem isUpper_of_commute_of_spansCenter {W : Subgroup (antiSp k)}
    (hWZ : W ≤ antiUnipotentCenter k) (hsp : SpansCenter W) {g : antiSp k}
    (hg : ∀ w ∈ W, g * w = w * g) : IsUpper g := by
  obtain ⟨b, c, b', c', h1, h2, -, hdet⟩ := P6B.exists_indep hWZ hsp
  have m1 : glMat (g : GL (Fin 4) k) * uMat 0 b c 0 =
      uMat 0 b c 0 * glMat (g : GL (Fin 4) k) := by
    have := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) (hg _ h1)
    simpa [glMat_uElt] using this
  have m2 : glMat (g : GL (Fin 4) k) * uMat 0 b' c' 0 =
      uMat 0 b' c' 0 * glMat (g : GL (Fin 4) k) := by
    have := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) (hg _ h2)
    simpa [glMat_uElt] using this
  have a00 := congrFun (congrFun m1 0) 0
  have b00 := congrFun (congrFun m2 0) 0
  have a01 := congrFun (congrFun m1 0) 1
  have b01 := congrFun (congrFun m2 0) 1
  have a13 := congrFun (congrFun m1 1) 3
  have b13 := congrFun (congrFun m2 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at a00 b00 a01 b01 a13 b13
  set Y := glMat (g : GL (Fin 4) k)
  have key : ∀ x y : k, b * x + c * y = 0 → b' * x + c' * y = 0 → x = 0 ∧ y = 0 := by
    intro x y hx hy
    have ex : x * (c * b' - c' * b) = 0 := by linear_combination c * hy - c' * hx
    have ey : y * (c * b' - c' * b) = 0 := by linear_combination b' * hx - b * hy
    exact ⟨(mul_eq_zero.mp ex).resolve_right hdet, (mul_eq_zero.mp ey).resolve_right hdet⟩
  obtain ⟨h20, h30⟩ := key (Y 2 0) (Y 3 0) (by linear_combination -a00)
    (by linear_combination -b00)
  obtain ⟨h21, h31⟩ := key (Y 2 1) (Y 3 1) (by linear_combination -a01)
    (by linear_combination -b01)
  obtain ⟨-, h10⟩ := key (Y 1 1 - Y 3 3) (Y 1 0) (by linear_combination a13)
    (by linear_combination b13)
  exact isUpper_of_flag h10 h20 h30 h21 h31

omit [CharP k 2] in
theorem isUpper_pow {g : antiSp k} (hg : IsUpper g) (m : ℕ) :
    IsUpper (g ^ m) ∧ ∀ i, glMat ((g ^ m : antiSp k) : GL (Fin 4) k) i i =
      glMat (g : GL (Fin 4) k) i i ^ m := by
  induction m with
  | zero =>
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change (1 : Matrix (Fin 4) (Fin 4) k) i j = 0
      exact Matrix.one_apply_ne (ne_of_gt hij)
    · change (1 : Matrix (Fin 4) (Fin 4) k) i i = _
      rw [Matrix.one_apply_eq, pow_zero]
  | succ m ih =>
    refine ⟨by rw [pow_succ]; exact isUpper_mul ih.1 hg, fun i => ?_⟩
    rw [pow_succ]
    change (glMat ((g ^ m : antiSp k) : GL (Fin 4) k) * glMat (g : GL (Fin 4) k)) i i = _
    rw [upper_mul_apply_self ih.1 hg, ih.2 i, pow_succ]

theorem mem_antiUnipotent_of_isUpper_of_pow {g : antiSp k} (hg : IsUpper g) {m : ℕ}
    (hm : g ^ 2 ^ m = 1) : g ∈ antiUnipotent k := by
  refine (mem_antiUnipotent_iff_upper g).mpr ⟨hg, fun i => ?_⟩
  have h1 := (isUpper_pow hg (2 ^ m)).2 i
  rw [hm] at h1
  change (1 : Matrix (Fin 4) (Fin 4) k) i i = _ at h1
  rw [Matrix.one_apply_eq] at h1
  have h2 : (glMat (g : GL (Fin 4) k) i i - 1) ^ 2 ^ m = 0 := by
    rw [sub_pow_char_pow, ← h1, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)

theorem isUpper_of_mem_normalizer {F₀ : Subfield k} {c y : antiSp k} (hc : IsUpper c)
    (hy : y ∈ Subgroup.normalizer
      (((subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ antiUnipotent k : Subgroup _) :
        Set (antiSp k))) : IsUpper y := by
  set y' := c⁻¹ * y * c with hy'
  have key : ∀ u ∈ subfieldSp F₀, u ∈ antiUnipotent k → y'⁻¹ * u * y' ∈ antiUnipotent k := by
    intro u huF huU
    have h1 : c * u * c⁻¹ ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ antiUnipotent k :=
      ⟨⟨u, huF, rfl⟩, (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_isUpper hc) u).mp huU⟩
    have h2 := ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy)) _).mp h1
    have h3 := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_isUpper (isUpper_inv hc))
      _).mp h2.2
    have e : c⁻¹ * (y⁻¹ * (c * u * c⁻¹) * y⁻¹⁻¹) * c⁻¹⁻¹ = y'⁻¹ * u * y' := by
      rw [hy']
      group
    rwa [e] at h3
  have hcol : ∀ u ∈ subfieldSp F₀, u ∈ antiUnipotent k →
      glMat (u : GL (Fin 4) k) * glMat (y' : GL (Fin 4) k) =
        glMat (y' : GL (Fin 4) k) * glMat ((y'⁻¹ * u * y' : antiSp k) : GL (Fin 4) k) := by
    intro u _ _
    change glMat (u : GL (Fin 4) k) * glMat (y' : GL (Fin 4) k) =
      glMat ((y' * (y'⁻¹ * u * y') : antiSp k) : GL (Fin 4) k)
    rw [show y' * (y'⁻¹ * u * y') = u * y' by group]
    rfl
  have hu1F : uElt (1 : k) 0 0 0 ∈ subfieldSp F₀ :=
    uElt_mem_subfieldSp F₀.one_mem F₀.zero_mem F₀.zero_mem F₀.zero_mem
  have hu2F : uElt (0 : k) 0 0 1 ∈ subfieldSp F₀ :=
    uElt_mem_subfieldSp F₀.zero_mem F₀.zero_mem F₀.zero_mem F₀.one_mem
  obtain ⟨a₁, b₁, c₁, d₁, h₁⟩ :=
    mem_antiUnipotent.mp (key _ hu1F (uElt_mem_antiUnipotent 1 0 0 0))
  obtain ⟨a₂, b₂, c₂, d₂, h₂⟩ :=
    mem_antiUnipotent.mp (key _ hu2F (uElt_mem_antiUnipotent 0 0 0 1))
  have E1 := hcol _ hu1F (uElt_mem_antiUnipotent 1 0 0 0)
  have E2 := hcol _ hu2F (uElt_mem_antiUnipotent 0 0 0 1)
  rw [h₁, glMat_uElt] at E1
  rw [h₂, glMat_uElt] at E2
  set Y := glMat (y' : GL (Fin 4) k)
  have x00 := congrFun (congrFun E1 0) 0
  have x20 := congrFun (congrFun E1 2) 0
  have x21 := congrFun (congrFun E1 2) 1
  have z10 := congrFun (congrFun E2 1) 0
  have z11 := congrFun (congrFun E2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at x00 x20 x21 z10 z11
  have h10 : Y 1 0 = 0 := x00
  have h30 : Y 3 0 = 0 := x20
  have h20 : Y 2 0 = 0 := z10
  have h31 : Y 3 1 = 0 := by linear_combination x21 + a₁ * h20
  have h21 : Y 2 1 = 0 := by linear_combination z11 + a₂ * h10
  have hup : IsUpper y' := isUpper_of_flag h10 h20 h30 h21 h31
  have e : y = c * y' * c⁻¹ := by rw [hy']; group
  rw [e]
  exact isUpper_mul (isUpper_mul hc hup) (isUpper_inv hc)

omit [CharP k 2] in
theorem le_normalizer_twoGen {Q : Type*} [Group Q] (P : Subgroup Q) :
    P ≤ Subgroup.normalizer (twoGen P : Set Q) := by
  have key : ∀ p ∈ P, ∀ x ∈ twoGen P, p * x * p⁻¹ ∈ twoGen P := by
    intro p hp x hx
    have h : twoGen P ≤ (twoGen P).comap (MulAut.conj p).toMonoidHom := by
      rw [twoGen, Subgroup.closure_le]
      rintro y ⟨hyP, m, hm⟩
      refine Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hp hyP) (P.inv_mem hp), m, ?_⟩
      show (p * y * p⁻¹) ^ 2 ^ m = 1
      rw [conj_pow, hm, mul_one, mul_inv_cancel]
    exact h hx
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key p hp x, fun hx => ?_⟩
  have := key p⁻¹ (P.inv_mem hp) _ hx
  rwa [inv_inv, show p⁻¹ * (p * x * p⁻¹) * p = x by group] at this

variable [Finite k]

theorem not_le_rootGroupOf {F₀ : Subfield k} {c : antiSp k} (hc : IsUpper c)
    {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k) (hsp : SpansCenter W)
    {P : Subgroup (antiSp k)}
    (hP : IsMaxParabolic2 ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) P)
    (hBP : (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓
      Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) ≤ P) :
    ¬ W ≤ rootGroupOf P := by
  intro hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hY
  have hPY : P ≤ Y := hP.1.1
  have hTU : twoGen P ≤ antiUnipotent k := by
    rw [twoGen, Subgroup.closure_le]
    rintro x ⟨hxP, m, hm⟩
    have hx : x ∈ twoGen P := Subgroup.subset_closure ⟨hxP, m, hm⟩
    have hxC : ∀ w ∈ W, x * w = w * x := fun w hw =>
      Subgroup.mem_centralizer_iff.mp (hW hw).2 x hx
    exact mem_antiUnipotent_of_isUpper_of_pow (isUpper_of_commute_of_spansCenter hWZ hsp hxC) hm
  have hS := isSylowOf_inf_antiUnipotent (F₀ := F₀) hc
  rw [← CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf] at hS
  have hUT : Y ⊓ antiUnipotent k ≤ twoGen P := by
    intro u hu
    obtain ⟨m, hm⟩ := hS.2.1 ⟨u, hu⟩
    refine Subgroup.subset_closure ⟨hBP ⟨hu.1, Subgroup.le_normalizer hu.2⟩, m, ?_⟩
    have h2 := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have heq : twoGen P = Y ⊓ antiUnipotent k := by
    refine le_antisymm (le_inf ?_ hTU) hUT
    rw [twoGen, Subgroup.closure_le]
    rintro x ⟨hxP, -⟩
    exact hPY hxP
  have hPup : ∀ p ∈ P, IsUpper p := fun p hp =>
    isUpper_of_mem_normalizer hc (heq ▸ le_normalizer_twoGen P hp)
  have hQpar : IsParabolic2 Y (Y ⊓ lineStab k) := by
    refine ⟨inf_le_left, Y ⊓ antiUnipotent k, hS, fun y hy => ⟨hy.1, ?_⟩⟩
    exact mem_lineStab_of_isUpper (isUpper_of_mem_normalizer hc hy.2)
  have hcS : c ∈ lineStab k := mem_lineStab_of_isUpper hc
  have hcS' : c⁻¹ ∈ lineStab k := mem_lineStab_of_isUpper (isUpper_inv hc)
  have hQne : Y ⊓ lineStab k ≠ Y := by
    intro hQY
    have hw : c * wLong * c⁻¹ ∈ Y := ⟨wLong, wLong_mem_subfieldSp F₀, rfl⟩
    rw [← hQY] at hw
    apply wLong_not_mem_lineStab (k := k)
    have := (lineStab k).mul_mem ((lineStab k).mul_mem hcS' hw.2) hcS
    rwa [show c⁻¹ * (c * wLong * c⁻¹) * c = wLong by group] at this
  have hPQ : P ≤ Y ⊓ lineStab k := fun p hp => ⟨hPY hp, mem_lineStab_of_isUpper (hPup p hp)⟩
  have hQP := hP.2.2 (Y ⊓ lineStab k) hQpar hQne hPQ
  have hsQ : c * sElt k * c⁻¹ ∈ Y ⊓ lineStab k :=
    ⟨⟨sElt k, sElt_mem_subfieldSp F₀, rfl⟩,
      (lineStab k).mul_mem ((lineStab k).mul_mem hcS sElt_mem_lineStab) hcS'⟩
  rw [hQP] at hsQ
  apply not_isUpper_sElt (k := k)
  have := isUpper_mul (isUpper_mul (isUpper_inv hc) (hPup _ hsQ)) hc
  rwa [show c⁻¹ * (c * sElt k * c⁻¹) * c = sElt k by group] at this

end CFSG.Quasithin.E2.KG7
