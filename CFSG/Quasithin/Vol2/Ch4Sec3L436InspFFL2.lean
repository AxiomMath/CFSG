module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin.H13.Ch4.FFL2

open Matrix

section Fix

variable {U : Type} [CommGroup U]

@[expose] def fixPts (a : MulAut U) : Subgroup U where
  carrier := {u | a u = u}
  one_mem' := map_one a
  mul_mem' := fun {x y} (hx : a x = x) (hy : a y = y) => show a (x * y) = x * y by
    rw [map_mul, hx, hy]
  inv_mem' := fun {x} (hx : a x = x) => show a x⁻¹ = x⁻¹ by rw [map_inv, hx]

theorem mem_fixPts {a : MulAut U} {u : U} : u ∈ fixPts a ↔ a u = u := Iff.rfl

theorem fixV_le_fixPts {A : Subgroup (MulAut U)} {a : MulAut U} (ha : a ∈ A) :
    CFSG.Quasithin.fixV A ≤ fixPts a :=
  fun _ hu => hu a ha

theorem card_fixPts_conj (a k : MulAut U) :
    Nat.card (fixPts (k⁻¹ * a * k)) = Nat.card (fixPts a) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨k u, ?_⟩
      invFun := fun u => ⟨k⁻¹ u, ?_⟩
      left_inv := fun u => Subtype.ext (MulAut.inv_apply_self U k u)
      right_inv := fun u => Subtype.ext (MulAut.apply_inv_self U k u) }
  · have hu : (k⁻¹ * a * k) u = u := u.2
    rw [MulAut.mul_apply, MulAut.mul_apply] at hu
    show a (k u) = k u
    have := congrArg k hu
    rwa [MulAut.apply_inv_self U] at this
  · have hu : a u = u := u.2
    show (k⁻¹ * a * k) (k⁻¹ u) = k⁻¹ u
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self U, hu]

theorem exists_card_fixPts [Finite U] {d ℓ : ℕ} (hℓ : ℓ.Prime) {h : MulAut U}
    (hh : orderOf h = ℓ) (hU : Nat.card U = 2 ^ d) :
    ∃ e < d, Nat.card (fixPts h) = 2 ^ e ∧ ℓ ∣ 2 ^ d - 2 ^ e := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h1 : h ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hh
    exact hℓ.one_lt.ne hh
  let Kz := Subgroup.zpowers h
  have hK : IsPGroup ℓ Kz := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hh, pow_one])
  have hset : MulAction.fixedPoints Kz U = (fixPts h : Set U) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hv
      exact hv ⟨h, Subgroup.mem_zpowers h⟩
    · intro hv g
      have hle : Kz ≤ MulAction.stabilizer (MulAut U) v := by
        rw [Subgroup.zpowers_le]
        exact hv
      exact hle g.2
  have hmod := hK.card_modEq_card_fixedPoints U
  rw [hset] at hmod
  change Nat.card U ≡ Nat.card (fixPts h) [MOD ℓ] at hmod
  obtain ⟨e, hed, hFe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hU ▸ Subgroup.card_subgroup_dvd_card (fixPts h))
  have hlt : e < d := by
    refine lt_of_le_of_ne hed fun hde => h1 ?_
    have htop : fixPts h = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hFe, hU, hde])
    ext v
    have hv : v ∈ fixPts h := htop ▸ Subgroup.mem_top v
    rw [MulAut.one_apply]
    exact hv
  refine ⟨e, hlt, hFe, ?_⟩
  rw [hFe, hU] at hmod
  exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hlt.le)).mp hmod.symm

theorem two_pow_mul_card_fixPts_le [Finite U] (hU : IsPGroup 2 U) {m ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hprim : ∀ k : ℕ, 0 < k → k < 2 * m → ¬ ℓ ∣ 2 ^ k - 1) {a h : MulAut U}
    (ha : a * a = 1) (hah : a * h * a = h⁻¹) (hh : orderOf h = ℓ) :
    2 ^ m * Nat.card (fixPts a) ≤ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hU
  obtain ⟨e, hed, hFe, hdvd⟩ := exists_card_fixPts hℓ hh hd
  have hde : 2 * m ≤ d - e := by
    have hfac : 2 ^ d - 2 ^ e = 2 ^ e * (2 ^ (d - e) - 1) := by
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
    rw [hfac] at hdvd
    have hcop : Nat.Coprime ℓ (2 ^ e) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2)
    have h2 := hcop.dvd_of_dvd_mul_left hdvd
    by_contra hlt
    push Not at hlt
    exact hprim (d - e) (by omega) hlt h2
  have hodd : ℓ % 2 = 1 := Nat.odd_iff.mp (hℓ.odd_of_ne_two hℓ2)
  set k := h ^ ((ℓ + 1) / 2) with hk
  have hkk : k * k = h := by
    have e2 : (ℓ + 1) / 2 + (ℓ + 1) / 2 = ℓ + 1 := by omega
    rw [hk, ← pow_add, e2, pow_succ, ← hh, pow_orderOf_eq_one, one_mul]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hconj : ∀ x : MulAut U, a * x * a = MulAut.conj a x := fun x => by
    rw [MulAut.conj_apply, hainv]
  have hak : a * k * a = k⁻¹ := by
    rw [hconj, hk, map_pow, ← hconj, hah, inv_pow]
  have h1 : a * k⁻¹ * a = k := by
    calc a * k⁻¹ * a = a⁻¹ * k⁻¹ * a⁻¹ := by rw [hainv]
      _ = (a * k * a)⁻¹ := by group
      _ = k := by rw [hak, inv_inv]
  set b := k⁻¹ * a * k with hb
  have hab : a * b = h := by
    calc a * b = (a * k⁻¹ * a) * k := by rw [hb]; group
      _ = h := by rw [h1, hkk]
  have hle : fixPts a ⊓ fixPts b ≤ fixPts h := by
    intro u hu
    obtain ⟨hua, hub⟩ := Subgroup.mem_inf.mp hu
    rw [mem_fixPts] at hua hub ⊢
    rw [← hab, MulAut.mul_apply, hub, hua]
  have hcb : Nat.card (fixPts b) = Nat.card (fixPts a) := card_fixPts_conj a k
  have hidx : ∀ X : Subgroup U, Nat.card X * X.index = 2 ^ d := fun X => by
    rw [Subgroup.card_mul_index, hd]
  have hih : (fixPts h).index = 2 ^ (d - e) := by
    have e1 := hidx (fixPts h)
    rw [hFe] at e1
    have e2 : 2 ^ e * 2 ^ (d - e) = 2 ^ d := by rw [← pow_add, Nat.add_sub_cancel' hed.le]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (e1.trans e2.symm)
  have hib : (fixPts b).index = (fixPts a).index := by
    have e1 := hidx (fixPts b)
    have e2 := hidx (fixPts a)
    rw [hcb] at e1
    have hpos : 0 < Nat.card (fixPts a) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  have hfin : (fixPts a ⊓ fixPts b).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hi1 : (fixPts h).index ≤ (fixPts a ⊓ fixPts b).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hfin) (Subgroup.index_dvd_of_le hle)
  have hi2 : (fixPts a ⊓ fixPts b).index ≤ (fixPts a).index * (fixPts b).index :=
    Subgroup.index_inf_le
  have hsq : (2 ^ m) ^ 2 ≤ (fixPts a).index ^ 2 := by
    calc (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (d - e) := Nat.pow_le_pow_right (by norm_num) hde
      _ = (fixPts h).index := hih.symm
      _ ≤ (fixPts a).index * (fixPts b).index := hi1.trans hi2
      _ = (fixPts a).index ^ 2 := by rw [hib, sq]
  have hm : 2 ^ m ≤ (fixPts a).index := (Nat.pow_le_pow_iff_left two_ne_zero).mp hsq
  calc 2 ^ m * Nat.card (fixPts a) ≤ (fixPts a).index * Nat.card (fixPts a) :=
        Nat.mul_le_mul_right _ hm
    _ = Nat.card U := by rw [mul_comm, Subgroup.card_mul_index]

end Fix

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def t0 : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩

theorem exists_mul_self_eq (x : F) : ∃ μ : F, μ * μ = x := by
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' x
  exact ⟨μ, hμ.symm⟩

omit [Finite F] [CharP F 2] in
theorem det_entries (g : SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have := g.2
  rwa [det_fin_two] at this

theorem exists_conj_t0 {a : SpecialLinearGroup (Fin 2) F} (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ g : SpecialLinearGroup (Fin 2) F, g * t0 * g⁻¹ = a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet := det_entries a
  rw [← hM] at hdet
  have hsq : M * M = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) ha
    simpa [hM] using this
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    have := congrFun₂ hsq 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
    have := congrFun₂ hsq 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hδ : M 1 1 = M 0 0 := by
    have hsub : (M 1 1 + M 0 0) * (M 1 1 + M 0 0) = 0 := by
      linear_combination e00 + e11 + 2 * hdet + 2 * h2
    have hsum := mul_self_eq_zero.mp hsub
    linear_combination hsum - M 0 0 * h2
  have hdet' : M 0 0 * M 0 0 - M 0 1 * M 1 0 = 1 := by
    have h' := hdet
    rw [hδ] at h'
    exact h'
  by_cases hβ : M 0 1 = 0
  ·
    have hα : M 0 0 = 1 := by
      have hsub : (M 0 0 + 1) * (M 0 0 + 1) = 0 := by
        rw [hβ] at e00
        linear_combination e00 + (M 0 0 + 1) * h2
      have hsum := mul_self_eq_zero.mp hsub
      linear_combination hsum - h2
    have hγ : M 1 0 ≠ 0 := by
      intro hγ
      apply ha1
      apply Subtype.ext
      change M = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hα, hβ, hγ, hδ]
    obtain ⟨μ, hμ⟩ := exists_mul_self_eq (M 1 0)⁻¹
    have hμγ : μ * μ * M 1 0 = 1 := by rw [hμ, inv_mul_cancel₀ hγ]
    let g : SpecialLinearGroup (Fin 2) F :=
      ⟨!![0, μ; μ * M 1 0, 0], by
        rw [det_fin_two_of]
        linear_combination -hμγ - h2⟩
    refine ⟨g, mul_inv_eq_of_eq_mul ?_⟩
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) F) *
      ((t0 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      M * (g : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, t0, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, hδ]
    ring
  ·
    obtain ⟨μ, hμ⟩ := exists_mul_self_eq (M 0 1)⁻¹
    have hμβ : μ * μ * M 0 1 = 1 := by rw [hμ, inv_mul_cancel₀ hβ]
    let g : SpecialLinearGroup (Fin 2) F :=
      ⟨!![μ * M 0 1, 0; μ * (M 0 0 + 1), μ], by
        rw [det_fin_two_of]
        linear_combination hμβ⟩
    refine ⟨g, mul_inv_eq_of_eq_mul ?_⟩
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) F) *
      ((t0 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      M * (g : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, t0, Matrix.mul_apply, Fin.sum_univ_two, hδ]
    · linear_combination (-(M 0 0 * M 0 1 * μ)) * h2
    · ring
    · linear_combination (-μ) * e00
    · linear_combination μ * h2

omit [Finite F] [CharP F 2] in
theorem pow_entries_of_lower_eq_zero {h : SpecialLinearGroup (Fin 2) F}
    (hγ : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (k : ℕ) :
    ((h ^ k : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((h ^ k : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    show ((h ^ k).1 * h.1) 1 0 = 0 ∧ ((h ^ k).1 * h.1) 0 0 = h.1 0 0 ^ (k + 1)
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    have hγ' : h.1 1 0 = 0 := hγ
    rw [ih.1, ih.2, hγ']
    constructor <;> ring

theorem exists_inverted_by_t0 {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓF : ¬ ℓ ∣ Nat.card F - 1) {h : SpecialLinearGroup (Fin 2) F} (hh : orderOf h = ℓ) :
    ∃ h₀ : SpecialLinearGroup (Fin 2) F, orderOf h₀ = ℓ ∧ t0 * h₀ * t0 = h₀⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 2) (Fin 2) F := (h : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet := det_entries h
  rw [← hM] at hdet
  have hord2 : h * h ≠ 1 := by
    intro h11
    have hdvd : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h11])
    rw [hh] at hdvd
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp hdvd)
  have hτ : M 0 0 + M 1 1 ≠ 0 := by
    intro hτ
    apply hord2
    apply Subtype.ext
    show M * M = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -hdet + M 0 0 * hτ - h2
    · linear_combination M 0 1 * hτ
    · linear_combination M 1 0 * hτ
    · linear_combination -hdet + M 1 1 * hτ - h2
  have hγ : M 1 0 ≠ 0 := by
    intro hγ
    obtain ⟨-, hpow⟩ := pow_entries_of_lower_eq_zero hγ ℓ
    rw [← hh, pow_orderOf_eq_one] at hpow
    change (1 : Matrix (Fin 2) (Fin 2) F) 0 0 = M 0 0 ^ orderOf h at hpow
    rw [Matrix.one_apply_eq, hh] at hpow
    have hα0 : M 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_pow hℓ.ne_zero] at hpow
      exact one_ne_zero hpow
    set u : Fˣ := Units.mk0 (M 0 0) hα0 with hu
    have hu1 : u ^ ℓ = 1 := Units.ext (by simp [hu, ← hpow])
    have hdvd1 : orderOf u ∣ ℓ := orderOf_dvd_of_pow_eq_one hu1
    have hdvd2 : orderOf u ∣ Nat.card F - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard u
    have hou : orderOf u = 1 := by
      rcases (Nat.dvd_prime hℓ).mp hdvd1 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hdvd2) hℓF
    have hα : M 0 0 = 1 := by
      have := orderOf_eq_one_iff.mp hou
      have := congrArg Units.val this
      simpa [hu] using this
    have hδ : M 1 1 = 1 := by
      rw [hα, hγ] at hdet
      linear_combination hdet
    apply hord2
    apply Subtype.ext
    show M * M = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hα, hγ, hδ]
    linear_combination M 0 1 * h2
  obtain ⟨μ, hμ⟩ := exists_mul_self_eq (M 1 0 / (M 0 0 + M 1 1))
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact div_ne_zero hγ hτ hμ.symm
  have hμτ : μ * μ * (M 0 0 + M 1 1) = M 1 0 := by
    rw [hμ, div_mul_cancel₀ _ hτ]
  let d : SpecialLinearGroup (Fin 2) F :=
    ⟨!![μ, 0; 0, μ⁻¹], by rw [det_fin_two_of]; field_simp; ring⟩
  let h₀ : SpecialLinearGroup (Fin 2) F :=
    ⟨!![M 0 0, μ * μ * M 0 1; M 0 0 + M 1 1, M 1 1], by
      rw [det_fin_two_of]
      linear_combination hdet - M 0 1 * hμτ⟩
  have hconj : h₀ = d * h * d⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Subtype.ext
    show (h₀ : Matrix (Fin 2) (Fin 2) F) * (d : Matrix (Fin 2) (Fin 2) F) =
      (d : Matrix (Fin 2) (Fin 2) F) * M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀, d, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ((try field_simp); all_goals first | ring1 | linear_combination hμτ)
  refine ⟨h₀, ?_, ?_⟩
  · rw [hconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hh]
  · apply eq_inv_of_mul_eq_one_left
    apply Subtype.ext
    show (t0 : SpecialLinearGroup (Fin 2) F).1 * h₀.1 * (t0 : SpecialLinearGroup (Fin 2) F).1 *
      h₀.1 = 1
    have hdet0 : M 0 0 * M 1 1 - μ * μ * M 0 1 * (M 0 0 + M 1 1) = 1 := by
      linear_combination hdet - M 0 1 * hμτ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀, t0, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hdet0 + (2 * M 0 0 ^ 2 + 2 * M 0 0 * M 1 1 + M 1 1 ^ 2 +
        μ * μ * M 0 1 * (M 0 0 + M 1 1)) * h2
    · linear_combination (M 0 0 * (μ * μ * M 0 1) + μ * μ * M 0 1 * M 1 1 + M 0 0 * M 1 1 +
        M 1 1 ^ 2) * h2
    · linear_combination (M 0 0 ^ 2 + 2 * M 0 0 * M 1 1 + M 1 1 ^ 2) * h2
    · linear_combination hdet0 + ((M 0 0 + M 1 1) * (μ * μ * M 0 1) + M 1 1 ^ 2) * h2

theorem two_pow_mul_card_fixPts_le_of_sl2 {U : Type} [CommGroup U] [Finite U]
    (hU : IsPGroup 2 U) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3) (hF : Nat.card F = 2 ^ m)
    (L : Subgroup (MulAut U)) (e : ↥L ≃* SpecialLinearGroup (Fin 2) F) {a : MulAut U}
    (haL : a ∈ L) (ha : a * a = 1) (ha1 : a ≠ 1) :
    2 ^ m * Nat.card (fixPts a) ≤ Nat.card U := by
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * m) (by omega) (by omega)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ (2 * m) := dvd_pow_self 2 (by omega)
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self Nat.one_le_two_pow] at h2
    omega
  have hℓF : ¬ ℓ ∣ Nat.card F - 1 := by
    rw [hF]
    exact hprim m (by omega) (by omega)
  have hcardSL : ℓ ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF, ← pow_mul,
      mul_comm m 2]
    exact Dvd.dvd.mul_left hℓdvd _
  obtain ⟨h', hh'⟩ := exists_prime_orderOf_dvd_card' ℓ hcardSL
  obtain ⟨h₀, hh₀, hinv⟩ := exists_inverted_by_t0 hℓ hℓ2 hℓF hh'
  set a' := e ⟨a, haL⟩ with ha'
  have ha'2 : a' * a' = 1 := by
    rw [ha', ← map_mul]
    have : (⟨a, haL⟩ : ↥L) * ⟨a, haL⟩ = 1 := Subtype.ext ha
    rw [this, map_one]
  have ha'1 : a' ≠ 1 := by
    intro h1
    apply ha1
    have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    exact this
  obtain ⟨g, hg⟩ := exists_conj_t0 ha'2 ha'1
  set h₁ := g * h₀ * g⁻¹ with hh₁
  have hinv₁ : a' * h₁ * a' = h₁⁻¹ := by
    rw [← hg, hh₁]
    calc g * t0 * g⁻¹ * (g * h₀ * g⁻¹) * (g * t0 * g⁻¹) = g * (t0 * h₀ * t0) * g⁻¹ := by
          group
      _ = (g * h₀ * g⁻¹)⁻¹ := by rw [hinv]; group
  have hord : orderOf ((e.symm h₁ : ↥L) : MulAut U) = ℓ := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hh₁, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hh₀]
  have hah : a * ((e.symm h₁ : ↥L) : MulAut U) * a = ((e.symm h₁ : ↥L) : MulAut U)⁻¹ := by
    have e1 : ((e.symm a' : ↥L) : MulAut U) = a := by rw [ha', MulEquiv.symm_apply_apply]
    rw [← e1, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hinv₁, map_inv,
      Subgroup.coe_inv]
  exact two_pow_mul_card_fixPts_le hU hℓ hℓ2 hprim ha hah hord

end SL2

theorem isPGroup_of_sq_eq_one {U : Type} [Group U] (hU2 : ∀ u : U, u ^ 2 = 1) :
    IsPGroup 2 U := fun u => ⟨1, by rw [pow_one, hU2 u]⟩

theorem eq_of_sl2 {U : Type} [CommGroup U] [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1)
    {L K A : Subgroup (MulAut U)} {n m : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ m) (e : ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))
    (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hAK : A ≤ K) (hA1 : A ≠ ⊥)
    (hA2 : CFSG.Quasithin.IsElemAbelian2 A) (hAcard : Nat.card ↥A ≤ 2 ^ n)
    (hoff : Nat.card U ≤ Nat.card ↥A * Nat.card ↥(CFSG.Quasithin.fixV A)) : L = K := by
  have e' : ↥L ≃* SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have hcardL : Nat.card ↥L = 2 ^ m * (4 ^ m - 1) := by
    rw [Nat.card_congr e'.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF,
      ← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hdvd : 2 ^ n * (4 ^ n - 1) ∣ 2 ^ m * (4 ^ m - 1) := by
    rw [← hcardK, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  have hm1 : 1 ≤ m := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hF] at h2
    by_contra h0
    have : m = 0 := by omega
    subst this
    norm_num at h2
  have hodd : ∀ k : ℕ, 1 ≤ k → Odd (4 ^ k - 1) := fun k hk => by
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 4 ^ k % 2 = 0 := by
      rw [Nat.pow_mod]
      norm_num [zero_pow (by omega : k ≠ 0)]
    exact Nat.odd_iff.mpr (by omega)
  have hnm : n ≤ m := by
    have h1 : 2 ^ n ∣ 2 ^ m * (4 ^ m - 1) := (Dvd.intro _ rfl).trans hdvd
    have hcop : Nat.Coprime (2 ^ n) (4 ^ m - 1) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr (hodd m hm1))
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h1)
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have hmn : m ≤ n := by
    by_cases hm3 : m = 3
    · subst hm3
      by_contra hlt
      have hn2 : n = 2 := by omega
      subst hn2
      norm_num at hdvd
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have ha : (a : MulAut U) * a = 1 := by rw [← sq]; exact hA2.2 a a.2
    have hb := two_pow_mul_card_fixPts_le_of_sl2 (isPGroup_of_sq_eq_one hU2) (by omega) hm3 hF L e'
      (hKL (hAK a.2)) ha (fun h => ha1 (Subtype.ext h))
    have hfix : Nat.card ↥(CFSG.Quasithin.fixV A) ≤ Nat.card (fixPts (a : MulAut U)) :=
      Subgroup.card_le_of_le (fixV_le_fixPts a.2)
    have h3 : 2 ^ m * Nat.card (fixPts (a : MulAut U)) ≤ 2 ^ n * Nat.card (fixPts (a : MulAut U)) :=
      calc 2 ^ m * Nat.card (fixPts (a : MulAut U)) ≤ Nat.card U := hb
        _ ≤ Nat.card ↥A * Nat.card ↥(CFSG.Quasithin.fixV A) := hoff
        _ ≤ 2 ^ n * Nat.card (fixPts (a : MulAut U)) := Nat.mul_le_mul hAcard hfix
    have hpos : 0 < Nat.card (fixPts (a : MulAut U)) := Nat.card_pos
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h3 hpos)
  have hnm' : n = m := le_antisymm hnm hmn
  subst hnm'
  exact (Subgroup.eq_of_le_of_card_ge hKL (by rw [hcardL, hcardK])).symm

end CFSG.Quasithin.H13.Ch4.FFL2
