module

public import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def l05nK43a_twUnit {p : ℕ} [Fact p.Prime] {n : ℕ}
    (i j : Fin n) (c : ZMod p) (hc : c ≠ 0) : Fin n → (ZMod p)ˣ :=
  fun k => if k = i then Units.mk0 c⁻¹ (inv_ne_zero hc) else if k = j then Units.mk0 c hc else 1

private noncomputable def l05nK43a_Tw {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (hij : i ≠ j) (hc : c ≠ 0) : V ≃ₗ[ZMod p] V :=
  (b.equiv (b.unitsSMul (l05nK43a_twUnit i j c hc)) (Equiv.refl (Fin n))) *
    (b.equiv b (Equiv.swap i j))

private lemma l05nK43a_twUnit_self {p : ℕ} [Fact p.Prime] {n : ℕ}
    (i j : Fin n) (c : ZMod p) (hc : c ≠ 0) (hij : i ≠ j) :
    l05nK43a_twUnit i j c hc i = Units.mk0 c⁻¹ (inv_ne_zero hc) := by
  simp [l05nK43a_twUnit]

private lemma l05nK43a_twUnit_other {p : ℕ} [Fact p.Prime] {n : ℕ}
    (i j : Fin n) (c : ZMod p) (hc : c ≠ 0) (hij : i ≠ j) :
    l05nK43a_twUnit i j c hc j = Units.mk0 c hc := by
  simp only [l05nK43a_twUnit, if_neg (Ne.symm hij)]
  simp

private lemma l05nK43a_Tw_apply_i {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (hij : i ≠ j) (hc : c ≠ 0) :
    l05nK43a_Tw b i j c hij hc (b i) = c • b j := by
  simp only [l05nK43a_Tw, LinearEquiv.mul_apply, Module.Basis.equiv_apply, Equiv.swap_apply_left,
    Module.Basis.unitsSMul_apply, Equiv.refl_apply]
  rw [l05nK43a_twUnit_other i j c hc hij, Units.smul_def, Units.val_mk0]

private lemma l05nK43a_Tw_apply_j {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (hij : i ≠ j) (hc : c ≠ 0) :
    l05nK43a_Tw b i j c hij hc (b j) = c⁻¹ • b i := by
  simp only [l05nK43a_Tw, LinearEquiv.mul_apply, Module.Basis.equiv_apply, Equiv.swap_apply_right,
    Module.Basis.unitsSMul_apply, Equiv.refl_apply]
  rw [l05nK43a_twUnit_self i j c hc hij, Units.smul_def, Units.val_mk0]

private lemma l05nK43a_Tw_apply_other {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j k : Fin n) (c : ZMod p) (hij : i ≠ j) (hc : c ≠ 0)
    (hki : k ≠ i) (hkj : k ≠ j) :
    l05nK43a_Tw b i j c hij hc (b k) = b k := by
  simp only [l05nK43a_Tw, LinearEquiv.mul_apply, Module.Basis.equiv_apply,
    Equiv.swap_apply_of_ne_of_ne hki hkj, Module.Basis.unitsSMul_apply, Equiv.refl_apply]
  simp only [l05nK43a_twUnit, if_neg hki, if_neg hkj, one_smul]

private lemma l05nK43a_Tw_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (hij : i ≠ j) (hc : c ≠ 0) (k : Fin n) :
    l05nK43a_Tw b i j c hij hc (b k) =
      if k = i then c • b j else if k = j then c⁻¹ • b i else b k := by
  by_cases hki : k = i
  · subst hki
    rw [l05nK43a_Tw_apply_i]
    simp
  · by_cases hkj : k = j
    · subst hkj
      rw [l05nK43a_Tw_apply_j]
      simp [hki]
    · rw [l05nK43a_Tw_apply_other b i j k c hij hc hki hkj]
      simp [hki, hkj]

private lemma l05nK43a_permMap_symm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (σ : Equiv.Perm (Fin n)) :
    (ZS.permMap p b σ)⁻¹ = ZS.permMap p b σ.symm := by
  rw [ZS.permMap]
  exact Module.Basis.equiv_symm b b σ

private lemma l05nK43a_permMap_conj_Tw {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) (c : ZMod p) (hij : i ≠ j) (hc : c ≠ 0) :
    ZS.permMap p b σ * l05nK43a_Tw b i j c hij hc * (ZS.permMap p b σ)⁻¹ =
      l05nK43a_Tw b (σ i) (σ j) c (fun h => hij (σ.injective h)) hc := by
  rw [← LinearEquiv.toLinearMap_inj]
  apply Module.Basis.ext b
  intro k
  change ZS.permMap p b σ (l05nK43a_Tw b i j c hij hc ((ZS.permMap p b σ)⁻¹ (b k))) =
    l05nK43a_Tw b (σ i) (σ j) c (fun h => hij (σ.injective h)) hc (b k)
  rw [l05nK43a_permMap_symm]
  rw [show ZS.permMap p b σ.symm (b k) = b (σ.symm k) by
        simp [ZS.permMap, Module.Basis.equiv_apply]]
  by_cases h1 : k = σ i
  · subst h1
    rw [show σ.symm (σ i) = i by simp]
    rw [l05nK43a_Tw_apply_i b i j c hij hc, map_smul]
    rw [show ZS.permMap p b σ (b j) = b (σ j) by simp [ZS.permMap, Module.Basis.equiv_apply]]
    rw [l05nK43a_Tw_apply_i b (σ i) (σ j) c (fun h => hij (σ.injective h)) hc]
  · by_cases h2 : k = σ j
    · subst h2
      rw [show σ.symm (σ j) = j by simp]
      rw [l05nK43a_Tw_apply_j b i j c hij hc, map_smul]
      rw [show ZS.permMap p b σ (b i) = b (σ i) by simp [ZS.permMap, Module.Basis.equiv_apply]]
      rw [l05nK43a_Tw_apply_j b (σ i) (σ j) c (fun h => hij (σ.injective h)) hc]
    · have h3 : σ.symm k ≠ i := fun h => h1 (by have := congrArg σ h; simpa using this)
      have h4 : σ.symm k ≠ j := fun h => h2 (by have := congrArg σ h; simpa using this)
      rw [l05nK43a_Tw_apply_other b i j (σ.symm k) c hij hc h3 h4]
      rw [show ZS.permMap p b σ (b (σ.symm k)) = b k by
            simp [ZS.permMap, Module.Basis.equiv_apply]]
      rw [l05nK43a_Tw_apply_other b (σ i) (σ j) k c (fun h => hij (σ.injective h)) hc h1 h2]

private lemma l05nK43a_coord_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i k : Fin n) :
    b.coord i (b k) = if k = i then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]

private lemma l05nK43a_coord_apply_self {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    b.coord i (b i) = 1 := by
  rw [l05nK43a_coord_apply, if_pos rfl]

private lemma l05nK43a_coord_apply_ne {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i k : Fin n}
    (hki : k ≠ i) : b.coord i (b k) = 0 := by
  rw [l05nK43a_coord_apply, if_neg hki]

private lemma l05nK43a_two_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private lemma l05nK43a_three_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (3 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private lemma l05nK43a_four_ne_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (4 : ZMod p) ≠ 1 := by
  rw [← sub_ne_zero]
  have h41 : (4 : ZMod p) - 1 = 3 := by norm_num
  rw [h41]
  exact l05nK43a_three_ne_zero hp5

private noncomputable def l05nK43a_hcan {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) : V :=
  b i - c • b j

private noncomputable def l05nK43a_bcan {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) : Module.Dual (ZMod p) V :=
  b.coord i - c⁻¹ • b.coord j

private lemma l05nK43a_bcan_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (k : Fin n) :
    l05nK43a_bcan b i j c (b k) = (if k = i then 1 else 0) - c⁻¹ * (if k = j then 1 else 0) := by
  simp only [l05nK43a_bcan, LinearMap.sub_apply, LinearMap.smul_apply, l05nK43a_coord_apply,
    smul_eq_mul]

private lemma l05nK43a_bcan_self {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (hij : i ≠ j) :
    l05nK43a_bcan b i j c (b i) = 1 := by
  rw [l05nK43a_bcan_apply, if_pos rfl, if_neg hij]
  ring

private lemma l05nK43a_bcan_other {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) (hij : i ≠ j) :
    l05nK43a_bcan b i j c (b j) = -c⁻¹ := by
  rw [l05nK43a_bcan_apply, if_neg (Ne.symm hij), if_pos rfl]
  ring

private lemma l05nK43a_bcan_ne {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i j : Fin n) (c : ZMod p) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    l05nK43a_bcan b i j c (b k) = 0 := by
  rw [l05nK43a_bcan_apply, if_neg hki, if_neg hkj]
  ring

private inductive l05nK43a_ReflShape {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (s : V ≃ₗ[ZMod p] V) (αs : Module.Dual (ZMod p) V) (hs₀ : V) : Prop
  | sign (i : Fin n) (a : ZMod p) (ha : a ≠ 0)
      (hh : hs₀ = (2 * a⁻¹) • b i) (hα : αs = a • b.coord i) :
      l05nK43a_ReflShape b s αs hs₀
  | twist (i j : Fin n) (c a : ZMod p) (hij : i ≠ j) (hc : c ≠ 0) (ha : a ≠ 0)
      (hh : hs₀ = a⁻¹ • (b i - c • b j))
      (hα : αs = a • l05nK43a_bcan b i j c) :
      l05nK43a_ReflShape b s αs hs₀

private lemma l05nK43a_reflShape {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {r : V ≃ₗ[ZMod p] V} (hr : GGLinRefl r)
    {α : Module.Dual (ZMod p) V} {h : V}
    (hsl : ∀ w, r w = w - α w • h) (h2 : α h = 2)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p) (hc : ∀ i, c i ≠ 0)
    (hrb : ∀ i, r (b i) = c i • b (σ i)) :
    l05nK43a_ReflShape b r α h := by
  have hp2 : p ≠ 2 := by omega
  have h2nz : (2 : ZMod p) ≠ 0 := l05nK43a_two_ne_zero hp5
  have h0 : h ≠ 0 := by
    intro hh
    rw [hh, map_zero] at h2
    exact h2nz h2.symm
  have hsub : ∀ w, α w • h = w - r w := by
    intro w
    rw [hsl w]
    abel
  rcases ggRC_monomial_refl_shape hp2 b r hr σ c hc hrb with
    ⟨i, hσ, hci, hcj⟩ | ⟨i, j, hij, hσ, hcij, hck⟩
  · have hbi : r (b i) = -b i := by rw [hrb i, hσ]; simp [hci]
    have hbk : ∀ k, k ≠ i → r (b k) = b k := by
      intro k hk; rw [hrb k, hσ]; simp [hcj k hk]
    have hai' : α (b i) • h = b i + b i := by
      have := hsub (b i)
      rw [hbi, sub_neg_eq_add] at this
      exact this
    have hai : α (b i) • h = (2 : ZMod p) • b i := by
      rw [two_smul]; exact hai'
    set a := α (b i) with ha
    have ha0 : a ≠ 0 := by
      intro ha0
      have hzero : (2 : ZMod p) • b i = 0 := by rw [← hai, ha0, zero_smul]
      exact b.ne_zero i ((smul_eq_zero.mp hzero).resolve_left h2nz)
    have hh : h = (2 * a⁻¹) • b i := by
      have h1 : h = a⁻¹ • ((2 : ZMod p) • b i) := by
        rw [← hai, ← mul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [h1, smul_smul, mul_comm]
    have hα : α = a • b.coord i := by
      apply Module.Basis.ext b
      intro k
      by_cases hk : k = i
      · rw [hk]
        simpa [LinearMap.smul_apply, l05nK43a_coord_apply_self, smul_eq_mul] using ha.symm
      · have hk0 : α (b k) = 0 := by
          have := hsub (b k)
          rw [hbk k hk, sub_self] at this
          exact (smul_eq_zero.mp this).resolve_right h0
        rw [hk0, LinearMap.smul_apply, l05nK43a_coord_apply_ne b hk, smul_zero]
    exact l05nK43a_ReflShape.sign i a ha0 hh hα
  · set C := c i with hC
    have hC0 : C ≠ 0 := hc i
    have hCj : c j = C⁻¹ := by simpa [C] using eq_inv_of_mul_eq_one_right hcij
    have hbi : r (b i) = C • b j := by rw [hrb i, hσ]; simp [hC]
    have hbj : r (b j) = C⁻¹ • b i := by rw [hrb j, hσ, Equiv.swap_apply_right, hCj]
    have hbk : ∀ k, k ≠ i → k ≠ j → r (b k) = b k := by
      intro k hki hkj
      rw [hrb k, hσ, Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp [hck k hki hkj]
    have hai : α (b i) • h = b i - C • b j := by rw [hsub (b i), hbi]
    set a := α (b i) with ha
    have hcoord_i : a * (b.coord i h) = 1 := by
      have hc1 := congrArg (b.coord i) hai
      simp only [map_smul, smul_eq_mul, map_sub, l05nK43a_coord_apply_self,
        l05nK43a_coord_apply_ne b (i := i) (k := j) (Ne.symm hij), mul_zero, sub_zero] at hc1
      simpa using hc1
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcoord_i
      exact one_ne_zero hcoord_i.symm
    have hh : h = a⁻¹ • (b i - C • b j) := by
      rw [← hai, ← mul_smul, inv_mul_cancel₀ ha0, one_smul]
    have hcoord_i' : b.coord i h = a⁻¹ := by
      rw [hh]
      simp only [map_smul, smul_eq_mul, map_sub, l05nK43a_coord_apply_self,
        l05nK43a_coord_apply_ne b (i := i) (k := j) (Ne.symm hij), mul_zero, sub_zero, mul_one]
    have hbjdata : α (b j) • h = b j - C⁻¹ • b i := by rw [hsub (b j), hbj]
    have hbjd : α (b j) = -C⁻¹ * a := by
      have hc1 := congrArg (b.coord i) hbjdata
      simp only [map_smul, smul_eq_mul, map_sub, l05nK43a_coord_apply_self,
        l05nK43a_coord_apply_ne b (i := i) (k := j) (Ne.symm hij), mul_zero, sub_zero,
        mul_one, zero_sub] at hc1
      rw [hcoord_i'] at hc1
      calc α (b j) = α (b j) * (a⁻¹ * a) := by rw [inv_mul_cancel₀ ha0, mul_one]
        _ = (α (b j) * a⁻¹) * a := by ring
        _ = -C⁻¹ * a := by rw [hc1]
    have hbk0 : ∀ k, k ≠ i → k ≠ j → α (b k) = 0 := by
      intro k hki hkj
      have hdata : α (b k) • h = 0 := by
        rw [hsub (b k), hbk k hki hkj, sub_self]
      have hc1 := congrArg (b.coord i) hdata
      simp only [map_smul, smul_eq_mul, map_zero] at hc1
      rw [hcoord_i'] at hc1
      exact (mul_eq_zero.mp hc1).resolve_right (inv_ne_zero ha0)
    have hα : α = a • l05nK43a_bcan b i j C := by
      apply Module.Basis.ext b
      intro k
      by_cases hki : k = i
      · rw [hki]
        simpa [LinearMap.smul_apply, l05nK43a_bcan_self b i j C hij, smul_eq_mul] using ha.symm
      · by_cases hkj : k = j
        · rw [hkj]
          rw [LinearMap.smul_apply, l05nK43a_bcan_other b i j C hij, hbjd, smul_eq_mul]
          ring
        · rw [hbk0 k hki hkj, LinearMap.smul_apply,
            l05nK43a_bcan_ne b i j C hki hkj, smul_zero]
    exact l05nK43a_ReflShape.twist i j C a hij hC0 ha0 hh hα

private noncomputable def l05nK43a_delta {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (j k : Fin n) (ζ : ZMod p) (hjk : j ≠ k) (hζ : ζ ≠ 0) : V ≃ₗ[ZMod p] V :=
  l05nK43a_Tw b j k ζ hjk hζ * ZS.permMap p b (Equiv.swap j k)

private lemma l05nK43a_delta_apply_j {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (j k : Fin n) (ζ : ZMod p) (hjk : j ≠ k) (hζ : ζ ≠ 0) :
    l05nK43a_delta b j k ζ hjk hζ (b j) = ζ⁻¹ • b j := by
  rw [l05nK43a_delta, LinearEquiv.mul_apply, ZS.permMap, Module.Basis.equiv_apply,
    Equiv.swap_apply_left, l05nK43a_Tw_apply_j]

private lemma l05nK43a_delta_apply_k {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (j k : Fin n) (ζ : ZMod p) (hjk : j ≠ k) (hζ : ζ ≠ 0) :
    l05nK43a_delta b j k ζ hjk hζ (b k) = ζ • b k := by
  rw [l05nK43a_delta, LinearEquiv.mul_apply, ZS.permMap, Module.Basis.equiv_apply,
    Equiv.swap_apply_right, l05nK43a_Tw_apply_i]

private lemma l05nK43a_delta_apply_other {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (j k l : Fin n) (ζ : ZMod p) (hjk : j ≠ k) (hζ : ζ ≠ 0)
    (hlj : l ≠ j) (hlk : l ≠ k) :
    l05nK43a_delta b j k ζ hjk hζ (b l) = b l := by
  rw [l05nK43a_delta, LinearEquiv.mul_apply, ZS.permMap, Module.Basis.equiv_apply,
    Equiv.swap_apply_of_ne_of_ne hlj hlk, l05nK43a_Tw_apply_other b j k l ζ hjk hζ hlj hlk]

private lemma l05nK43a_delta_mul_inv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (j k : Fin n) (ζ : ZMod p) (hjk : j ≠ k) (hζ : ζ ≠ 0) :
    l05nK43a_delta b j k ζ hjk hζ * l05nK43a_delta b j k ζ⁻¹ hjk (inv_ne_zero hζ) = 1 := by
  rw [← LinearEquiv.toLinearMap_inj]
  apply Module.Basis.ext b
  intro l
  change l05nK43a_delta b j k ζ hjk hζ
      (l05nK43a_delta b j k ζ⁻¹ hjk (inv_ne_zero hζ) (b l)) = b l
  by_cases hlj : l = j
  · rw [hlj, l05nK43a_delta_apply_j, map_smul, l05nK43a_delta_apply_j, smul_smul,
      show ζ⁻¹⁻¹ * ζ⁻¹ = 1 by field_simp, one_smul]
  · by_cases hlk : l = k
    · rw [hlk, l05nK43a_delta_apply_k, map_smul, l05nK43a_delta_apply_k, smul_smul,
        show ζ⁻¹ * ζ = 1 by exact inv_mul_cancel₀ hζ, one_smul]
    · rw [l05nK43a_delta_apply_other b j k l ζ⁻¹ hjk (inv_ne_zero hζ) hlj hlk,
        l05nK43a_delta_apply_other b j k l ζ hjk hζ hlj hlk]

private lemma l05nK43a_eq_Tw_action {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {r : V ≃ₗ[ZMod p] V} {i j : Fin n} {C : ZMod p} (hij : i ≠ j) (hC : C ≠ 0)
    (hi : r (b i) = C • b j) (hj : r (b j) = C⁻¹ • b i)
    (ho : ∀ k, k ≠ i → k ≠ j → r (b k) = b k) :
    r = l05nK43a_Tw b i j C hij hC := by
  rw [← LinearEquiv.toLinearMap_inj]
  apply Module.Basis.ext b
  intro k
  change r (b k) = l05nK43a_Tw b i j C hij hC (b k)
  rw [l05nK43a_Tw_apply b i j C hij hC k]
  by_cases hki : k = i
  · rw [hki, hi, if_pos rfl]
  · by_cases hkj : k = j
    · rw [hkj, hj, if_neg (Ne.symm hij), if_pos rfl]
    · rw [ho k hki hkj, if_neg hki, if_neg hkj]

private def l05nK43a_UnitMono {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {a | ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)}
  one_mem' := ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun i => by simp⟩
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, ha⟩ ⟨σ', c', hc', ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_⟩
    · intro i
      rcases hc' i with h | h <;> rcases hc (σ' i) with h2 | h2 <;> simp [h, h2]
    · intro i
      rw [LinearEquiv.mul_apply, ha', map_smul, ha, mul_smul]
      rfl
  inv_mem' := by
    rintro a ⟨σ, c, hc, ha⟩
    refine ⟨σ⁻¹, fun i => c (σ⁻¹ i), fun i => hc (σ⁻¹ i), ?_⟩
    intro i
    have h2 : b (σ⁻¹ i) = c (σ⁻¹ i) • a⁻¹ (b i) := by
      have h1 : a (b (σ⁻¹ i)) = c (σ⁻¹ i) • b i := by rw [ha]; simp
      calc b (σ⁻¹ i) = a⁻¹ (a (b (σ⁻¹ i))) := by simp
        _ = a⁻¹ (c (σ⁻¹ i) • b i) := by rw [h1]
        _ = c (σ⁻¹ i) • a⁻¹ (b i) := by rw [map_smul]
    rw [h2, smul_smul]
    have hcc : c (σ⁻¹ i) * c (σ⁻¹ i) = 1 := by
      rcases hc (σ⁻¹ i) with h | h <;> rw [h] <;> norm_num
    rw [hcc, one_smul]

private lemma l05nK43a_bad_refl_exists {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hbad : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    ∃ r ∈ A, GGLinRefl r ∧ r ∉ l05nK43a_UnitMono b := by
  by_contra hcon
  push Not at hcon
  apply hbad
  intro a ha
  have hAle : A ≤ l05nK43a_UnitMono b := by
    rw [hgen, Subgroup.closure_le]
    intro x hx
    exact hcon x hx.1 hx.2
  rcases hAle ha with ⟨σ, c, hc, hact⟩
  exact ⟨σ, c, hc, hact⟩

private lemma l05nK43a_twist_in_A {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hperm : ∀ σ : Equiv.Perm (Fin n), ZS.permMap p b σ ∈ A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hbad : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (j k : Fin n) (hjk : j ≠ k) :
    ∃ ζ : ZMod p, ∃ hζ : ζ ≠ 0, ζ ≠ 1 ∧ ζ ≠ -1 ∧
      l05nK43a_Tw b j k ζ hjk hζ ∈ A := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨r, hrA, hrr, hrE⟩ := l05nK43a_bad_refl_exists b A hgen hbad
  obtain ⟨σ, c, hc, hrb⟩ := hmon r hrA
  rcases ggRC_monomial_refl_shape hp2 b r hrr σ c hc hrb with
    ⟨i, hσ, hci, hcj⟩ | ⟨i, i', hi', hσ, hcii', hck⟩
  · exfalso
    apply hrE
    refine ⟨σ, c, ?_, hrb⟩
    intro m
    by_cases hm : m = i
    · rw [hm, hci]; exact Or.inr rfl
    · rw [hcj m hm]; exact Or.inl rfl
  · set C := c i with hC
    have hC0 : C ≠ 0 := hc i
    have hCj : c i' = C⁻¹ := by
      have := eq_inv_of_mul_eq_one_right hcii'
      simpa [C] using this
    have hi : r (b i) = C • b i' := by rw [hrb i, hσ]; simp [hC]
    have hj : r (b i') = C⁻¹ • b i := by
      rw [hrb i', hσ, Equiv.swap_apply_right, hCj]
    have ho : ∀ m, m ≠ i → m ≠ i' → r (b m) = b m := by
      intro m hmi hmi'
      rw [hrb m, hσ, Equiv.swap_apply_of_ne_of_ne hmi hmi']
      simp [hck m hmi hmi']
    have hr_eq : r = l05nK43a_Tw b i i' C hi' hC0 :=
      l05nK43a_eq_Tw_action b hi' hC0 hi hj ho
    have hC1 : C ≠ 1 := by
      intro h1
      apply hrE
      refine ⟨σ, c, ?_, hrb⟩
      intro m
      by_cases hm : m = i
      · rw [hm, ← hC]; exact Or.inl h1
      · by_cases hm' : m = i'
        · rw [hm', hCj, h1]; norm_num
        · rw [hck m hm hm']; exact Or.inl rfl
    have hCm1 : C ≠ -1 := by
      intro h1
      apply hrE
      refine ⟨σ, c, ?_, hrb⟩
      intro m
      by_cases hm : m = i
      · rw [hm, ← hC]; exact Or.inr h1
      · by_cases hm' : m = i'
        · rw [hm', hCj, h1]; norm_num
        · rw [hck m hm hm']; exact Or.inl rfl
    have hTwA : l05nK43a_Tw b i i' C hi' hC0 ∈ A := by rw [← hr_eq]; exact hrA
    have hne : Equiv.swap i j i' ≠ j := by
      intro h
      have := (Equiv.swap_apply_eq_iff.mp h)
      rw [Equiv.swap_apply_right] at this
      exact hi' this.symm
    let τ : Equiv.Perm (Fin n) := Equiv.swap (Equiv.swap i j i') k * Equiv.swap i j
    have hτi : τ i = j := by
      simp only [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne (a := Equiv.swap i j i') (b := k) (x := j)
        (Ne.symm hne) hjk]
    have hτi' : τ i' = k := by
      simp only [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine ⟨C, hC0, hC1, hCm1, ?_⟩
    have hmem : ZS.permMap p b τ * l05nK43a_Tw b i i' C hi' hC0 * (ZS.permMap p b τ)⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (hperm τ) hTwA) (A.inv_mem (hperm τ))
    have hconj := l05nK43a_permMap_conj_Tw b τ i i' C hi' hC0
    rw [hconj] at hmem
    convert hmem using 1
    simp only [l05nK43a_Tw]
    rw [hτi, hτi']

private lemma l05nK43a_delta_inv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (j k : Fin n) (ζ : ZMod p) (hjk : j ≠ k) (hζ : ζ ≠ 0) :
    (l05nK43a_delta b j k ζ hjk hζ)⁻¹ =
      l05nK43a_delta b j k ζ⁻¹ hjk (inv_ne_zero hζ) :=
  inv_eq_of_mul_eq_one_right (l05nK43a_delta_mul_inv b j k ζ hjk hζ)

private lemma l05nK43a_construct_one_line {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {s s' : V ≃ₗ[ZMod p] V}
    {αs αs' : Module.Dual (ZMod p) V} {hs₀ hs₀' : V}
    (hsl : ∀ w, s w = w - αs w • hs₀) (hsl' : ∀ w, s' w = w - αs' w • hs₀')
    {i j k : Fin n} {c d a a' : ZMod p}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hh : hs₀ = a⁻¹ • (b i - c • b j)) (hα : αs = a • l05nK43a_bcan b i j c)
    (hh' : hs₀' = a'⁻¹ • (b j - d • b k)) (hα' : αs' = a' • l05nK43a_bcan b j k d)
    {ζ' : ZMod p} (hζ'0 : ζ' ≠ 0) (hζ'1 : ζ' ≠ 1) (hζ'm1 : ζ' ≠ -1)
    (hδA : l05nK43a_delta b j k ζ' hjk hζ'0 ∈ A) :
    ∃ δ ∈ A, ∃ ζ : ZMod p, ζ ≠ 0 ∧ ζ ≠ 1 ∧ ζ ≠ -1 ∧
      αs' (δ hs₀) * αs (δ⁻¹ hs₀') = 1 ∧ αs (δ hs₀) * αs (δ⁻¹ hs₀) = 2 + ζ + ζ⁻¹ ∧
      αs' hs₀ * αs (δ⁻¹ hs₀') * αs (δ hs₀) = 1 + ζ⁻¹ ∧
      δ * s * δ⁻¹ * s' ≠ s' * (δ * s * δ⁻¹) := by
  set δ := l05nK43a_delta b j k ζ' hjk hζ'0 with hδ
  have hδA' : δ ∈ A := by rw [hδ]; exact hδA
  have hinv1 : ζ'⁻¹ ≠ 1 := by
    intro h; apply hζ'1; rw [← inv_inv ζ', h, inv_one]
  have hinvm1 : ζ'⁻¹ ≠ -1 := by
    intro h; apply hζ'm1; rw [← inv_inv ζ', h]; norm_num
  have hδj : δ (b j) = ζ'⁻¹ • b j := by
    rw [hδ]; exact l05nK43a_delta_apply_j b j k ζ' hjk hζ'0
  have hδk : δ (b k) = ζ' • b k := by
    rw [hδ]; exact l05nK43a_delta_apply_k b j k ζ' hjk hζ'0
  have hδi : δ (b i) = b i := by
    rw [hδ]; exact l05nK43a_delta_apply_other b j k i ζ' hjk hζ'0 hij hik
  have hδinv : δ⁻¹ = l05nK43a_delta b j k ζ'⁻¹ hjk (inv_ne_zero hζ'0) := by
    rw [hδ]; exact l05nK43a_delta_inv b j k ζ' hjk hζ'0
  have hδinvj : δ⁻¹ (b j) = ζ' • b j := by
    rw [hδinv]; simpa [inv_inv] using l05nK43a_delta_apply_j b j k ζ'⁻¹ hjk (inv_ne_zero hζ'0)
  have hδinvk : δ⁻¹ (b k) = ζ'⁻¹ • b k := by
    rw [hδinv]; exact l05nK43a_delta_apply_k b j k ζ'⁻¹ hjk (inv_ne_zero hζ'0)
  have hδinvi : δ⁻¹ (b i) = b i := by
    rw [hδinv]; exact l05nK43a_delta_apply_other b j k i ζ'⁻¹ hjk (inv_ne_zero hζ'0) hij hik
  have hδhs : δ hs₀ = a⁻¹ • (b i - (c * ζ'⁻¹) • b j) := by
    rw [hh, map_smul, map_sub, map_smul, hδi, hδj, smul_smul]
  have hδinvhs : δ⁻¹ hs₀ = a⁻¹ • (b i - (c * ζ') • b j) := by
    rw [hh, map_smul, map_sub, map_smul, hδinvi, hδinvj, smul_smul]
  have hδhs' : δ hs₀' = a'⁻¹ • (ζ'⁻¹ • b j - (d * ζ') • b k) := by
    rw [hh', map_smul, map_sub, map_smul, hδj, hδk, smul_smul]
  have hδinvhs' : δ⁻¹ hs₀' = a'⁻¹ • (ζ' • b j - (d * ζ'⁻¹) • b k) := by
    rw [hh', map_smul, map_sub, map_smul, hδinvj, hδinvk, smul_smul]
  have hs_i : s (b i) = c • b j := by
    rw [hsl (b i), hα, hh, LinearMap.smul_apply, l05nK43a_bcan_self b i j c hij,
      smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ ha, one_smul]
    abel
  have hs_j : s (b j) = c⁻¹ • b i := by
    rw [hsl (b j), hα, hh, LinearMap.smul_apply, l05nK43a_bcan_other b i j c hij,
      smul_eq_mul, smul_smul]
    rw [show (a * -c⁻¹) * a⁻¹ = -c⁻¹ by field_simp]
    rw [show (-c⁻¹) • (b i - c • b j) = -(c⁻¹ • (b i - c • b j)) by exact neg_smul c⁻¹ _]
    rw [smul_sub, smul_smul, show c⁻¹ * c = 1 by field_simp, one_smul]
    abel
  have hs'_i : s' (b i) = b i := by
    rw [hsl' (b i), hα', hh', LinearMap.smul_apply,
      l05nK43a_bcan_ne b j k d hij hik, smul_eq_mul, mul_zero, zero_smul, sub_zero]
  have hs'_j : s' (b j) = d • b k := by
    rw [hsl' (b j), hα', hh', LinearMap.smul_apply, l05nK43a_bcan_self b j k d hjk,
      smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ ha', one_smul]
    abel
  have ht_i : (δ * s * δ⁻¹) (b i) = (c * ζ'⁻¹) • b j := by
    simp only [LinearEquiv.mul_apply, hδinvi, hs_i, map_smul, hδj, smul_smul]
  have g1 : αs' (δ hs₀) = -a' * a⁻¹ * c * ζ'⁻¹ := by
    simp only [hα', hδhs, LinearMap.smul_apply, map_smul, map_sub, map_smul,
      l05nK43a_bcan_ne b j k d hij hik, l05nK43a_bcan_self b j k d hjk, smul_eq_mul]
    field_simp
    ring
  have g2 : αs (δ⁻¹ hs₀') = -a * a'⁻¹ * c⁻¹ * ζ' := by
    simp only [hα, hδinvhs', LinearMap.smul_apply, map_smul, map_sub, map_smul,
      l05nK43a_bcan_ne b i j c (Ne.symm hik) (Ne.symm hjk),
      l05nK43a_bcan_other b i j c hij, smul_eq_mul]
    field_simp
    ring
  have g3 : αs (δ hs₀) = 1 + ζ'⁻¹ := by
    simp only [hα, hδhs, LinearMap.smul_apply, map_smul, map_sub, map_smul,
      l05nK43a_bcan_self b i j c hij, l05nK43a_bcan_other b i j c hij, smul_eq_mul]
    field_simp
    ring
  have g4 : αs (δ⁻¹ hs₀) = 1 + ζ' := by
    simp only [hα, hδinvhs, LinearMap.smul_apply, map_smul, map_sub, map_smul,
      l05nK43a_bcan_self b i j c hij, l05nK43a_bcan_other b i j c hij, smul_eq_mul]
    field_simp
    ring
  have f1 : αs' hs₀ = -a' * a⁻¹ * c := by
    simp only [hα', hh, LinearMap.smul_apply, map_smul, map_sub, map_smul,
      l05nK43a_bcan_ne b j k d hij hik, l05nK43a_bcan_self b j k d hjk, smul_eq_mul]
    field_simp
    ring
  refine ⟨δ, hδA', ζ'⁻¹, inv_ne_zero hζ'0, hinv1, hinvm1, ?_, ?_, ?_, ?_⟩
  · rw [g1, g2]
    field_simp
    try ring
  · rw [g3, g4]
    field_simp
    try ring
  · rw [f1, g2, g3]
    field_simp
    try ring
  · intro hcomm
    have hL : (δ * s * δ⁻¹ * s') (b i) = (c * ζ'⁻¹) • b j := by
      simp only [LinearEquiv.mul_apply, hs'_i, ht_i]
    have hR : (s' * (δ * s * δ⁻¹)) (b i) = (c * ζ'⁻¹ * d) • b k := by
      simp only [LinearEquiv.mul_apply, ht_i, map_smul, hs'_j, smul_smul]
    have hcomm_i := congrArg (fun f : V ≃ₗ[ZMod p] V => f (b i)) hcomm
    rw [hL, hR] at hcomm_i
    have hneL : c * ζ'⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hζ'0)
    have h1 := congrArg (b.coord j) hcomm_i
    simp only [map_smul, smul_eq_mul, l05nK43a_coord_apply_self, mul_one,
      l05nK43a_coord_apply_ne b (Ne.symm hjk), mul_zero] at h1
    exact hneL h1

private lemma l05nK43a_construct_same {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {s s' : V ≃ₗ[ZMod p] V}
    {αs αs' : Module.Dual (ZMod p) V} {hs₀ hs₀' : V}
    (hsl : ∀ w, s w = w - αs w • hs₀) (hsl' : ∀ w, s' w = w - αs' w • hs₀')
    {i j k : Fin n} {c d a a' : ZMod p}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hh : hs₀ = a⁻¹ • (b i - c • b j)) (hα : αs = a • l05nK43a_bcan b i j c)
    (hh' : hs₀' = a'⁻¹ • (b i - d • b j)) (hα' : αs' = a' • l05nK43a_bcan b i j d)
    (hζr : (d * c⁻¹) ^ 2 + d * c⁻¹ + 1 = 0)
    (hδA : ZS.permMap p b (Equiv.swap j k) ∈ A) :
    ∃ δ ∈ A, ∃ ζ : ZMod p, ζ ≠ 0 ∧ ζ ≠ 1 ∧ ζ ≠ -1 ∧
      αs' (δ hs₀) * αs (δ⁻¹ hs₀') = 1 ∧ αs (δ hs₀) * αs (δ⁻¹ hs₀) = 2 + ζ + ζ⁻¹ ∧
      αs' hs₀ * αs (δ⁻¹ hs₀') * αs (δ hs₀) = 1 + ζ⁻¹ ∧
      δ * s * δ⁻¹ * s' ≠ s' * (δ * s * δ⁻¹) := by
  set δ := ZS.permMap p b (Equiv.swap j k) with hδ
  have hδA' : δ ∈ A := by rw [hδ]; exact hδA
  have hδj : δ (b j) = b k := by
    rw [hδ, ZS.permMap, Module.Basis.equiv_apply, Equiv.swap_apply_left]
  have hδk : δ (b k) = b j := by
    rw [hδ, ZS.permMap, Module.Basis.equiv_apply, Equiv.swap_apply_right]
  have hδl : ∀ l, l ≠ j → l ≠ k → δ (b l) = b l := by
    intro l hlj hlk
    rw [hδ, ZS.permMap, Module.Basis.equiv_apply, Equiv.swap_apply_of_ne_of_ne hlj hlk]
  have hδi : δ (b i) = b i := hδl i hij hik
  have hδδ : δ * δ = 1 := by
    rw [← LinearEquiv.toLinearMap_inj]
    apply Module.Basis.ext b
    intro l
    change δ (δ (b l)) = b l
    by_cases hlj : l = j
    · rw [hlj, hδj, hδk]
    · by_cases hlk : l = k
      · rw [hlk, hδk, hδj]
      · rw [hδl l hlj hlk, hδl l hlj hlk]
  have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_left hδδ
  set ζ := d * c⁻¹ with hζ
  have hζr' : ζ ^ 2 + ζ + 1 = 0 := by rw [hζ]; exact hζr
  have hζ0 : ζ ≠ 0 := by
    rw [hζ]; exact mul_ne_zero hd (inv_ne_zero hc)
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by
      have := hζr'
      rw [h] at this
      ring_nf at this
      exact this
    exact l05nK43a_three_ne_zero hp5 h3
  have hζm1 : ζ ≠ -1 := by
    intro h
    have h1 : (1 : ZMod p) = 0 := by
      have := hζr'
      rw [h] at this
      ring_nf at this
      exact this
    exact one_ne_zero h1
  have hζsum : 2 + ζ + ζ⁻¹ = 1 := by
    have h := hζr'
    field_simp
    ring_nf at h ⊢
    linear_combination h
  have hδhs : δ hs₀ = a⁻¹ • (b i - c • b k) := by
    rw [hh, map_smul, map_sub, map_smul, hδi, hδj]
  have hδinvhs : δ⁻¹ hs₀ = a⁻¹ • (b i - c • b k) := by
    rw [hδinv, hδhs]
  have hδhs' : δ hs₀' = a'⁻¹ • (b i - d • b k) := by
    rw [hh', map_smul, map_sub, map_smul, hδi, hδj]
  have hδinvhs' : δ⁻¹ hs₀' = a'⁻¹ • (b i - d • b k) := by
    rw [hδinv, hδhs']
  have hs_i : s (b i) = c • b j := by
    rw [hsl (b i), hα, hh, LinearMap.smul_apply, l05nK43a_bcan_self b i j c hij,
      smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ ha, one_smul]
    abel
  have hs_k : s (b k) = b k := by
    rw [hsl (b k), hα, hh, LinearMap.smul_apply,
      l05nK43a_bcan_ne b i j c (Ne.symm hik) (Ne.symm hjk), smul_eq_mul, mul_zero, zero_smul,
      sub_zero]
  have hs'_i : s' (b i) = d • b j := by
    rw [hsl' (b i), hα', hh', LinearMap.smul_apply, l05nK43a_bcan_self b i j d hij,
      smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ ha', one_smul]
    abel
  have hs'_k : s' (b k) = b k := by
    rw [hsl' (b k), hα', hh', LinearMap.smul_apply,
      l05nK43a_bcan_ne b i j d (Ne.symm hik) (Ne.symm hjk), smul_eq_mul, mul_zero, zero_smul,
      sub_zero]
  have ht_j : (δ * s * δ⁻¹) (b j) = b j := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hδinv]
    rw [hδj, hs_k, hδk]
  have ht_i : (δ * s * δ⁻¹) (b i) = c • b k := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hδinv]
    rw [hδi, hs_i, map_smul, hδj]
  have g1 : αs' (δ hs₀) = a' * a⁻¹ := by
    simp only [hα', hδhs, LinearMap.smul_apply, map_smul, map_sub, smul_eq_mul,
      l05nK43a_bcan_self b i j d hij, l05nK43a_bcan_ne b i j d (Ne.symm hik) (Ne.symm hjk)]
    field_simp
    try ring
  have g2 : αs (δ⁻¹ hs₀') = a * a'⁻¹ := by
    simp only [hα, hδinvhs', LinearMap.smul_apply, map_smul, map_sub, smul_eq_mul,
      l05nK43a_bcan_self b i j c hij, l05nK43a_bcan_ne b i j c (Ne.symm hik) (Ne.symm hjk)]
    field_simp
    try ring
  have g3 : αs (δ hs₀) = 1 := by
    simp only [hα, hδhs, LinearMap.smul_apply, map_smul, map_sub, smul_eq_mul,
      l05nK43a_bcan_self b i j c hij, l05nK43a_bcan_ne b i j c (Ne.symm hik) (Ne.symm hjk)]
    field_simp
    try ring
  have g4 : αs (δ⁻¹ hs₀) = 1 := by
    simp only [hα, hδinvhs, LinearMap.smul_apply, map_smul, map_sub, smul_eq_mul,
      l05nK43a_bcan_self b i j c hij, l05nK43a_bcan_ne b i j c (Ne.symm hik) (Ne.symm hjk)]
    field_simp
    try ring
  have f1 : αs' hs₀ = a' * a⁻¹ * (1 + c * d⁻¹) := by
    simp only [hα', hh, LinearMap.smul_apply, map_smul, map_sub, smul_eq_mul,
      l05nK43a_bcan_self b i j d hij, l05nK43a_bcan_other b i j d hij]
    field_simp
    try ring
  refine ⟨δ, hδA', ζ, hζ0, hζ1, hζm1, ?_, ?_, ?_, ?_⟩
  · rw [g1, g2]
    field_simp
    try ring
  · rw [g3, g4, hζsum]
    simp
  · rw [f1, g2, g3, hζ]
    field_simp
    try ring
  · intro hcomm
    have hL : (δ * s * δ⁻¹ * s') (b i) = d • b j := by
      simp only [LinearEquiv.mul_apply, hs'_i, map_smul, ht_j]
    have hR : (s' * (δ * s * δ⁻¹)) (b i) = c • b k := by
      simp only [LinearEquiv.mul_apply, ht_i, map_smul, hs'_k]
    have hcomm_i := congrArg (fun f : V ≃ₗ[ZMod p] V => f (b i)) hcomm
    rw [hL, hR] at hcomm_i
    have h1 := congrArg (b.coord j) hcomm_i
    simp only [map_smul, smul_eq_mul, l05nK43a_coord_apply_self, mul_one,
      l05nK43a_coord_apply_ne b (Ne.symm hjk), mul_zero] at h1
    exact hd h1
private def l05nK43a_TriangleConclusion {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (A : Subgroup (V ≃ₗ[ZMod p] V)) (s s' : V ≃ₗ[ZMod p] V)
    (αs αs' : Module.Dual (ZMod p) V) (hs₀ hs₀' : V) : Prop :=
  ∃ δ ∈ A, ∃ ζ : ZMod p, ζ ≠ 0 ∧ ζ ≠ 1 ∧ ζ ≠ -1 ∧
    αs' (δ hs₀) * αs (δ⁻¹ hs₀') = 1 ∧ αs (δ hs₀) * αs (δ⁻¹ hs₀) = 2 + ζ + ζ⁻¹ ∧
    αs' hs₀ * αs (δ⁻¹ hs₀') * αs (δ hs₀) = 1 + ζ⁻¹ ∧
    δ * s * δ⁻¹ * s' ≠ s' * (δ * s * δ⁻¹)

private lemma l05nK43a_third_line {n : ℕ} (hn : 3 ≤ n)
    (i j : Fin n) (hij : i ≠ j) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  have hlt : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
      calc ({i, j} : Finset (Fin n)).card ≤ ({j} : Finset (Fin n)).card + 1 :=
            Finset.card_insert_le i {j}
        _ ≤ 2 := by simp
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2⟩

private lemma l05nK43a_two_ne_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (2 : ZMod p) ≠ 1 := by
  have h21 : (2 : ZMod p) - 1 = 1 := by norm_num
  intro h
  exact one_ne_zero (by rw [← h21, sub_eq_zero.mpr h])

private lemma l05nK43a_bcan_swap {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j : Fin n} (hij : i ≠ j) (d : ZMod p) (hd : d ≠ 0) :
    l05nK43a_bcan b j i d⁻¹ = -d • l05nK43a_bcan b i j d := by
  apply Module.Basis.ext b
  intro k
  rw [l05nK43a_bcan, l05nK43a_bcan]
  simp only [LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.sub_apply,
    l05nK43a_coord_apply, smul_eq_mul]
  by_cases hki : k = i
  · rw [hki]; simp [hij]
  · by_cases hkj : k = j
    · rw [hkj]; simp [Ne.symm hij, hij, hki, mul_inv_cancel₀ hd]
    · simp [hki, hkj]

private lemma l05nK43a_twist_swap_data {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {αs : Module.Dual (ZMod p) V} {hs₀ : V}
    {i j : Fin n} {d a : ZMod p} (hij : i ≠ j) (hd : d ≠ 0) (ha : a ≠ 0)
    (hh : hs₀ = a⁻¹ • l05nK43a_hcan b i j d)
    (hα : αs = a • l05nK43a_bcan b i j d) :
    ∃ a' : ZMod p, a' ≠ 0 ∧ hs₀ = a'⁻¹ • l05nK43a_hcan b j i d⁻¹ ∧
      αs = a' • l05nK43a_bcan b j i d⁻¹ := by
  refine ⟨-a * d⁻¹, mul_ne_zero (neg_ne_zero.mpr ha) (inv_ne_zero hd), ?_, ?_⟩
  · rw [hh, l05nK43a_hcan, l05nK43a_hcan]
    rw [show (-a * d⁻¹)⁻¹ = -a⁻¹ * d by rw [mul_inv_rev, inv_inv, inv_neg]; ring]
    simp only [smul_sub, smul_smul]
    rw [show (-a⁻¹ * d) * d⁻¹ = -a⁻¹ by field_simp]
    module
  · rw [hα, l05nK43a_bcan_swap b hij d hd]
    rw [smul_comm, smul_smul]
    congr 1
    field_simp
    try ring

private lemma l05nK43a_twist_twist_prod {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j p' q : Fin n} {c d a a' : ZMod p} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (a • l05nK43a_bcan b i j c) (a'⁻¹ • (b p' - d • b q)) *
        (a' • l05nK43a_bcan b p' q d) (a⁻¹ • (b i - c • b j)) =
      l05nK43a_bcan b i j c (b p' - d • b q) *
        l05nK43a_bcan b p' q d (b i - c • b j) := by
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  field_simp
  try ring

private lemma l05nK43a_use_one_line {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hperm : ∀ σ : Equiv.Perm (Fin n), ZS.permMap p b σ ∈ A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hbad : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    {s s' : V ≃ₗ[ZMod p] V} {αs αs' : Module.Dual (ZMod p) V} {hs₀ hs₀' : V}
    (hsl : ∀ w, s w = w - αs w • hs₀) (hsl' : ∀ w, s' w = w - αs' w • hs₀')
    {α β γ : Fin n} {c d a a' : ZMod p}
    (hαβ : α ≠ β) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hh : hs₀ = a⁻¹ • l05nK43a_hcan b α β c) (hαα : αs = a • l05nK43a_bcan b α β c)
    (hh' : hs₀' = a'⁻¹ • l05nK43a_hcan b β γ d)
    (hαα' : αs' = a' • l05nK43a_bcan b β γ d) :
    l05nK43a_TriangleConclusion A s s' αs αs' hs₀ hs₀' := by
  obtain ⟨ζ', hζ'0, hζ'1, hζ'm1, hTw⟩ :=
    l05nK43a_twist_in_A hp5 b A hperm hgen hmon hbad β γ hβγ
  exact l05nK43a_construct_one_line hp5 b hsl hsl' hαβ hβγ hαγ hc hd ha ha'
    hh hαα hh' hαα' hζ'0 hζ'1 hζ'm1 (A.mul_mem hTw (hperm (Equiv.swap β γ)))

private lemma l05nK43a_use_same {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hperm : ∀ σ : Equiv.Perm (Fin n), ZS.permMap p b σ ∈ A)
    {s s' : V ≃ₗ[ZMod p] V} {αs αs' : Module.Dual (ZMod p) V} {hs₀ hs₀' : V}
    (hsl : ∀ w, s w = w - αs w • hs₀) (hsl' : ∀ w, s' w = w - αs' w • hs₀')
    {i j k : Fin n} {c d a a' : ZMod p}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hh : hs₀ = a⁻¹ • l05nK43a_hcan b i j c) (hαα : αs = a • l05nK43a_bcan b i j c)
    (hh' : hs₀' = a'⁻¹ • l05nK43a_hcan b i j d)
    (hαα' : αs' = a' • l05nK43a_bcan b i j d)
    (hζr : (d * c⁻¹) ^ 2 + d * c⁻¹ + 1 = 0) :
    l05nK43a_TriangleConclusion A s s' αs αs' hs₀ hs₀' :=
  l05nK43a_construct_same hp5 b hsl hsl' hij hik hjk hc hd ha ha' hh hαα hh' hαα' hζr
    (hperm (Equiv.swap j k))

private lemma l05nK43a_same_zeta {p : ℕ} [Fact p.Prime] (c d : ZMod p) (hc : c ≠ 0)
    (hd : d ≠ 0) (h : (1 + d * c⁻¹) * (1 + c * d⁻¹) = 1) :
    (d * c⁻¹) ^ 2 + d * c⁻¹ + 1 = 0 := by
  set x := d * c⁻¹ with hx
  have hcd : c * d⁻¹ = x⁻¹ := by rw [hx]; field_simp
  have hx0 : x ≠ 0 := by rw [hx]; exact mul_ne_zero hd (inv_ne_zero hc)
  have hx' : x + x⁻¹ + 1 = 0 := by
    have key : (1 + x) * (1 + x⁻¹) = 1 + (x + x⁻¹ + 1) := by
      field_simp
      ring
    rw [hcd] at h
    rw [key] at h
    have h' : 1 + (x + x⁻¹ + 1) = 1 + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h'
  have h3 : x * (x + x⁻¹ + 1) = 0 := by rw [hx', mul_zero]
  field_simp at h3
  linear_combination h3

private lemma l05nK43a_classify {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 3 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hperm : ∀ σ : Equiv.Perm (Fin n), ZS.permMap p b σ ∈ A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hbad : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    {s s' : V ≃ₗ[ZMod p] V} {αs αs' : Module.Dual (ZMod p) V} {hs₀ hs₀' : V}
    (hsl : ∀ w, s w = w - αs w • hs₀) (hsl' : ∀ w, s' w = w - αs' w • hs₀')
    (hsδ : l05nK43a_ReflShape b s αs hs₀) (hsδ' : l05nK43a_ReflShape b s' αs' hs₀')
    (hpair : αs hs₀' * αs' hs₀ = 1) :
    l05nK43a_TriangleConclusion A s s' αs αs' hs₀ hs₀' := by
  rcases hsδ with ⟨i, a, ha, hh, hα⟩ | ⟨i, j, c, a, hij, hc, ha, hh, hα⟩
  · rcases hsδ' with ⟨k, a', ha', hh', hα'⟩ | ⟨p', q, d, a', hp', hd, ha', hh', hα'⟩
    · exfalso
      rw [hα, hα', hh, hh'] at hpair
      simp only [LinearMap.smul_apply, map_smul, l05nK43a_coord_apply, smul_eq_mul] at hpair
      by_cases hki : k = i
      · rw [if_pos hki] at hpair
        rw [if_pos hki.symm] at hpair
        simp only [mul_one] at hpair
        have h4 : (4 : ZMod p) = 1 := by rw [← hpair] <;> field_simp <;> try ring
        exact l05nK43a_four_ne_one hp5 h4
      · rw [if_neg hki] at hpair
        rw [if_neg (fun h => hki h.symm)] at hpair
        simp only [mul_zero] at hpair
        exact one_ne_zero hpair.symm
    · exfalso
      rw [hα, hα', hh, hh'] at hpair
      simp only [LinearMap.smul_apply, map_smul, map_sub, l05nK43a_coord_apply,
        l05nK43a_bcan_apply, smul_eq_mul] at hpair
      by_cases hpi : p' = i
      · have hqi : q ≠ i := fun h => hp' (by rw [hpi, h])
        rw [if_pos hpi] at hpair
        rw [if_neg hqi] at hpair
        rw [if_pos hpi.symm] at hpair
        rw [if_neg (fun h => hqi h.symm)] at hpair
        simp only [mul_zero, sub_zero, mul_one] at hpair
        have h2 : (2 : ZMod p) = 1 := by rw [← hpair] <;> field_simp <;> try ring
        exact l05nK43a_two_ne_one hp5 h2
      · by_cases hqi : q = i
        · rw [if_neg hpi] at hpair
          rw [if_pos hqi] at hpair
          rw [if_neg (fun h => hpi h.symm)] at hpair
          rw [if_pos hqi.symm] at hpair
          simp only [mul_zero, sub_zero, mul_one] at hpair
          have h2 : (2 : ZMod p) = 1 := by rw [← hpair] <;> field_simp <;> try ring
          exact l05nK43a_two_ne_one hp5 h2
        · rw [if_neg hpi] at hpair
          rw [if_neg hqi] at hpair
          rw [if_neg (fun h => hpi h.symm)] at hpair
          rw [if_neg (fun h => hqi h.symm)] at hpair
          simp only [mul_zero, sub_zero, mul_one] at hpair
          exact one_ne_zero hpair.symm
  · rcases hsδ' with ⟨k, a', ha', hh', hα'⟩ | ⟨p', q, d, a', hp', hd, ha', hh', hα'⟩
    · exfalso
      rw [hα, hα', hh, hh'] at hpair
      simp only [LinearMap.smul_apply, map_smul, map_sub, l05nK43a_coord_apply,
        l05nK43a_bcan_apply, smul_eq_mul] at hpair
      by_cases hki : k = i
      · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
        rw [if_pos hki] at hpair
        rw [if_neg hkj] at hpair
        rw [if_pos hki.symm] at hpair
        rw [if_neg (fun h => (Ne.symm hij) (h.trans hki))] at hpair
        simp only [mul_zero, sub_zero, mul_one] at hpair
        have h2 : (2 : ZMod p) = 1 := by rw [← hpair] <;> field_simp <;> try ring
        exact l05nK43a_two_ne_one hp5 h2
      · by_cases hkj : k = j
        · rw [if_neg hki] at hpair
          rw [if_pos hkj] at hpair
          rw [if_neg (fun h => hij (h.trans hkj))] at hpair
          rw [if_pos hkj.symm] at hpair
          simp only [mul_zero, sub_zero, mul_one] at hpair
          have h2 : (2 : ZMod p) = 1 := by rw [← hpair] <;> field_simp <;> try ring
          exact l05nK43a_two_ne_one hp5 h2
        · rw [if_neg hki] at hpair
          rw [if_neg hkj] at hpair
          rw [if_neg (fun h => hki h.symm)] at hpair
          rw [if_neg (fun h => hkj h.symm)] at hpair
          simp only [mul_zero, sub_zero, mul_one] at hpair
          exact one_ne_zero hpair.symm
    · by_cases hpi : p' = i
      · by_cases hqj : q = j
        ·
          rw [hpi, hqj] at hh' hα'
          rw [hα, hα', hh, hh'] at hpair
          rw [l05nK43a_twist_twist_prod b ha ha'] at hpair
          simp only [map_sub, map_smul, l05nK43a_bcan_apply, smul_eq_mul] at hpair
          simp only [hij, Ne.symm hij, if_true, if_false] at hpair
          obtain ⟨k3, hk3i, hk3j⟩ := l05nK43a_third_line hn i j hij
          have hζr : (d * c⁻¹) ^ 2 + d * c⁻¹ + 1 = 0 := by
            apply l05nK43a_same_zeta c d hc hd
            have hh := hpair
            field_simp at hh ⊢
            ring_nf at hh ⊢
            exact hh
          exact l05nK43a_use_same hp5 b A hperm hsl hsl' hij (Ne.symm hk3i) (Ne.symm hk3j)
            hc hd ha ha' hh hα hh' hα' hζr
        ·
          have hqi : q ≠ i := fun h => hp' (by rw [hpi, h])
          have hqj' : q ≠ j := hqj
          obtain ⟨a3, ha3, hh3, hα3⟩ := l05nK43a_twist_swap_data b hij hc ha hh hα
          rw [hpi] at hh' hα'
          exact l05nK43a_use_one_line hp5 b A hperm hgen hmon hbad hsl hsl'
            (α := j) (β := i) (γ := q) (Ne.symm hij) (Ne.symm hqi) (Ne.symm hqj')
            (inv_ne_zero hc) hd ha3 ha' hh3 hα3 hh' hα'
      · by_cases hpj : p' = j
        · by_cases hqi : q = i
          ·
            obtain ⟨a'', ha'', hh'', hα''⟩ := l05nK43a_twist_swap_data b hp' hd ha' hh' hα'
            rw [hqi, hpj] at hh'' hα''
            simp only [l05nK43a_hcan] at hh''
            rw [hα, hα'', hh, hh''] at hpair
            rw [l05nK43a_twist_twist_prod b ha ha''] at hpair
            simp only [map_sub, map_smul, l05nK43a_bcan_apply, smul_eq_mul] at hpair
            simp only [hij, Ne.symm hij, if_true, if_false] at hpair
            obtain ⟨k3, hk3i, hk3j⟩ := l05nK43a_third_line hn i j hij
            have hζr : (d⁻¹ * c⁻¹) ^ 2 + d⁻¹ * c⁻¹ + 1 = 0 := by
              apply l05nK43a_same_zeta c d⁻¹ hc (inv_ne_zero hd)
              have hh := hpair
              field_simp at hh ⊢
              ring_nf at hh ⊢
              exact hh
            exact l05nK43a_use_same hp5 b A hperm hsl hsl' hij (Ne.symm hk3i) (Ne.symm hk3j)
              hc (inv_ne_zero hd) ha ha'' hh hα hh'' hα'' hζr
          ·
            have hqj' : q ≠ j := fun h => hp' (by rw [hpj, h])
            rw [hpj] at hh' hα'
            exact l05nK43a_use_one_line hp5 b A hperm hgen hmon hbad hsl hsl'
              (α := i) (β := j) (γ := q) hij (Ne.symm hqj') (Ne.symm hqi) hc hd ha ha' hh hα hh' hα'
        · by_cases hqi : q = i
          ·
            obtain ⟨a'', ha'', hh'', hα''⟩ := l05nK43a_twist_swap_data b hp' hd ha' hh' hα'
            obtain ⟨a3, ha3, hh3, hα3⟩ := l05nK43a_twist_swap_data b hij hc ha hh hα
            rw [hqi] at hh'' hα''
            exact l05nK43a_use_one_line hp5 b A hperm hgen hmon hbad hsl hsl'
              (α := j) (β := i) (γ := p') (Ne.symm hij) (Ne.symm hpi) (Ne.symm hpj)
              (inv_ne_zero hc) (inv_ne_zero hd) ha3 ha'' hh3 hα3 hh'' hα''
          · by_cases hqj : q = j
            ·
              obtain ⟨a'', ha'', hh'', hα''⟩ := l05nK43a_twist_swap_data b hp' hd ha' hh' hα'
              rw [hqj] at hh'' hα''
              exact l05nK43a_use_one_line hp5 b A hperm hgen hmon hbad hsl hsl'
                (α := i) (β := j) (γ := p') hij (Ne.symm hpj) (Ne.symm hpi)
                hc (inv_ne_zero hd) ha ha'' hh hα hh'' hα''
            ·
              exfalso
              rw [hα, hα', hh, hh'] at hpair
              rw [l05nK43a_twist_twist_prod b ha ha'] at hpair
              simp only [map_sub, map_smul, l05nK43a_bcan_apply, smul_eq_mul] at hpair
              have hpi' : i ≠ p' := fun h => hpi h.symm
              have hpj' : j ≠ p' := fun h => hpj h.symm
              have hqi' : i ≠ q := fun h => hqi h.symm
              have hqj' : j ≠ q := fun h => hqj h.symm
              simp only [hpi, hpj, hqi, hqj, hpi', hpj', hqi', hqj', if_true, if_false,
                mul_zero, sub_zero] at hpair
              exact one_ne_zero hpair.symm
theorem ggRC_twisted_triangle {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 3 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hperm : ∀ σ : Equiv.Perm (Fin n), ZS.permMap p b σ ∈ A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hbad : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    {s s' : V ≃ₗ[ZMod p] V} (hs : s ∈ A) (hs' : s' ∈ A) (hsr : GGLinRefl s) (hsr' : GGLinRefl s')
    {hs₀ hs₀' : V} {αs αs' : Module.Dual (ZMod p) V}
    (hsl : ∀ w, s w = w - αs w • hs₀) (hsl' : ∀ w, s' w = w - αs' w • hs₀')
    (h2 : αs hs₀ = 2) (h2' : αs' hs₀' = 2) (hpair : αs hs₀' * αs' hs₀ = 1)
    (hind : LinearIndependent (ZMod p) ![hs₀, hs₀']) :
    ∃ δ ∈ A, ∃ ζ : ZMod p, ζ ≠ 0 ∧ ζ ≠ 1 ∧ ζ ≠ -1 ∧
      αs' (δ hs₀) * αs (δ⁻¹ hs₀') = 1 ∧ αs (δ hs₀) * αs (δ⁻¹ hs₀) = 2 + ζ + ζ⁻¹ ∧
      αs' hs₀ * αs (δ⁻¹ hs₀') * αs (δ hs₀) = 1 + ζ⁻¹ ∧
      δ * s * δ⁻¹ * s' ≠ s' * (δ * s * δ⁻¹) := by
  obtain ⟨σs, cs, hcs, hsr_b⟩ := hmon s hs
  obtain ⟨σs', cs', hcs', hsr_b'⟩ := hmon s' hs'
  exact l05nK43a_classify hp5 hn b A hperm hgen hmon hbad hsl hsl'
    (l05nK43a_reflShape hp5 b hsr hsl h2 σs cs hcs hsr_b)
    (l05nK43a_reflShape hp5 b hsr' hsl' h2' σs' cs' hcs' hsr_b') hpair

end CFSG.StandardType

end

