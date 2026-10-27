module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Fld

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

section Field

variable {F : Type} [Field F] [Finite F]

theorem sigma_fixed_of_mul_self (hF : 2 ∣ Nat.card F) (σ : F ≃+* F) {x y : F}
    (hx : σ x = x) (hy : y * y = x) : σ y = y := by
  have : CharP F 2 := charP_two_of_two_dvd hF
  have h1 : σ y * σ y = y * y := by rw [← map_mul, hy, hx]
  have h2 : (σ y - y) * (σ y - y) = 0 := by
    linear_combination h1 + (y * y - σ y * y) * (CharTwo.two_eq_zero : (2 : F) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem orbit_fixed (hF : 2 ∣ Nat.card F) (σ : F ≃+* F) (Q : F → F → Prop)
    (hD : ∀ μ a b, σ μ = μ → μ ≠ 0 → Q a b → Q (μ * a) (μ⁻¹ * b))
    (hC : ∀ a b, Q a b → Q b (a + b)) {a b : F} (ha : σ a = a) (hb : σ b = b)
    (hab : ¬ (a = 0 ∧ b = 0)) (hQ : Q a b) {a' b' : F} (ha' : σ a' = a') (hb' : σ b' = b')
    (hab' : ¬ (a' = 0 ∧ b' = 0)) : Q a' b' := by
  have : CharP F 2 := charP_two_of_two_dvd hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hC2 : ∀ a b, Q a b → Q (a + b) a := by
    intro a b h
    have h1 := hC _ _ (hC a b h)
    have e : b + (a + b) = a := by linear_combination b * h2
    rwa [e] at h1
  have hto1 : ∀ c, σ c = c → c ≠ 0 → Q c 0 → Q 1 0 := by
    intro c hc hc0 h
    have h1 := hD c⁻¹ c 0 (by rw [map_inv₀, hc]) (inv_ne_zero hc0) h
    rwa [inv_mul_cancel₀ hc0, mul_zero] at h1
  have hone : Q 1 0 := by
    by_cases hb0 : b = 0
    · subst hb0
      have ha0 : a ≠ 0 := fun h0 => hab ⟨h0, rfl⟩
      exact hto1 a ha ha0 hQ
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := hC2 0 b hQ
      rw [zero_add] at h1
      exact hto1 b hb hb0 h1
    obtain ⟨ν, hν⟩ := exists_mul_self_eq hF (b / a)
    have hσν : σ ν = ν := sigma_fixed_of_mul_self hF σ (by rw [map_div₀, ha, hb]) hν
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hν
      exact div_ne_zero hb0 ha0 hν.symm
    have h1 := hD ν a b hσν hν0 hQ
    have e : ν⁻¹ * b = ν * a := by
      have : b = ν * ν * a := by rw [hν, div_mul_cancel₀ b ha0]
      rw [this, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hν0, one_mul]
    rw [e] at h1
    have hy0 : ν * a ≠ 0 := mul_ne_zero hν0 ha0
    have h3 := hC2 _ _ h1
    have e2 : ν * a + ν * a = 0 := by linear_combination (ν * a) * h2
    rw [e2] at h3
    have h4 := hC2 _ _ h3
    rw [zero_add] at h4
    exact hto1 (ν * a) (by rw [map_mul, hσν, ha]) hy0 h4
  have hfrom1 : ∀ c, σ c = c → c ≠ 0 → Q c 0 := by
    intro c hc hc0
    have h1 := hD c 1 0 hc hc0 hone
    rwa [mul_one, mul_zero] at h1
  by_cases hb0' : b' = 0
  · subst hb0'
    exact hfrom1 a' ha' fun h0 => hab' ⟨h0, rfl⟩
  by_cases ha0' : a' = 0
  · subst ha0'
    have h1 := hC _ _ (hfrom1 b' hb' hb0')
    rwa [add_zero] at h1
  obtain ⟨y, hy⟩ := exists_mul_self_eq hF (a' * b')
  have hσy : σ y = y := sigma_fixed_of_mul_self hF σ (by rw [map_mul, ha', hb']) hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hy
    exact mul_ne_zero ha0' hb0' hy.symm
  have h1 := hC _ _ (hfrom1 y hσy hy0)
  rw [add_zero] at h1
  have h2' := hC _ _ h1
  rw [zero_add] at h2'
  have h3 := hD (a' / y) y y (by rw [map_div₀, ha', hσy]) (div_ne_zero ha0' hy0) h2'
  have e1 : a' / y * y = a' := div_mul_cancel₀ a' hy0
  have e2 : (a' / y)⁻¹ * y = b' := by
    rw [inv_div, div_mul_eq_mul_div, hy, mul_comm a' b', mul_div_assoc, div_self ha0', mul_one]
  rwa [e1, e2] at h3

omit [Finite F] in
theorem exists_sl2_basis {u₁ u₂ x y : Fin 2 → F} (hd : det2 u₁ u₂ ≠ 0)
    (hxy : det2 x y = det2 u₁ u₂) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) F,
      (B : Matrix (Fin 2) (Fin 2) F).mulVec u₁ = x ∧
        (B : Matrix (Fin 2) (Fin 2) F).mulVec u₂ = y := by
  set d := det2 u₁ u₂ with hdd
  have hd' : d = u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0 := rfl
  have hxy' : x 0 * y 1 - x 1 * y 0 = d := hxy
  let P : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![u₁ 0, u₂ 0 / d; u₁ 1, u₂ 1 / d], by
    rw [Matrix.det_fin_two_of]
    have : u₁ 0 * (u₂ 1 / d) - u₂ 0 / d * u₁ 1 = (u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0) / d := by ring
    rw [this, ← hd']
    exact div_self hd⟩
  let X : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![x 0, y 0 / d; x 1, y 1 / d], by
    rw [Matrix.det_fin_two_of]
    have : x 0 * (y 1 / d) - y 0 / d * x 1 = (x 0 * y 1 - x 1 * y 0) / d := by ring
    rw [this, hxy']
    exact div_self hd⟩
  have hP1 : (P : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = u₁ := by
    funext i
    fin_cases i <;> simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hP2 : (P : Matrix (Fin 2) (Fin 2) F).mulVec ![0, d] = u₂ := by
    funext i
    fin_cases i <;> simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_mul_cancel₀ _ hd]
  have hX1 : (X : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = x := by
    funext i
    fin_cases i <;> simp [X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hX2 : (X : Matrix (Fin 2) (Fin 2) F).mulVec ![0, d] = y := by
    funext i
    fin_cases i <;> simp [X, Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_mul_cancel₀ _ hd]
  refine ⟨X * P⁻¹, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hP1, inv_mulVec_mulVec, hX1]
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hP2, inv_mulVec_mulVec, hX2]

omit [Finite F] in
theorem sl2_pow_succ_mulVec (B : Matrix.SpecialLinearGroup (Fin 2) F) (k : ℕ) (w : Fin 2 → F) :
    ((B ^ (k + 1) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w =
      (B : Matrix (Fin 2) (Fin 2) F).mulVec
        (((B ^ k : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w) := by
  rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

end Field

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem mem_addSub_fix_iff (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (y : Fin 2 → h.data.K) :
    y ∈ h.data.addSub (V ⊓ Subgroup.centralizer ({t} : Set G)) ↔
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ y = y := by
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  set v : ↥V := h.data.E.symm (Multiplicative.ofAdd y) with hv
  have hEv : Multiplicative.toAdd (h.data.E v) = y := by simp [hv]
  rw [← hEv, h.data.toAdd_mem_addSub, h.data.conj_apply]
  constructor
  · intro hvU
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp hvU.2 t rfl
    show t * (v : G) * t⁻¹ = v
    rw [this]
    group
  · intro hfix
    refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [Set.mem_singleton_iff.mp hx]
    have h2 := congrArg Subtype.val (h.data.E.injective (Multiplicative.toAdd.injective hfix))
    rw [conjAct_apply_coe] at h2
    have h3 : t * (v : G) * t⁻¹ = v := h2
    calc t * (v : G) = (t * (v : G) * t⁻¹) * t := by group
      _ = v * t := by rw [h3]

theorem conj_mem_addSub (h : Hyp611Nat G T M L V n) (x : Subgroup.normalizer (V : Set G))
    {W : Subgroup G} (hxW : (x : G) ∈ Subgroup.normalizer (W : Set G))
    {y : Fin 2 → h.data.K} (hy : y ∈ h.data.addSub W) : h.data.conj x y ∈ h.data.addSub W := by
  set v : ↥V := h.data.E.symm (Multiplicative.ofAdd y) with hv
  have hEv : Multiplicative.toAdd (h.data.E v) = y := by simp [hv]
  rw [← hEv] at hy ⊢
  rw [h.data.toAdd_mem_addSub] at hy
  rw [h.data.conj_apply, h.data.toAdd_mem_addSub, conjAct_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp hxW _).mp hy

theorem mem_normalizer_fix_of_comm (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (x : Subgroup.normalizer (V : Set G))
    (hx : ∀ w, h.data.conj x (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ w) =
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ (h.data.conj x w)) :
    (x : G) ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G) := by
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  have hid : ∀ w, h.data.conj 1 w = w := fun w =>
    h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _) w
  have hxinv : ∀ w, h.data.conj x⁻¹ (h.data.conj tt w) = h.data.conj tt (h.data.conj x⁻¹ w) := by
    intro w
    apply (h.data.conj x).injective
    rw [← h.data.conj_mul x x⁻¹, mul_inv_cancel, hid, hx, ← h.data.conj_mul x x⁻¹,
      mul_inv_cancel, hid]
  have key : ∀ z : Subgroup.normalizer (V : Set G),
      (∀ w, h.data.conj z (h.data.conj tt w) = h.data.conj tt (h.data.conj z w)) →
      ∀ u ∈ U, (z : G) * u * (z : G)⁻¹ ∈ U := by
    intro z hz u hu
    have hzu : (z : G) * u * (z : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp z.2 u).mp hu.1
    have h1 : Multiplicative.toAdd (h.data.E ⟨u, hu.1⟩) ∈ h.data.addSub U :=
      (h.data.toAdd_mem_addSub _).mpr hu
    rw [h.mem_addSub_fix_iff htT] at h1
    have h2 : h.data.conj z (Multiplicative.toAdd (h.data.E ⟨u, hu.1⟩)) ∈ h.data.addSub U := by
      rw [h.mem_addSub_fix_iff htT, ← hz, h1]
    rw [h.data.conj_apply, h.data.toAdd_mem_addSub, conjAct_apply_coe] at h2
    exact h2
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key x hx u, fun hu => ?_⟩
  have := key x⁻¹ hxinv _ hu
  simpa [mul_assoc] using this

theorem exists_mem_lOne_of_comm (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (B : Matrix.SpecialLinearGroup (Fin 2) h.data.K)
    (hB : ∀ w, (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec
        (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ w) =
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩
        ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w))
    {m : ℕ} (hm : Odd m) (hBm : B ^ m = 1) :
    ∃ ℓ : ↥L, (ℓ : G) ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ∧ h.data.rho ℓ = B := by
  obtain ⟨g, hg⟩ := h.data.rho_surjective B
  have hgU : (g : G) ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) :
      Subgroup G) : Set G) := by
    refine h.mem_normalizer_fix_of_comm htT ⟨g, h.data.le_normalizer g.2⟩ fun w => ?_
    rw [h.data.conj_eq_rho, h.data.conj_eq_rho, hg]
    exact hB w
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
    (show (g : G) ∈ L ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) :
      Subgroup G) : Set G) from ⟨g.2, hgU⟩)
  have hodd : Odd (orderOf B) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hBm)
  have hcop : Nat.Coprime (2 ^ k) (orderOf B) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (A4.mem_zpowers_pow_of_coprime hcop)
  refine ⟨(g ^ 2 ^ k) ^ j, ?_, ?_⟩
  · have : (((g ^ 2 ^ k) ^ j : ↥L) : G) = ((g : G) ^ 2 ^ k) ^ j := by
      rw [Subgroup.coe_zpow, Subgroup.coe_pow]
    rw [this]
    exact Subgroup.zpow_mem _ hk j
  · rw [map_zpow, map_pow, hg, hj]

theorem irred_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    IsIrredOnSection (lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      (T ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))) V (V ⊓ Subgroup.centralizer ({t} : Set G)) := by
  classical
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  have h2K : (2 : h.data.K) = 0 := CharTwo.two_eq_zero
  have hlOne : lOne L U ≤ L ⊓ Subgroup.normalizer (U : Set G) := oTwoUpper_le _
  have hUcard : Nat.card U = 2 ^ n := h.card_fix_of_fieldAut htT ht
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  refine ⟨lt_of_le_of_ne inf_le_left fun heq => ?_,
    sup_le (hlOne.trans (inf_le_left.trans h.data.le_normalizer))
      (inf_le_left.trans h.toHyp611.T_le_normalizer),
    sup_le (hlOne.trans inf_le_right) inf_le_right, fun W hUW hWV hXW => ?_⟩
  · rw [heq, hVcard] at hUcard
    nlinarith
  by_cases hWU : W ≤ U
  · exact Or.inl (le_antisymm hWU hUW)
  right
  obtain ⟨w₀, hw₀W, hw₀U⟩ := Set.not_subset.mp hWU
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear tt (h.T_le_normalizer_L htT)
  obtain ⟨u₁, u₂, hu₁, hu₂, hdet⟩ := h.exists_basis_fix htT ht
  have hg : ∀ a b : h.data.K, h.data.conj tt (a • u₁ + b • u₂) = σ a • u₁ + σ b • u₂ := by
    intro a b
    rw [map_add, hσ, hσ, hu₁, hu₂]
  have hgg : ∀ w, h.data.conj tt (h.data.conj tt w) = w := by
    intro w
    rw [← h.data.conj_mul]
    exact h.data.conj_eq_of_mem_centralizer (tt * tt)
      (h.sq_mem_centralizer_of_fieldAut htT ht) w
  have hcoord : ∀ a b a' b' : h.data.K, a • u₁ + b • u₂ = a' • u₁ + b' • u₂ → a = a' ∧ b = b' := by
    intro a b a' b' heq
    have e0 := congrFun heq 0
    have e1 := congrFun heq 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    have hdet' : u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0 ≠ 0 := hdet
    constructor
    · have : (a - a') * (u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0) = 0 := by
        linear_combination (u₂ 1) * e0 - (u₂ 0) * e1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hdet')
    · have : (b - b') * (u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0) = 0 := by
        linear_combination (u₁ 0) * e1 - (u₁ 1) * e0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hdet')
  have hfixc : ∀ w, h.data.conj tt w = w →
      σ ((w 0 * u₂ 1 - w 1 * u₂ 0) / det2 u₁ u₂) = (w 0 * u₂ 1 - w 1 * u₂ 0) / det2 u₁ u₂ ∧
      σ ((u₁ 0 * w 1 - u₁ 1 * w 0) / det2 u₁ u₂) = (u₁ 0 * w 1 - u₁ 1 * w 0) / det2 u₁ u₂ := by
    intro w hw
    have h1 := hw
    rw [eq_add_of_det2_ne_zero hdet w, hg] at h1
    exact hcoord _ _ _ _ h1
  have hcomm_basis : ∀ B : Matrix.SpecialLinearGroup (Fin 2) h.data.K,
      h.data.conj tt ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₁) =
        (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₁ →
      h.data.conj tt ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₂) =
        (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₂ →
      ∀ w, (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec (h.data.conj tt w) =
        h.data.conj tt ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w) := by
    intro B h1 h2 w
    rw [eq_add_of_det2_ne_zero hdet w, hg]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [map_add, hσ, hσ, h1, h2]
  have hone_basis : ∀ B : Matrix.SpecialLinearGroup (Fin 2) h.data.K,
      (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₁ = u₁ →
      (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₂ = u₂ → B = 1 := by
    intro B h1 h2
    apply Subtype.ext
    apply matrix_eq_of_mulVec_eq
    intro w
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, eq_add_of_det2_ne_zero hdet w]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [h1, h2]
  set W' := h.data.addSub W with hW'
  have htN : t ∈ T ⊓ Subgroup.normalizer (U : Set G) :=
    ⟨htT, Subgroup.centralizer_le_normalizer _ htU⟩
  have hWt : ∀ y ∈ W', h.data.conj tt y ∈ W' := fun y hy =>
    h.conj_mem_addSub tt (hXW (Subgroup.mem_sup_right htN)) hy
  have hWB : ∀ B : Matrix.SpecialLinearGroup (Fin 2) h.data.K,
      (∀ w, (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec (h.data.conj tt w) =
        h.data.conj tt ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w)) →
      (∃ m, Odd m ∧ B ^ m = 1) →
      ∀ y ∈ W', (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec y ∈ W' := by
    rintro B hB ⟨m, hm, hBm⟩ y hy
    obtain ⟨ℓ, hℓ, hρℓ⟩ := h.exists_mem_lOne_of_comm htT B hB hm hBm
    rw [← hρℓ, ← h.data.conj_eq_rho]
    exact h.conj_mem_addSub _ (hXW (Subgroup.mem_sup_left hℓ)) hy
  let ψ : ↥W' →+ (Fin 2 → h.data.K) :=
    { toFun := fun y => (y : Fin 2 → h.data.K) + h.data.conj tt y
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [AddSubgroup.coe_add, map_add]
        abel }
  have hψ : ∀ y : ↥W', ψ y = (y : Fin 2 → h.data.K) + h.data.conj tt y := fun _ => rfl
  have hψB : ∀ B : Matrix.SpecialLinearGroup (Fin 2) h.data.K,
      (∀ w, (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec (h.data.conj tt w) =
        h.data.conj tt ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w)) →
      (∃ m, Odd m ∧ B ^ m = 1) →
      ∀ x ∈ ψ.range, (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec x ∈ ψ.range := by
    intro B hB hBo x hx
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hx
    refine AddMonoidHom.mem_range.mpr ⟨⟨_, hWB B hB hBo y y.2⟩, ?_⟩
    rw [hψ, hψ, Matrix.mulVec_add, hB]
  have hDiag : ∀ μ a b : h.data.K, σ μ = μ → μ ≠ 0 → a • u₁ + b • u₂ ∈ ψ.range →
      (μ * a) • u₁ + (μ⁻¹ * b) • u₂ ∈ ψ.range := by
    intro μ a b hμ hμ0 hx
    have hdetμ : det2 (μ • u₁) (μ⁻¹ • u₂) = det2 u₁ u₂ := by
      simp only [det2, Pi.smul_apply, smul_eq_mul]
      rw [show μ * u₁ 0 * (μ⁻¹ * u₂ 1) - μ * u₁ 1 * (μ⁻¹ * u₂ 0) =
          (μ * μ⁻¹) * (u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0) by ring, mul_inv_cancel₀ hμ0, one_mul]
    obtain ⟨B, hB1, hB2⟩ := exists_sl2_basis hdet hdetμ
    have hBc := hcomm_basis B (by rw [hB1, hσ, hu₁, hμ])
      (by rw [hB2, hσ, hu₂, map_inv₀, hμ])
    have hpow : ∀ k : ℕ, ((B ^ k : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₁ = μ ^ k • u₁ ∧
        ((B ^ k : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₂ = μ⁻¹ ^ k • u₂ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        refine ⟨?_, ?_⟩
        · rw [sl2_pow_succ_mulVec, ih.1, Matrix.mulVec_smul, hB1, smul_smul, pow_succ]
        · rw [sl2_pow_succ_mulVec, ih.2, Matrix.mulVec_smul, hB2, smul_smul, pow_succ]
    have : Fintype h.data.K := Fintype.ofFinite _
    have hcardK : Fintype.card h.data.K = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, h.data.card]
    have hn2 := h.two_le
    have hodd : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have hBm : B ^ (2 ^ n - 1) = 1 := by
      apply hone_basis
      · rw [(hpow _).1, ← hcardK, FiniteField.pow_card_sub_one_eq_one μ hμ0, one_smul]
      · rw [(hpow _).2, ← hcardK, FiniteField.pow_card_sub_one_eq_one μ⁻¹ (inv_ne_zero hμ0),
          one_smul]
    have h1 := hψB B hBc ⟨_, hodd, hBm⟩ _ hx
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hB1, hB2, smul_smul,
      smul_smul, mul_comm a, mul_comm b] at h1
    exact h1
  have hCyc : ∀ a b : h.data.K, a • u₁ + b • u₂ ∈ ψ.range → b • u₁ + (a + b) • u₂ ∈ ψ.range := by
    intro a b hx
    have hdetc : det2 u₂ (u₁ + u₂) = det2 u₁ u₂ := by
      simp only [det2, Pi.add_apply]
      linear_combination (u₁ 1 * u₂ 0 - u₁ 0 * u₂ 1) * h2K
    obtain ⟨B, hB1, hB2⟩ := exists_sl2_basis hdet hdetc
    have hBc := hcomm_basis B (by rw [hB1, hu₂]) (by rw [hB2, map_add, hu₁, hu₂])
    have hB3 : B ^ 3 = 1 := by
      apply hone_basis
      · rw [sl2_pow_succ_mulVec, sl2_pow_succ_mulVec, sl2_pow_succ_mulVec, pow_zero,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, hB1, hB2, Matrix.mulVec_add,
          hB1, hB2]
        funext i
        simp only [Pi.add_apply]
        linear_combination (u₂ i) * h2K
      · rw [sl2_pow_succ_mulVec, sl2_pow_succ_mulVec, sl2_pow_succ_mulVec, pow_zero,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, hB2, Matrix.mulVec_add, hB1, hB2]
        have : u₂ + (u₁ + u₂) = u₁ := by
          funext i
          simp only [Pi.add_apply]
          linear_combination (u₂ i) * h2K
        rw [this, hB1]
    have h1 := hψB B hBc ⟨3, ⟨1, by norm_num⟩, hB3⟩ _ hx
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hB1, hB2] at h1
    have e : a • u₂ + b • (u₁ + u₂) = b • u₁ + (a + b) • u₂ := by
      rw [smul_add, add_smul]
      abel
    rwa [e] at h1
  set y₀ : ↥W' := ⟨Multiplicative.toAdd (h.data.E ⟨w₀, hWV hw₀W⟩),
    (h.data.toAdd_mem_addSub _).mpr hw₀W⟩ with hy₀
  set x₀ := ψ y₀ with hx₀
  have hx₀fix : h.data.conj tt x₀ = x₀ := by
    rw [hx₀, hψ, map_add, hgg, add_comm]
  have hx₀0 : x₀ ≠ 0 := by
    intro h0
    apply hw₀U
    have h1 : h.data.conj tt (y₀ : Fin 2 → h.data.K) = y₀ := by
      rw [hx₀, hψ] at h0
      funext i
      have := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      linear_combination this - ((y₀ : Fin 2 → h.data.K) i) * h2K
    rw [← h.mem_addSub_fix_iff htT, hy₀] at h1
    exact (h.data.toAdd_mem_addSub _).mp h1
  obtain ⟨hσa₀, hσb₀⟩ := hfixc x₀ hx₀fix
  have hx₀eq := eq_add_of_det2_ne_zero hdet x₀
  have hrange : ∀ w, h.data.conj tt w = w → w ∈ ψ.range := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact AddSubgroup.zero_mem _
    obtain ⟨hσa, hσb⟩ := hfixc w hw
    rw [eq_add_of_det2_ne_zero hdet w]
    refine orbit_fixed h.two_dvd_card_K σ (fun a b => a • u₁ + b • u₂ ∈ ψ.range) hDiag hCyc
      hσa₀ hσb₀ ?_ ?_ hσa hσb ?_
    · rintro ⟨ha, hb⟩
      apply hx₀0
      rw [hx₀eq, ha, hb, zero_smul, zero_smul, add_zero]
    · show _ • u₁ + _ • u₂ ∈ ψ.range
      rw [← hx₀eq]
      exact AddMonoidHom.mem_range.mpr ⟨y₀, rfl⟩
    · rintro ⟨ha, hb⟩
      apply hw0
      rw [eq_add_of_det2_ne_zero hdet w, ha, hb, zero_smul, zero_smul, add_zero]
  have hcardW' : Nat.card ↥W' = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have hker : 2 ^ n ≤ Nat.card ψ.ker := by
    rw [← hUcard, ← h.data.card_addSub (inf_le_left : U ≤ V)]
    refine Nat.card_le_card_of_injective (fun y => ⟨⟨y.1, ?_⟩, ?_⟩) ?_
    · rw [hW', h.data.mem_addSub]
      exact hUW ((h.data.mem_addSub).mp y.2)
    · rw [AddMonoidHom.mem_ker, hψ]
      have h1 : h.data.conj tt y.1 = y.1 := (h.mem_addSub_fix_iff htT y.1).mp y.2
      change y.1 + h.data.conj tt y.1 = 0
      rw [h1]
      funext i
      exact CharTwo.add_self_eq_zero _
    · intro a b hab
      have h1 := congrArg (fun z : ↥ψ.ker => ((z : ↥W') : Fin 2 → h.data.K)) hab
      exact Subtype.ext h1
  have hrng : 2 ^ n ≤ Nat.card ψ.range := by
    have hfix : Nat.card {w : Fin 2 → h.data.K // h.data.conj tt w = w} = 2 ^ n := by
      rw [← Nat.card_congr (h.data.fixedEquiv tt)]
      exact hUcard
    rw [← hfix]
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, hrange w.1 w.2⟩) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext h1
  have hWcard : Nat.card V ≤ Nat.card W := by
    rw [← h.data.card_addSub hWV, ← hW', hcardW', hVcard]
    exact Nat.mul_le_mul hker hrng
  exact Subgroup.eq_of_le_of_card_ge hWV hWcard

end Hyp611Nat

end CFSG.Quasithin.H13
