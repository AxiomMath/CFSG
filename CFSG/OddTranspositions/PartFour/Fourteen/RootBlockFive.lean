module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlock
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open

namespace RootBlockFive

open TableE1Five

private theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

section Vectors

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem exists_sq_add_sq_eq {a d t : ZMod 5} (ha : a ≠ 0) (hd : d ≠ 0) (ht : t ≠ 0) :
    ∃ l m : ZMod 5, l * l * a + m * m * d = t := by
  revert a d t
  decide

private theorem exists_aniso_perp₄ (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {u₁ u₂ u₃ u₄ : Fin n → ZMod 5}
    (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0) (h₃ : b u₃ u₃ ≠ 0) (h₄ : b u₄ u₄ ≠ 0)
    (h₁₂ : b u₁ u₂ = 0) (h₁₃ : b u₁ u₃ = 0) (h₁₄ : b u₁ u₄ = 0) (h₂₃ : b u₂ u₃ = 0)
    (h₂₄ : b u₂ u₄ = 0) (h₃₄ : b u₃ u₄ = 0) :
    ∃ z, b z u₁ = 0 ∧ b z u₂ = 0 ∧ b z u₃ = 0 ∧ b z u₄ = 0 ∧ b z z ≠ 0 := by
  have h₂₁ : b u₂ u₁ = 0 := by rw [hsym]; exact h₁₂
  have h₃₁ : b u₃ u₁ = 0 := by rw [hsym]; exact h₁₃
  have h₄₁ : b u₄ u₁ = 0 := by rw [hsym]; exact h₁₄
  have h₃₂ : b u₃ u₂ = 0 := by rw [hsym]; exact h₂₃
  have h₄₂ : b u₄ u₂ = 0 := by rw [hsym]; exact h₂₄
  have h₄₃ : b u₄ u₃ = 0 := by rw [hsym]; exact h₃₄
  obtain ⟨z, hz, hzz⟩ := exists_aniso_perp hsym hnd (k := 4) (by omega) ![u₁, u₂, u₃, u₄]
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | simp [h₁₂, h₂₁, h₁₃, h₃₁, h₁₄, h₄₁, h₂₃, h₃₂, h₂₄, h₄₂, h₃₄, h₄₃])
    (fun i => by fin_cases i <;> simp [h₁, h₂, h₃, h₄])
  exact ⟨z, by simpa using hz 0, by simpa using hz 1, by simpa using hz 2, by simpa using hz 3,
    hzz⟩

theorem exists_norm_eq_perp₃ (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {u₁ u₂ u₃ : Fin n → ZMod 5}
    (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0) (h₃ : b u₃ u₃ ≠ 0)
    (h₁₂ : b u₁ u₂ = 0) (h₁₃ : b u₁ u₃ = 0) (h₂₃ : b u₂ u₃ = 0) (c : ZMod 5) :
    ∃ y, b y u₁ = 0 ∧ b y u₂ = 0 ∧ b y u₃ = 0 ∧ b y y = c := by
  by_cases hc : c = 0
  · exact ⟨0, by simp, by simp, by simp, by simp [hc]⟩
  obtain ⟨e₁, he₁₁, he₁₂, he₁₃, he₁⟩ :=
    exists_aniso_perp₃ hsym hnd (by omega) h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  obtain ⟨e₂, he₂₁, he₂₂, he₂₃, he₂₄, he₂⟩ :=
    exists_aniso_perp₄ hsym hnd hn h₁ h₂ h₃ he₁ h₁₂ h₁₃ (by rw [hsym]; exact he₁₁) h₂₃
      (by rw [hsym]; exact he₁₂) (by rw [hsym]; exact he₁₃)
  obtain ⟨l, m, hlm⟩ := exists_sq_add_sq_eq he₁ he₂ hc
  refine ⟨l • e₁ + m • e₂, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, he₁₁, he₂₁]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, he₁₂, he₂₂]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, he₁₃, he₂₃]
    ring
  · have he₁₂' : b e₁ e₂ = 0 := by rw [hsym]; exact he₂₄
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, he₂₄, he₁₂']
    rw [← hlm]
    ring

private theorem eq_one_or_eq_neg_one_of_mul_self {c : ZMod 5} (h : c * c = 1) :
    c = 1 ∨ c = -1 := by
  revert c
  decide

private theorem exists_perp_pairing_two (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (hwv : w ≠ v) (hwv' : w ≠ -v) :
    ∃ x, b x v = 0 ∧ b x x = 1 ∧ b w x = 2 := by
  have hvw : b v w = b w v := hsym v w
  obtain ⟨c, hc⟩ : ∃ c, c = b w v := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin n → ZMod 5, p = w - c • v := ⟨_, rfl⟩
  have hwp : w = p + c • v := by rw [hp]; abel
  have hpv : b p v = 0 := by
    simp only [hp, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, ← hc]
    ring
  have hvp : b v p = 0 := by rw [hsym]; exact hpv
  have hpw : b p w = 1 - c * c := by
    simp only [hp, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hw, hvw, ← hc]
  have hpp : b p p = 1 - c * c := by
    have h1 : b p p = b p w - c * b p v := by
      calc b p p = b p (w - c • v) := congrArg (b p) hp
        _ = b p w - c * b p v := by
          rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]
    rw [h1, hpv, hpw]
    ring
  have hp0 : p ≠ 0 := by
    intro h0
    have hwc : w = c • v := by rw [hwp, h0, zero_add]
    have h1 : c * c = 1 := by
      have := hw
      rw [hwc, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv] at this
      linear_combination this
    rcases eq_one_or_eq_neg_one_of_mul_self h1 with h | h
    · exact hwv (by rw [hwc, h, one_smul])
    · exact hwv' (by rw [hwc, h, neg_one_smul])
  have hwx : ∀ x, b x v = 0 → b w x = b p x := by
    intro x hx
    rw [hwp, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hsym v x, hx]
    ring
  by_cases hiso : 1 - c * c = 0
  ·
    have hQp : b p p = 0 := by rw [hpp]; exact hiso
    obtain ⟨y, hy⟩ : ∃ y, b p y ≠ 0 := by
      by_contra! h
      exact hp0 (hnd p h)
    obtain ⟨t, ht⟩ : ∃ t : Fin n → ZMod 5, t = (b p y)⁻¹ • (y - b y v • v) := ⟨_, rfl⟩
    have htv : b t v = 0 := by
      simp only [ht, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.sub_left, hv]
      ring
    have hpt : b p t = 1 := by
      simp only [ht, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.sub_right, hpv]
      rw [mul_zero, sub_zero]
      exact inv_mul_cancel₀ hy
    have hxv : b ((2 : ZMod 5) • t + (4 - b t t) • p) v = 0 := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, htv, hpv]
      ring
    refine ⟨(2 : ZMod 5) • t + (4 - b t t) • p, hxv, ?_, ?_⟩
    · have hpt' : b t p = 1 := by rw [hsym]; exact hpt
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hpt, hpt', hQp]
      have h16 : (16 : ZMod 5) = 1 := by decide
      linear_combination h16
    · rw [hwx _ hxv]
      simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hpt, hQp]
      ring
  ·
    have hA : b p p ≠ 0 := by rw [hpp]; exact hiso
    have hv0 : b v v ≠ 0 := by rw [hv]; decide
    obtain ⟨e, hev, hep, hee⟩ := exists_aniso_perp₂ hsym hnd (by omega) hv0 hA hvp
    obtain ⟨y, hyv, hyp, -, hyy⟩ := exists_norm_eq_perp₃ hsym hnd hn hv0 hA hee hvp
      (by rw [hsym]; exact hev) (by rw [hsym]; exact hep) (1 - 4 * (b p p)⁻¹)
    have hinv : b p p * (b p p)⁻¹ = 1 := mul_inv_cancel₀ hA
    have hpy : b p y = 0 := by rw [hsym]; exact hyp
    have hxv : b ((2 * (b p p)⁻¹) • p + y) v = 0 := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hpv, hyv]
      ring
    refine ⟨(2 * (b p p)⁻¹) • p + y, hxv, ?_, ?_⟩
    · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hyp, hpy, hyy]
      linear_combination (4 * (b p p)⁻¹) * hinv
    · rw [hwx _ hxv]
      simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hpy]
      linear_combination 2 * hinv

private theorem mem_of_perp_pair (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {V C : (Fin n → ZMod 5) → Prop}
    (hperp : ∀ x y, V y → b x y = 0 → C x)
    (hCC : ∀ x y, C x → C y → C (act (refl b x) y)) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq : b p q = 0) (Vp : V p) (Vq : V q)
    {z : Fin n → ZMod 5} (hz : b z z = 1) : C z := by
  by_cases hzp : b z p = 0
  · exact hperp z p Vp hzp
  by_cases hzq : b z q = 0
  · exact hperp z q Vq hzq
  have hqp : b q p = 0 := by rw [hsym]; exact hpq
  obtain ⟨a, ha⟩ : ∃ a, a = b z p := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = b z q := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha]; exact hzp
  have ha'0 : a' ≠ 0 := by rw [ha']; exact hzq
  have hpz : b p z = a := by rw [hsym, ha]
  have hqz : b q z = a' := by rw [hsym, ha']
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Fin n → ZMod 5, z₀ = z - a • p - a' • q := ⟨_, rfl⟩
  have hzz₀ : z = a • p + a' • q + z₀ := by rw [hz₀]; abel
  have hz₀p : b z₀ p = 0 := by
    simp only [hz₀, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hp, hqp, ← ha]
    ring
  have hz₀q : b z₀ q = 0 := by
    simp only [hz₀, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hq, hpq, ← ha']
    ring
  have hpz₀ : b p z₀ = 0 := by rw [hsym]; exact hz₀p
  have hqz₀ : b q z₀ = 0 := by rw [hsym]; exact hz₀q
  have hq₀ : b z₀ z₀ = 1 - a * a - a' * a' := by
    calc b z₀ z₀ = b z₀ (z - a • p - a' • q) := congrArg (b z₀) hz₀
      _ = b z₀ z - a * b z₀ p - a' * b z₀ q := by
        rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sub_right,
          LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right]
      _ = 1 - a * a - a' * a' := by
        rw [hz₀p, hz₀q, hz₀]
        simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz, hpz, hqz]
        ring
  have hq₀ne : b z₀ z₀ ≠ 0 := by
    have key : ∀ a a' : ZMod 5, a ≠ 0 → a' ≠ 0 → 1 - a * a - a' * a' ≠ 0 := by decide
    rw [hq₀]
    exact key a a' ha0 ha'0
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  have hq0 : b q q ≠ 0 := by rw [hq]; decide
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (2 + a' * a') * (b z₀ z₀)⁻¹ := ⟨_, rfl⟩
  obtain ⟨u'', hu''p, hu''q, hu''z, hu''u''⟩ := exists_norm_eq_perp₃ hsym hnd hn hp0 hq0 hq₀ne
    hpq hpz₀ hqz₀ (1 - a' * a' - γ * γ * b z₀ z₀)
  obtain ⟨u, hu⟩ : ∃ u : Fin n → ZMod 5, u = (-a') • q + γ • z₀ + u'' := ⟨_, rfl⟩
  have hpu'' : b p u'' = 0 := by rw [hsym]; exact hu''p
  have hqu'' : b q u'' = 0 := by rw [hsym]; exact hu''q
  have hz₀u'' : b z₀ u'' = 0 := by rw [hsym]; exact hu''z
  have hup : b u p = 0 := by
    simp only [hu, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hqp, hz₀p, hu''p]
    ring
  have huq : b u q = -a' := by
    simp only [hu, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hq, hz₀q, hu''q]
    ring
  have hz₀u : b z₀ u = γ * b z₀ z₀ := by
    simp only [hu, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hz₀q, hz₀u'']
    ring
  have huu : b u u = 1 := by
    simp only [hu, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hq, hqz₀, hz₀q, hqu'', hz₀u'',
      hu''q, hu''z, hu''u'']
    ring
  have hzu : b z u = 2 := by
    have h1 : b z u = a * b p u + a' * b q u + b z₀ u := by
      conv_lhs => rw [hzz₀]
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
    rw [h1, hsym p u, hup, hsym q u, huq, hz₀u, hγ]
    have hinv : b z₀ z₀ * (b z₀ z₀)⁻¹ = 1 := mul_inv_cancel₀ hq₀ne
    linear_combination (2 + a' * a') * hinv
  have hrefl : act (refl b u) z = z + u := by
    rw [act_refl huu, hzu, show (-2 * 2 : ZMod 5) = 1 by decide, one_smul]
  have hyq : b (act (refl b u) z) q = 0 := by
    rw [hrefl, LinearMap.BilinForm.add_left, huq, ← ha']
    ring
  have Cu : C u := hperp u p Vp hup
  have Cy : C (act (refl b u) z) := hperp _ q Vq hyq
  have := hCC u _ Cu Cy
  rwa [← act_mul, refl_mul_self, act_one] at this

private theorem mem_of_two_members (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {V C : (Fin n → ZMod 5) → Prop}
    (hVC : ∀ z, V z → C z) (hperp : ∀ x y, V y → b x y = 0 → C x)
    (hCC : ∀ x y, C x → C y → C (act (refl b x) y))
    (hCV : ∀ x y, C x → V y → V (act (refl b x) y)) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (hwv : w ≠ v) (hwv' : w ≠ -v) (Vv : V v) (Vw : V w)
    {z : Fin n → ZMod 5} (hz : b z z = 1) : C z := by
  obtain ⟨x, hxv, hxx, hwx⟩ := exists_perp_pairing_two hsym hnd hn hv hw hwv hwv'
  have Cx : C x := hperp x v Vv hxv
  have hwx' : b x w = 2 := by rw [hsym]; exact hwx
  have h1 : act (refl b x) w = w + x := by
    rw [act_refl hxx, hwx, show (-2 * 2 : ZMod 5) = 1 by decide, one_smul]
  have h2 : act (refl b w) (w + x) = x := by
    rw [act_refl hw, LinearMap.BilinForm.add_left, hw, hwx',
      show (-2 * (1 + 2) : ZMod 5) = -1 by decide]
    module
  have Vx : V x := by
    have := hCV w _ (hVC w Vw) (hCV x w Cx Vw)
    rwa [h1, h2] at this
  exact mem_of_perp_pair hsym hnd hn hperp hCC hv hxx (by rw [hsym]; exact hxv) Vv Vx hz

end Vectors

section Quotient

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

@[expose] noncomputable def reflQ (b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5))
    (z : Fin n → ZMod 5) : reflGroup b ⧸ Subgroup.center (reflGroup b) :=
  QuotientGroup.mk ⟨refl b z, refl_mem_reflGroup z⟩

theorem reflQ_conj (hsym : ∀ x y, b x y = b y x) (x y : Fin n → ZMod 5) :
    reflQ b x * reflQ b y * (reflQ b x)⁻¹ = reflQ b (act (refl b x) y) := by
  unfold reflQ
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (conj_refl (refl_mem_isomGroup hsym x) y)

theorem reflQ_neg (z : Fin n → ZMod 5) : reflQ b (-z) = reflQ b z := by
  unfold reflQ
  congr 1
  exact Subtype.ext (refl_neg z)

theorem reflQ_comm_of_perp (hsym : ∀ x y, b x y = b y x) {x y : Fin n → ZMod 5}
    (h : b x y = 0) : reflQ b x * reflQ b y = reflQ b y * reflQ b x := by
  unfold reflQ
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (refl_comm_of_perp hsym h)

theorem refl_eq_of_reflQ_eq (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {x y : Fin n → ZMod 5}
    (hx : b x x = 1) (h : reflQ b x = reflQ b y) : refl b x = refl b y := by
  unfold reflQ at h
  rw [QuotientGroup.eq] at h
  rcases coe_eq_of_mem_center hsym hnd hn hx h with h1 | h1
  · rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact inv_mul_eq_one.mp h1
  · exfalso
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    apply refl_ne_neg_refl (b := b) (by omega) x y
    calc refl b y = refl b x * ((refl b x)⁻¹ * refl b y) := by group
      _ = -refl b x := by rw [h1, mul_neg_one]

theorem eq_perp_or_of_reflQ_comm (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {x y : Fin n → ZMod 5}
    (hx : b x x = 1) (hy : b y y = 1) (h : reflQ b x * reflQ b y = reflQ b y * reflQ b x) :
    b x y = 0 ∨ y = x ∨ y = -x := by
  have h1 : reflQ b y = reflQ b (act (refl b x) y) := by
    rw [← reflQ_conj hsym, h, mul_assoc, mul_inv_cancel, mul_one]
  have h2 := refl_eq_of_reflQ_eq hsym hnd hn hy h1
  have hy' : b (act (refl b x) y) (act (refl b x) y) = 1 := by
    rw [isom_norm (refl_mem_isomGroup hsym x), hy]
  rcases (refl_eq_refl_iff hy hy').mp h2 with h3 | h3
  · left
    rw [act_refl hx] at h3
    have h4 : (-2 * b y x) • x = 0 := by
      have := congrArg (fun t => t - y) h3
      simpa using this
    rcases smul_eq_zero.mp h4 with h5 | h5
    · rw [hsym]
      have h6 : b y x = 0 := by
        have h7 : (-2 : ZMod 5) ≠ 0 := by decide
        exact (mul_eq_zero.mp h5).resolve_left h7
      exact h6
    · exact absurd h5 (ne_zero_of_norm_ne_zero (by rw [hx]; decide))
  · right
    rw [act_refl hx] at h3
    have h4 : y = (b y x) • x := by
      have h5 : (2 : ZMod 5) • (y - (b y x) • x) = 0 := by
        have := congrArg (fun t => t + y) h3
        linear_combination (norm := module) this
      have h6 : y - (b y x) • x = 0 :=
        (smul_eq_zero.mp h5).resolve_left (by decide)
      exact sub_eq_zero.mp h6
    have h7 : b y x * b y x = 1 := by
      have := hy
      rw [h4] at this
      simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hx] at this
      linear_combination this
    rcases eq_one_or_eq_neg_one_of_mul_self h7 with h8 | h8
    · left
      rw [h4, h8, one_smul]
    · right
      rw [h4, h8, neg_one_smul]

private theorem five_eq_zero : (5 : ZMod 5) = 0 := by decide

theorem exists_pairing_two (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 3 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1) :
    ∃ z, b z z = 1 ∧ b z v = 2 := by
  obtain ⟨s, hsv, hss⟩ := exists_norm_eq_perp hsym hnd hn (v := v) (by rw [hv]; decide)
    (c := 2) (by decide)
  have hvs : b v s = 0 := by rw [hsym]; exact hsv
  refine ⟨(2 : ZMod 5) • v + s, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hss, hsv, hvs]
    linear_combination five_eq_zero
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hv, hsv]
    ring

private theorem eq_top_of_reflQ_mem (N : Subgroup (reflGroup b ⧸ Subgroup.center (reflGroup b)))
    (h : ∀ z, b z z = 1 → reflQ b z ∈ N) : N = ⊤ := by
  rw [eq_top_iff]
  intro q _
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, hg⟩ := γ
  refine Subgroup.closure_induction (k := reflSet b)
    (p := fun (g : GL (Fin n) (ZMod 5)) (hg : g ∈ Subgroup.closure (reflSet b)) =>
      (QuotientGroup.mk ⟨g, hg⟩ : reflGroup b ⧸ Subgroup.center (reflGroup b)) ∈ N)
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_reflSet_iff.mp hx
    exact h z hz
  · exact N.one_mem
  · intro x y _ _ hx hy
    exact N.mul_mem hx hy
  · intro x _ hx
    exact N.inv_mem hx

private theorem subset_rootBlock_and_ne_aux {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hn : 5 ≤ n)
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (φ : X ≃* reflGroup b ⧸ Subgroup.center (reflGroup b))
    (hφ : ∀ g : X, g ∈ E ↔ ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧
      φ g = (QuotientGroup.mk h : reflGroup b ⧸ Subgroup.center (reflGroup b)))
    {s : X} (hs : s ∈ E) :
    (∀ β, IsBlock E β → s ∈ β → β ⊆ {s}) ∧ rootBlock E s ≠ E := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin n → ZMod 5) → X, ∀ z, φ (ρ z) = reflQ b z :=
    ⟨fun z => φ.symm (reflQ b z), fun z => φ.apply_symm_apply _⟩
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hρE : ∀ z, b z z = 1 → ρ z ∈ E := fun z hz =>
    (hφ _).2 ⟨⟨refl b z, refl_mem_reflGroup z⟩, refl_mem_reflSet hz, hρ z⟩
  have hρcases : ∀ x ∈ E, ∃ z, b z z = 1 ∧ x = ρ z := by
    intro x hx
    obtain ⟨h, hhT, hφx⟩ := (hφ x).1 hx
    obtain ⟨z, hz, hzh⟩ := mem_reflSet_iff.1 hhT
    refine ⟨z, hz, φ.injective ?_⟩
    rw [hφx, hρ z]
    unfold reflQ
    congr 1
    exact Subtype.ext hzh.symm
  have hρneg : ∀ z, ρ (-z) = ρ z := fun z => φ.injective (by rw [hρ, hρ, reflQ_neg])
  have hρconj : ∀ x y, ρ x * ρ y * (ρ x)⁻¹ = ρ (act (refl b x) y) := fun x y =>
    φ.injective (by rw [map_mul, map_mul, map_inv, hρ, hρ, hρ, reflQ_conj hsym])
  have hρcomm : ∀ x y, b x y = 0 → Commute (ρ x) (ρ y) := fun x y h =>
    φ.injective (by rw [map_mul, map_mul, hρ, hρ, reflQ_comm_of_perp hsym h])
  have hρcomm' : ∀ x y, b x x = 1 → b y y = 1 → Commute (ρ x) (ρ y) →
      b x y = 0 ∨ y = x ∨ y = -x := fun x y hx hy hc =>
    eq_perp_or_of_reflQ_comm hsym hnd (by omega) hx hy (by
      have := congrArg φ hc.eq
      rwa [map_mul, map_mul, hρ, hρ] at this)
  obtain ⟨v, hv, rfl⟩ := hρcases s hs
  have hne : rootBlock E (ρ v) ≠ E := by
    intro hEq
    obtain ⟨z, hz, hzv⟩ := exists_pairing_two hsym hnd (by omega) hv
    have hzE : ρ z ∈ rootBlock E (ρ v) := by rw [hEq]; exact hρE z hz
    have h1 : Commute (ρ v) (ρ z) := (hzE.2 (ρ v) hs).mpr (Commute.refl _)
    rcases hρcomm' v z hv hz h1 with h2 | h2 | h2
    · rw [hsym, hzv] at h2
      exact absurd h2 (by decide)
    · rw [h2, hv] at hzv
      exact absurd hzv (by decide)
    · rw [h2, LinearMap.BilinForm.neg_left, hv] at hzv
      exact absurd hzv (by decide)
  refine ⟨fun β hβ hsβ t htβ => ?_, hne⟩
  obtain ⟨w, hw, rfl⟩ := hρcases t (hβ.1 htβ)
  by_cases hwv : w = v ∨ w = -v
  · have h1 : ρ w = ρ v := by
      rcases hwv with h | h
      · rw [h]
      · rw [h, hρneg]
    rw [h1]
    exact Set.mem_singleton _
  exfalso
  push Not at hwv
  have hCN : ∀ x ∈ β, ∀ g : X, Commute g x → g ∈ Subgroup.normalizer β := by
    intro x hx g hg
    by_contra hgN
    refine Set.disjoint_left.mp (hβ.2.2.2 g hgN) hx ⟨x, hx, ?_⟩
    change g * x * g⁻¹ = x
    rw [hg.eq, mul_inv_cancel_right]
  have hNmem : ∀ g ∈ Subgroup.normalizer β, ∀ x ∈ β, g * x * g⁻¹ ∈ β := by
    intro g hg x hx
    have h1 := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  have hall : ∀ z, b z z = 1 → ρ z ∈ Subgroup.normalizer β := fun z hz =>
    mem_of_two_members (V := fun z => ρ z ∈ β) (C := fun z => ρ z ∈ Subgroup.normalizer β)
      hsym hnd hn (fun z hz => hCN _ hz _ (Commute.refl _))
      (fun x y hy hxy => hCN _ hy _ (hρcomm x y hxy))
      (fun x y hx hy => by
        rw [← hρconj]
        exact (Subgroup.normalizer β).mul_mem ((Subgroup.normalizer β).mul_mem hx hy)
          ((Subgroup.normalizer β).inv_mem hx))
      (fun x y hx hy => by
        rw [← hρconj]
        exact hNmem _ hx _ hy)
      hv hw hwv.1 hwv.2 hsβ htβ hz
  have hN'top : (Subgroup.normalizer β).comap φ.symm.toMonoidHom = ⊤ :=
    eq_top_of_reflQ_mem _ fun z hz => by
      rw [Subgroup.mem_comap]
      have h1 : φ.symm.toMonoidHom (reflQ b z) = ρ z := by
        rw [← hρ z]
        exact φ.symm_apply_apply _
      rw [h1]
      exact hall z hz
  have hN : ∀ g : X, g ∈ Subgroup.normalizer β := fun g => by
    have h1 : φ g ∈ (Subgroup.normalizer β).comap φ.symm.toMonoidHom := by
      rw [hN'top]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_comap] at h1
    simpa using h1
  refine hβ.2.2.1 (hβ.1.antisymm fun x hx => ?_)
  obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
  exact hNmem g (hN g) (ρ v) hsβ

end Quotient

end RootBlockFive

theorem subset_rootBlock_and_ne_of_fischerCentralQuotientModel_five {X : Type} [Group X]
    {E : Set X} (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) {n : ℕ} (hn : 5 ≤ n)
    {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)} (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : fischerCentralQuotientModel E
      (Subgroup.closure (fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
    {s : X} (hs : s ∈ E) :
    (∀ β, IsBlock E β → s ∈ β → β ⊆ rootBlock E s) ∧ rootBlock E s ≠ E := by
  obtain ⟨φ, hφ⟩ := hM
  obtain ⟨hsub, hne⟩ := RootBlockFive.subset_rootBlock_and_ne_aux hcls hn hsym hnd φ hφ hs
  refine ⟨fun β hβ hsβ t htβ => ?_, hne⟩
  rw [hsub β hβ hsβ htβ]
  exact mem_rootBlock_self hs

theorem eq_singleton_of_isBlock_of_fischerCentralQuotientModel_five {X : Type} [Group X]
    {E : Set X} (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) {n : ℕ} (hn : 5 ≤ n)
    {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)} (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : fischerCentralQuotientModel E
      (Subgroup.closure (fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
    {s : X} (hs : s ∈ E) : ∀ β, IsBlock E β → s ∈ β → β = {s} := by
  obtain ⟨φ, hφ⟩ := hM
  intro β hβ hsβ
  exact (RootBlockFive.subset_rootBlock_and_ne_aux hcls hn hsym hnd φ hφ hs).1 β hβ hsβ
    |>.antisymm (Set.singleton_subset_iff.mpr hsβ)

theorem subset_rootBlock_and_ne_of_isFiveReflectionModel {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h : CFSG.OddTranspositions.PartThree.IsFiveReflectionModel k ε π E) {s : X} (hs : s ∈ E) :
    (∀ β, IsBlock E β → s ∈ β → β ⊆ rootBlock E s) ∧ rootBlock E s ≠ E := by
  obtain ⟨b, hsym, hnd, hM⟩ :=
    CFSG.OddTranspositions.PartThree.fischerModel_of_isFiveReflectionModel h
  exact subset_rootBlock_and_ne_of_fischerCentralQuotientModel_five hcls (n := k + 1) (by omega)
    hsym hnd hM hs

theorem rootBlock_eq_singleton_of_isFiveReflectionModel {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h : CFSG.OddTranspositions.PartThree.IsFiveReflectionModel k ε π E) {s : X} (hs : s ∈ E) :
    rootBlock E s = {s} := by
  obtain ⟨b, hsym, hnd, hM⟩ :=
    CFSG.OddTranspositions.PartThree.fischerModel_of_isFiveReflectionModel h
  have hne := (subset_rootBlock_and_ne_of_fischerCentralQuotientModel_five hcls (n := k + 1)
    (by omega) hsym hnd hM hs).2
  have hE : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    obtain ⟨d₀, rfl⟩ := hcls
    exact fun g x hx => (show IsConj d₀ x from hx).trans (isConj_iff.mpr ⟨g, rfl⟩)
  exact eq_singleton_of_isBlock_of_fischerCentralQuotientModel_five hcls (n := k + 1) (by omega)
    hsym hnd hM hs _ (isBlock_rootBlock hE hs hne) (mem_rootBlock_self hs)

end CFSG.OddTranspositions.PartFour
