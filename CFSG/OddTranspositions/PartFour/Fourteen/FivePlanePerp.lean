module

public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace FivePlane

open TableE1Five

private theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem two_mul_inv_two_mul (x : ZMod 5) : (2 : ZMod 5) * (2⁻¹ * x) = x := by
  rw [← mul_assoc, mul_inv_cancel₀ (by decide), one_mul]

private theorem norm_add (u v : Fin n → ZMod 5) :
    b (u + v) (u + v) = b u u + b u v + b v u + b v v := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
  ring

private theorem norm_sub (u v : Fin n → ZMod 5) :
    b (u - v) (u - v) = b u u - b u v - b v u + b v v := by
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right]
  ring

private theorem norm_add_sub (u v : Fin n → ZMod 5) :
    b (u + v) (u - v) = b u u - b u v + b v u - b v v := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.sub_right]
  ring

private theorem norm_smul (c : ZMod 5) (u : Fin n → ZMod 5) :
    b (c • u) (c • u) = c * c * b u u := by
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  ring

private theorem sub_smul_self_ne_zero {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hqp : q ≠ p) (hqp' : q ≠ -p) :
    p - b p q • q ≠ 0 := by
  intro h0
  have hpβ : p = b p q • q := sub_eq_zero.1 h0
  have hβ : b p q * b p q = 1 := by
    have h1 : b (b p q • q) (b p q • q) = b p q * b p q := by
      simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hq, mul_one]
    rw [← hpβ, hp] at h1
    exact h1.symm
  rcases mul_self_eq_one_iff.1 hβ with h | h
  · exact hqp (by rw [hpβ, h, one_smul])
  · exact hqp' (by rw [hpβ, h, neg_one_smul, neg_neg])

private theorem degenerate_perp_left {p q : Fin n → ZMod 5} (hp : b p p = 1)
    (hβ : b p q * b p q = 1) : b p (p - b p q • q) = 0 := by
  simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hp]
  linear_combination -hβ

private theorem degenerate_perp_right (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hβ : b p q * b p q = 1) : b (p - b p q • q) p = 0 := by
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hp, hsym q p]
  linear_combination -hβ

private theorem degenerate_isotropic (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hβ : b p q * b p q = 1) :
    b (p - b p q • q) (p - b p q • q) = 0 := by
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hp, hq, hsym q p]
  linear_combination -hβ

private theorem degenerate_perp_q {p q : Fin n → ZMod 5} (hq : b q q = 1) :
    b (p - b p q • q) q = 0 := by
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hq]
  ring

private theorem exists_perp_norm_one_of_degenerate (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {p q : Fin n → ZMod 5} (hp : b p p = 1)
    (hq : b q q = 1) (hqp : q ≠ p) (hqp' : q ≠ -p) (hβ : b p q * b p q = 1) :
    ∃ f', b f' p = 0 ∧ b f' (p - b p q • q) = 1 ∧ b f' f' = 0 := by
  have hpe : b p (p - b p q • q) = 0 := degenerate_perp_left hp hβ
  have hep : b (p - b p q • q) p = 0 := degenerate_perp_right hsym hp hβ
  have hee : b (p - b p q • q) (p - b p q • q) = 0 := degenerate_isotropic hsym hp hq hβ
  have he0 : p - b p q • q ≠ 0 := sub_smul_self_ne_zero hp hq hqp hqp'
  obtain ⟨t, ht⟩ : ∃ t, b t (p - b p q • q) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact he0 (hnd _ (fun y => by rw [hsym]; exact h y))
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, f₀ = t - b t p • p := ⟨_, rfl⟩
  have hf₀p : b f₀ p = 0 := by
    simp only [hf₀, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hp, mul_one,
      sub_self]
  have hf₀e : b f₀ (p - b p q • q) = b t (p - b p q • q) := by
    simp only [hf₀, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hpe,
      mul_zero, sub_zero]
  obtain ⟨f, hf⟩ : ∃ f, f = (b f₀ (p - b p q • q))⁻¹ • f₀ := ⟨_, rfl⟩
  have hfp : b f p = 0 := by
    simp only [hf, LinearMap.BilinForm.smul_left, hf₀p, mul_zero]
  have hfe : b f (p - b p q • q) = 1 := by
    rw [hf, LinearMap.BilinForm.smul_left, hf₀e]
    exact inv_mul_cancel₀ ht
  have hef : b (p - b p q • q) f = 1 := by
    rw [hsym]
    exact hfe
  obtain ⟨f', hf'⟩ : ∃ f', f' = f - (2⁻¹ * b f f) • (p - b p q • q) := ⟨_, rfl⟩
  have hf'p : b f' p = 0 := by
    simp only [hf', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hep,
      mul_zero, sub_zero, hfp]
  have hf'e : b f' (p - b p q • q) = 1 := by
    simp only [hf', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hee,
      mul_zero, sub_zero, hfe]
  have hf'f' : b f' f' = 0 := by
    have h2f : (2 : ZMod 5) * (2⁻¹ * b f f) = b f f := two_mul_inv_two_mul _
    rw [hf', norm_sub, norm_smul]
    simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hee, hfe, hef]
    linear_combination -h2f
  exact ⟨f', hf'p, hf'e, hf'f'⟩

private theorem exists_frame_of_degenerate (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {p q : Fin n → ZMod 5} (hp : b p p = 1)
    (hq : b q q = 1) (hqp : q ≠ p) (hqp' : q ≠ -p) (hβ : b p q * b p q = 1) :
    ∃ f' h₁ h₂ : Fin n → ZMod 5,
      b f' p = 0 ∧ b f' (p - b p q • q) = 1 ∧ b f' f' = 0 ∧
      h₁ = p - b p q • q + f' ∧ h₂ = p - b p q • q - f' ∧
      b p h₁ = 0 ∧ b p h₂ = 0 ∧ b h₁ h₁ ≠ 0 ∧ b h₂ h₂ ≠ 0 ∧ b h₁ h₂ = 0 ∧
      p - b p q • q = (2⁻¹ : ZMod 5) • (h₁ + h₂) := by
  obtain ⟨f', hf'p, hf'e, hf'f'⟩ :=
    exists_perp_norm_one_of_degenerate hsym hnd hp hq hqp hqp' hβ
  have hpe : b p (p - b p q • q) = 0 := degenerate_perp_left hp hβ
  have hee : b (p - b p q • q) (p - b p q • q) = 0 := degenerate_isotropic hsym hp hq hβ
  have hef' : b (p - b p q • q) f' = 1 := by
    rw [hsym]
    exact hf'e
  refine ⟨f', p - b p q • q + f', p - b p q • q - f', hf'p, hf'e, hf'f', rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.BilinForm.add_right, hpe, hsym p f', hf'p, add_zero]
  · rw [LinearMap.BilinForm.sub_right, hpe, hsym p f', hf'p, sub_zero]
  · have h : b (p - b p q • q + f') (p - b p q • q + f') = 2 := by
      rw [norm_add, hee, hef', hf'e, hf'f']
      ring
    rw [h]
    decide
  · have h : b (p - b p q • q - f') (p - b p q • q - f') = -2 := by
      rw [norm_sub, hee, hef', hf'e, hf'f']
      ring
    rw [h]
    decide
  · rw [norm_add_sub, hee, hef', hf'e, hf'f']
    ring
  · rw [show p - b p q • q + f' + (p - b p q • q - f') =
        (p - b p q • q) + (p - b p q • q) by abel,
      ← two_smul (R := ZMod 5) (x := p - b p q • q), smul_smul,
      inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]

private theorem perp_component_left {p q : Fin n → ZMod 5} (hp : b p p = 1) :
    b p (q - b p q • p) = 0 := by
  simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hp]
  ring

private theorem perp_component_norm (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) :
    b (q - b p q • p) (q - b p q • p) = 1 - b p q * b p q := by
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hp, hq, hsym q p]
  ring

private theorem perp_component_right {p q x : Fin n → ZMod 5} (hxp : b x p = 0) :
    b x (q - b p q • p) = b x q := by
  rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hxp]
  ring

private theorem family_orthogonalization {k : ℕ} {v : Fin k → Fin n → ZMod 5}
    (hsym : ∀ x y, b x y = b y x)
    (horth : ∀ i j, i ≠ j → b (v i) (v j) = 0) (hanis : ∀ i, b (v i) (v i) ≠ 0)
    {w₁ u : Fin n → ZMod 5} (hw₁ : b w₁ w₁ = 1) (hw₁v : ∀ i, b w₁ (v i) = 0)
    (huw₁ : b u w₁ = 0) (hu : ∀ w, b w w = 1 → (∀ i, b w (v i) = 0) → b u w = 0)
    (x : Fin n → ZMod 5) :
    ∃ x', x' = x - ∑ i, (b x (v i) * (b (v i) (v i))⁻¹) • v i - b x w₁ • w₁ ∧
      (∀ i, b x' (v i) = 0) ∧ b x' w₁ = 0 ∧ b u x' = 0 := by
  have key : ∀ a : ZMod 5, ∃ l m : ZMod 5, m ≠ 0 ∧ l * l + m * m * a = 1 := by decide
  obtain ⟨x', hx'⟩ : ∃ x', x' = x - ∑ i, (b x (v i) * (b (v i) (v i))⁻¹) • v i - b x w₁ • w₁ :=
    ⟨_, rfl⟩
  have hx'v : ∀ j, b x' (v j) = 0 := by
    intro j
    rw [hx', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sum_left,
      Finset.sum_eq_single j (fun i _ hij => by
        rw [LinearMap.BilinForm.smul_left, horth i j hij, mul_zero])
        (fun h => absurd (Finset.mem_univ j) h),
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left, mul_assoc,
      inv_mul_cancel₀ (hanis j), mul_one, hw₁v j]
    ring
  have hx'w₁ : b x' w₁ = 0 := by
    rw [hx', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sum_left,
      Finset.sum_eq_zero (fun i _ => by
        rw [LinearMap.BilinForm.smul_left, hsym (v i) w₁, hw₁v i, mul_zero]),
      LinearMap.BilinForm.smul_left, hw₁]
    ring
  have hux' : b u x' = 0 := by
    obtain ⟨l, m, hm, hlm⟩ := key (b x' x')
    have hw₁x' : b w₁ x' = 0 := by
      rw [hsym]
      exact hx'w₁
    have h1 : b (l • w₁ + m • x') (l • w₁ + m • x') = 1 := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw₁, hx'w₁, hw₁x',
        mul_one, mul_zero, add_zero]
      linear_combination hlm
    have h2 : ∀ i, b (l • w₁ + m • x') (v i) = 0 := by
      intro i
      rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_left, hw₁v i, hx'v i]
      ring
    have h := hu (l • w₁ + m • x') h1 h2
    rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.smul_right, huw₁, mul_zero, zero_add] at h
    exact (mul_eq_zero.1 h).resolve_left hm
  exact ⟨x', hx', hx'v, hx'w₁, hux'⟩

private theorem eq_zero_of_forall_norm_one_perp_of_family {k : ℕ} {v : Fin k → Fin n → ZMod 5}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (horth : ∀ i j, i ≠ j → b (v i) (v j) = 0) (hanis : ∀ i, b (v i) (v i) ≠ 0)
    {w₁ u : Fin n → ZMod 5} (hw₁ : b w₁ w₁ = 1) (hw₁v : ∀ i, b w₁ (v i) = 0)
    (huv : ∀ i, b u (v i) = 0) (huw₁ : b u w₁ = 0)
    (hu : ∀ w, b w w = 1 → (∀ i, b w (v i) = 0) → b u w = 0) : u = 0 := by
  refine hnd u ?_
  intro x
  obtain ⟨x', hx', hx'v, hx'w₁, hux'⟩ :=
    family_orthogonalization hsym horth hanis hw₁ hw₁v huw₁ hu x
  have hsum : b u (∑ i, (b x (v i) * (b (v i) (v i))⁻¹) • v i) = 0 := by
    rw [LinearMap.BilinForm.sum_right]
    exact Finset.sum_eq_zero (fun i _ => by
      rw [LinearMap.BilinForm.smul_right, huv i, mul_zero])
  have hx : x = x' + (∑ i, (b x (v i) * (b (v i) (v i))⁻¹) • v i) + b x w₁ • w₁ := by
    rw [hx']
    abel
  rw [hx, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, hsum,
    LinearMap.BilinForm.smul_right, huw₁, mul_zero, hux']
  ring

theorem eq_zero_of_forall_norm_one_perp_pair (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v₁ v₂ u : Fin n → ZMod 5}
    (h₁ : b v₁ v₁ ≠ 0) (h₂ : b v₂ v₂ ≠ 0) (h₁₂ : b v₁ v₂ = 0)
    (hu₁ : b u v₁ = 0) (hu₂ : b u v₂ = 0)
    (hu : ∀ w, b w w = 1 → b w v₁ = 0 → b w v₂ = 0 → b u w = 0) : u = 0 := by
  have h₂₁ : b v₂ v₁ = 0 := by rw [hsym]; exact h₁₂
  obtain ⟨z, hz₁, hz₂, hzz⟩ := exists_aniso_perp₂ hsym hnd (by omega) h₁ h₂ h₁₂
  obtain ⟨w₁, hw₁v₁, hw₁v₂, -, hw₁⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn h₁ h₂ hzz h₁₂
      (by rw [hsym]; exact hz₁) (by rw [hsym]; exact hz₂) (c := 1)
  refine eq_zero_of_forall_norm_one_perp_of_family hsym hnd (v := ![v₁, v₂]) ?_ ?_ hw₁ ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h₁₂
    · simpa using h₂₁
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · simpa using h₁
    · simpa using h₂
  · intro i
    fin_cases i
    · simpa using hw₁v₁
    · simpa using hw₁v₂
  · intro i
    fin_cases i
    · simpa using hu₁
    · simpa using hu₂
  · simpa using hu w₁ hw₁ hw₁v₁ hw₁v₂
  · intro w hw hwv
    exact hu w hw (by simpa using hwv 0) (by simpa using hwv 1)

theorem eq_zero_of_forall_norm_one_perp_triple (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v₁ v₂ v₃ u : Fin n → ZMod 5}
    (h₁ : b v₁ v₁ ≠ 0) (h₂ : b v₂ v₂ ≠ 0) (h₃ : b v₃ v₃ ≠ 0) (h₁₂ : b v₁ v₂ = 0)
    (h₁₃ : b v₁ v₃ = 0) (h₂₃ : b v₂ v₃ = 0)
    (hu₁ : b u v₁ = 0) (hu₂ : b u v₂ = 0) (hu₃ : b u v₃ = 0)
    (hu : ∀ w, b w w = 1 → b w v₁ = 0 → b w v₂ = 0 → b w v₃ = 0 → b u w = 0) : u = 0 := by
  have h₂₁ : b v₂ v₁ = 0 := by rw [hsym]; exact h₁₂
  have h₃₁ : b v₃ v₁ = 0 := by rw [hsym]; exact h₁₃
  have h₃₂ : b v₃ v₂ = 0 := by rw [hsym]; exact h₂₃
  obtain ⟨w₁, hw₁v₁, hw₁v₂, hw₁v₃, hw₁⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (c := 1)
  refine eq_zero_of_forall_norm_one_perp_of_family hsym hnd (v := ![v₁, v₂, v₃]) ?_ ?_ hw₁ ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h₁₂
    · simpa using h₁₃
    · simpa using h₂₁
    · exact absurd rfl hij
    · simpa using h₂₃
    · simpa using h₃₁
    · simpa using h₃₂
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · simpa using h₁
    · simpa using h₂
    · simpa using h₃
  · intro i
    fin_cases i
    · simpa using hw₁v₁
    · simpa using hw₁v₂
    · simpa using hw₁v₃
  · intro i
    fin_cases i
    · simpa using hu₁
    · simpa using hu₂
    · simpa using hu₃
  · simpa using hu w₁ hw₁ hw₁v₁ hw₁v₂ hw₁v₃
  · intro w hw hwv
    exact hu w hw (by simpa using hwv 0) (by simpa using hwv 1) (by simpa using hwv 2)

private theorem exists_norm_one_pairing_one (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p : Fin n → ZMod 5} (hp : b p p = 1) :
    ∃ q, b q q = 1 ∧ b p q = 1 ∧ q ≠ p ∧ q ≠ -p := by
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  obtain ⟨s₁, hs₁p, hs₁⟩ :=
    exists_norm_eq_perp hsym hnd (by omega) (v := p) hp0 (c := 1) one_ne_zero
  have hs₁0 : b s₁ s₁ ≠ 0 := by rw [hs₁]; decide
  obtain ⟨z, hzp, hzs₁, hzz⟩ :=
    exists_aniso_perp₂ hsym hnd (by omega) (u₁ := p) (u₂ := s₁) hp0 hs₁0
      (by rw [hsym]; exact hs₁p)
  obtain ⟨s₂, hs₂p, hs₂s₁, -, hs₂⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := p) (u₂ := s₁) (u₃ := z) hp0 hs₁0 hzz
      (by rw [hsym]; exact hs₁p) (by rw [hsym]; exact hzp) (by rw [hsym]; exact hzs₁) (c := 4)
  have hs₁s₂ : b s₁ s₂ = 0 := by rw [hsym]; exact hs₂s₁
  have hps : b p (s₁ + s₂) = 0 := by
    simp only [LinearMap.BilinForm.add_right, hsym p s₁, hsym p s₂, hs₁p, hs₂p, add_zero]
  have hsp : b (s₁ + s₂) p = 0 := by
    rw [hsym]
    exact hps
  have hss : b (s₁ + s₂) (s₁ + s₂) = 0 := by
    rw [norm_add, hs₁, hs₁s₂, hs₂s₁, hs₂]
    decide
  have hs₁q : b s₁ (p + (s₁ + s₂)) = 1 := by
    simp only [LinearMap.BilinForm.add_right, hs₁p, hs₁, hs₁s₂, add_zero, zero_add]
  have hs₁neg : b s₁ (-p) = 0 := by
    rw [LinearMap.BilinForm.neg_right, hs₁p, neg_zero]
  refine ⟨p + (s₁ + s₂), ?_, ?_, ?_, ?_⟩
  · rw [norm_add, hp, hps, hsp, hss]
    ring
  · rw [LinearMap.BilinForm.add_right, hp, hps, add_zero]
  · intro h
    rw [h, hs₁p] at hs₁q
    exact absurd hs₁q (by decide)
  · intro h
    rw [h, hs₁neg] at hs₁q
    exact absurd hs₁q (by decide)

private theorem eq_pair_of_sub_eq_zero {p q x : Fin n → ZMod 5} {l m : ZMod 5}
    (h : x - l • p - m • q = 0) : x = l • p + m • q := by
  calc x = (x - l • p - m • q) + (l • p + m • q) := by abel
    _ = l • p + m • q := by rw [h, zero_add]

private theorem eq_pair_of_sub_perp_eq_zero {p q x f' : Fin n → ZMod 5}
    (h : x - b x p • p - b x f' • (p - b p q • q) = 0) :
    ∃ l m : ZMod 5, x = l • p + m • q := by
  refine ⟨b x p + b x f', -((b x f') * b p q), ?_⟩
  calc x = (x - b x p • p - b x f' • (p - b p q • q)) +
        (b x p • p + b x f' • (p - b p q • q)) := by abel
    _ = b x p • p + b x f' • (p - b p q • q) := by rw [h, zero_add]
    _ = (b x p + b x f') • p + (-((b x f') * b p q)) • q := by
          rw [smul_sub, smul_smul, add_smul, neg_smul]
          abel

theorem exists_norm_one_perp_pair (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q : Fin n → ZMod 5} (hp : b p p = 1)
    (hq : b q q = 1) (hqp : q ≠ p) (hqp' : q ≠ -p) :
    ∃ y, b y y = 1 ∧ b y p = 0 ∧ b y q = 0 := by
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  by_cases hβ : b p q * b p q = 1
  ·
    obtain ⟨f', h₁, h₂, -, -, -, -, -, hp₁, hp₂, h₁₁, h₂₂, h₁₂, he⟩ :=
      exists_frame_of_degenerate hsym hnd hp hq hqp hqp' hβ
    obtain ⟨y, hyp, hy₁, hy₂, hyy⟩ :=
      RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := p) (u₂ := h₁) (u₃ := h₂) hp0 h₁₁ h₂₂
        hp₁ hp₂ h₁₂ (c := 1)
    have hye : b y (p - b p q • q) = 0 := by
      rw [he, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.add_right, hy₁, hy₂]
      ring
    have hq_eq : q = b p q • (p - (p - b p q • q)) := by
      rw [show p - (p - b p q • q) = b p q • q by abel, smul_smul, hβ, one_smul]
    refine ⟨y, hyy, hyp, ?_⟩
    rw [hq_eq, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.sub_right, hyp, hye]
    ring
  ·
    obtain ⟨q', hq'⟩ : ∃ q', q' = q - b p q • p := ⟨_, rfl⟩
    have hpq' : b p q' = 0 := by rw [hq']; exact perp_component_left hp
    have hq'0 : b q' q' ≠ 0 := by
      rw [hq', perp_component_norm hsym hp hq]
      intro h
      exact hβ (sub_eq_zero.1 h).symm
    obtain ⟨z, hz₁, hz₂, hzz⟩ :=
      exists_aniso_perp₂ hsym hnd (by omega) (u₁ := p) (u₂ := q') hp0 hq'0 hpq'
    obtain ⟨y, hyp, hyq', -, hyy⟩ :=
      RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := p) (u₂ := q') (u₃ := z) hp0 hq'0 hzz
        hpq' (by rw [hsym]; exact hz₁) (by rw [hsym]; exact hz₂) (c := 1)
    refine ⟨y, hyy, hyp, ?_⟩
    have hqq : q = q' + b p q • p := by rw [hq']; abel
    rw [hqq, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hyq', hyp]
    ring

private theorem exists_norm_two_perp_of_sq_ne_one (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hβ : b p q * b p q ≠ 1) (hx : b x x = 1)
    (hxp : b x p = 0) (hxq : b x q = 0) :
    ∃ a, b a p = 0 ∧ b a q = 0 ∧ b a x = 0 ∧ b a a = 2 := by
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  obtain ⟨q', hq'⟩ : ∃ q', q' = q - b p q • p := ⟨_, rfl⟩
  have hpq' : b p q' = 0 := by rw [hq']; exact perp_component_left hp
  have hq'q' : b q' q' = 1 - b p q * b p q := by
    rw [hq']
    exact perp_component_norm hsym hp hq
  have hq'0 : b q' q' ≠ 0 := by
    rw [hq'q']
    intro h
    exact hβ (sub_eq_zero.1 h).symm
  have hxq' : b x q' = 0 := by
    rw [hq', perp_component_right hxp]
    exact hxq
  have hx0 : b x x ≠ 0 := by rw [hx]; decide
  obtain ⟨a, hap, haq', hax, haa⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := p) (u₂ := q') (u₃ := x) hp0 hq'0 hx0
      hpq' (by rw [hsym]; exact hxp) (by rw [hsym]; exact hxq') (c := 2)
  have hqq : q = q' + b p q • p := by rw [hq']; abel
  have haq : b a q = 0 := by
    rw [hqq, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, haq', hap]
    ring
  exact ⟨a, hap, haq, hax, haa⟩

private theorem exists_perp_pair_not_perp_of_sq_eq_one (hsym : ∀ x y, b x y = b y x)
    {p q x : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1) (hqp : q ≠ p)
    (hqp' : q ≠ -p) (hβ : b p q * b p q = 1) (hx : b x x = 1) (hxp : b x p = 0)
    (hxq : b x q = 0) :
    ∃ y, b y y = 1 ∧ b y p = 0 ∧ b y q = 0 ∧ b x y ≠ 0 ∧ y ≠ x ∧ y ≠ -x := by
  have hpe : b p (p - b p q • q) = 0 := degenerate_perp_left hp hβ
  have hep : b (p - b p q • q) p = 0 := degenerate_perp_right hsym hp hβ
  have hee : b (p - b p q • q) (p - b p q • q) = 0 := degenerate_isotropic hsym hp hq hβ
  have heq : b (p - b p q • q) q = 0 := degenerate_perp_q hq
  have hxe : b x (p - b p q • q) = 0 := by
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hxq, hxp]
    ring
  have hex : b (p - b p q • q) x = 0 := by
    rw [hsym]
    exact hxe
  have he0 : p - b p q • q ≠ 0 := sub_smul_self_ne_zero hp hq hqp hqp'
  refine ⟨x + (p - b p q • q), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hx, hxe, hee, hex]
    ring
  · rw [LinearMap.BilinForm.add_left, hxp, hep, add_zero]
  · rw [LinearMap.BilinForm.add_left, hxq, heq, add_zero]
  · intro h
    simp only [LinearMap.BilinForm.add_right, hx, hxe, add_zero] at h
    exact absurd h (by decide)
  · intro h
    have h1 : p - b p q • q = 0 := by
      have := congrArg (fun z => z - x) h
      simpa using this
    exact he0 h1
  · intro h
    have h1 : b x (x + (p - b p q • q)) = b x (-x) := by rw [h]
    simp only [LinearMap.BilinForm.add_right, hx, hxe, LinearMap.BilinForm.neg_right, hx] at h1
    revert h1
    decide

private theorem exists_perp_pair_not_perp_of_sq_ne_one (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hβ : b p q * b p q ≠ 1) (hx : b x x = 1)
    (hxp : b x p = 0) (hxq : b x q = 0) :
    ∃ y, b y y = 1 ∧ b y p = 0 ∧ b y q = 0 ∧ b x y ≠ 0 ∧ y ≠ x ∧ y ≠ -x := by
  obtain ⟨a, hap, haq, hax, haa⟩ :=
    exists_norm_two_perp_of_sq_ne_one hsym hnd hn hp hq hβ hx hxp hxq
  have hxa : b x a = 0 := by rw [hsym]; exact hax
  have hya : b ((2 : ZMod 5) • x + a) q = 0 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxq, haq, mul_zero,
      zero_add]
  have hxya : b x ((2 : ZMod 5) • x + a) = 2 := by
    rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hx, hxa]
    ring
  have h2x : b ((2 : ZMod 5) • x) ((2 : ZMod 5) • x) = 4 := by
    rw [norm_smul, hx]
    ring
  have h2a : b ((2 : ZMod 5) • x) a = 0 := by
    rw [LinearMap.BilinForm.smul_left, hxa, mul_zero]
  have ha2 : b a ((2 : ZMod 5) • x) = 0 := by
    rw [LinearMap.BilinForm.smul_right, hax, mul_zero]
  refine ⟨(2 : ZMod 5) • x + a, ?_, ?_, hya, ?_, ?_, ?_⟩
  · rw [norm_add, h2x, h2a, ha2, haa]
    decide
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxp, hap, mul_zero,
      zero_add]
  · rw [hxya]
    decide
  · intro h
    rw [h] at hxya
    rw [hx] at hxya
    revert hxya
    decide
  · intro h
    rw [h] at hxya
    rw [LinearMap.BilinForm.neg_right, hx] at hxya
    revert hxya
    decide

theorem exists_perp_pair_not_perp (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) (hqp : q ≠ p) (hqp' : q ≠ -p)
    (hx : b x x = 1) (hxp : b x p = 0) (hxq : b x q = 0) :
    ∃ y, b y y = 1 ∧ b y p = 0 ∧ b y q = 0 ∧ b x y ≠ 0 ∧ y ≠ x ∧ y ≠ -x := by
  by_cases hβ : b p q * b p q = 1
  · exact exists_perp_pair_not_perp_of_sq_eq_one hsym hp hq hqp hqp' hβ hx hxp hxq
  · exact exists_perp_pair_not_perp_of_sq_ne_one hsym hnd hn hp hq hβ hx hxp hxq

private theorem exists_gram_coefficients (hsym : ∀ x y, b x y = b y x) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hβ : b p q * b p q ≠ 1) :
    ∃ l m : ZMod 5, b (x - l • p - m • q) p = 0 ∧ b (x - l • p - m • q) q = 0 := by
  have hD0 : 1 - b p q * b p q ≠ 0 := by
    intro h
    exact hβ (sub_eq_zero.1 h).symm
  have hD0' : 1 - (b p q) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact hD0
  obtain ⟨l, hl⟩ : ∃ l, l = (b x p - b p q * b x q) * (1 - b p q * b p q)⁻¹ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = (b x q - b p q * b x p) * (1 - b p q * b p q)⁻¹ := ⟨_, rfl⟩
  refine ⟨l, m, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hp, hsym q p, hl, hm]
    field_simp [hD0']
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hq, hl, hm]
    field_simp [hD0']
    ring

private theorem exists_degenerate_frame_and_perp (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hqp : q ≠ p) (hqp' : q ≠ -p)
    (hx : ∀ y, b y y = 1 → b y p = 0 → b y q = 0 → b x y = 0)
    (hβ : b p q * b p q = 1) :
    ∃ f' h₁ h₂ : Fin n → ZMod 5,
      b f' p = 0 ∧ b f' (p - b p q • q) = 1 ∧ b f' f' = 0 ∧
      h₁ = p - b p q • q + f' ∧ h₂ = p - b p q • q - f' ∧
      b p h₁ = 0 ∧ b p h₂ = 0 ∧ b h₁ h₁ ≠ 0 ∧ b h₂ h₂ ≠ 0 ∧ b h₁ h₂ = 0 ∧
      p - b p q • q = (2⁻¹ : ZMod 5) • (h₁ + h₂) ∧ b x (p - b p q • q) = 0 := by
  obtain ⟨y₀, hy₀, hy₀p, hy₀q⟩ := exists_norm_one_perp_pair hsym hnd hn hp hq hqp hqp'
  have hee : b (p - b p q • q) (p - b p q • q) = 0 := degenerate_isotropic hsym hp hq hβ
  have hep : b (p - b p q • q) p = 0 := degenerate_perp_right hsym hp hβ
  have heq : b (p - b p q • q) q = 0 := degenerate_perp_q hq
  have hy₀e : b y₀ (p - b p q • q) = 0 := by
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hy₀q, hy₀p]
    ring
  have hy₀ep : b (p - b p q • q) y₀ = 0 := by
    rw [hsym]
    exact hy₀e
  have h1mem : b (y₀ + (p - b p q • q)) (y₀ + (p - b p q • q)) = 1 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hy₀, hy₀e, hee,
      hy₀ep]
    ring
  have h1p : b (y₀ + (p - b p q • q)) p = 0 := by
    rw [LinearMap.BilinForm.add_left, hy₀p, hep, add_zero]
  have h1q : b (y₀ + (p - b p q • q)) q = 0 := by
    rw [LinearMap.BilinForm.add_left, hy₀q, heq, add_zero]
  have hxe : b x (p - b p q • q) = 0 := by
    have h0 := hx y₀ hy₀ hy₀p hy₀q
    have h1 := hx (y₀ + (p - b p q • q)) h1mem h1p h1q
    rw [LinearMap.BilinForm.add_right, h0, zero_add] at h1
    exact h1
  obtain ⟨f', h₁, h₂, hf'p, hf'e, hf'f', h₁eq, h₂eq, hp₁, hp₂, h₁₁, h₂₂, h₁₂, he⟩ :=
    exists_frame_of_degenerate hsym hnd hp hq hqp hqp' hβ
  exact ⟨f', h₁, h₂, hf'p, hf'e, hf'f', h₁eq, h₂eq, hp₁, hp₂, h₁₁, h₂₂, h₁₂, he, hxe⟩

private theorem mem_pair_of_forall_perp_of_sq_eq_one (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) (hqp : q ≠ p) (hqp' : q ≠ -p)
    (hx : ∀ y, b y y = 1 → b y p = 0 → b y q = 0 → b x y = 0)
    (hβ : b p q * b p q = 1) : ∃ l m : ZMod 5, x = l • p + m • q := by
  obtain ⟨f', h₁, h₂, hf'p, hf'e, hf'f', h₁eq, h₂eq, hp₁, hp₂, h₁₁, h₂₂, h₁₂, he, hxe⟩ :=
    exists_degenerate_frame_and_perp hsym hnd hn hp hq hqp hqp' hx hβ
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  have hpe : b p (p - b p q • q) = 0 := degenerate_perp_left hp hβ
  have hep : b (p - b p q • q) p = 0 := degenerate_perp_right hsym hp hβ
  have hee : b (p - b p q • q) (p - b p q • q) = 0 := degenerate_isotropic hsym hp hq hβ
  have hex : b (p - b p q • q) f' = 1 := by
    rw [hsym]
    exact hf'e
  have hf'p' : b p f' = 0 := by rw [hsym]; exact hf'p
  obtain ⟨x'', hx''⟩ : ∃ x'', x'' = x - b x p • p - b x f' • (p - b p q • q) := ⟨_, rfl⟩
  have hx''p : b x'' p = 0 := by
    simp only [hx'', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hp, hep,
      hf'p, mul_zero, mul_one, sub_zero, sub_self]
  have hx''e : b x'' (p - b p q • q) = 0 := by
    simp only [hx'', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hpe, hee,
      hxe, hf'e, mul_zero, mul_one, sub_zero, sub_self]
  have hx''f' : b x'' f' = 0 := by
    simp only [hx'', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hf'p', hex,
      mul_zero, mul_one, sub_zero, sub_self]
  have hx''h₁ : b x'' h₁ = 0 := by
    rw [h₁eq, LinearMap.BilinForm.add_right, hx''e, hx''f', add_zero]
  have hx''h₂ : b x'' h₂ = 0 := by
    rw [h₂eq, LinearMap.BilinForm.sub_right, hx''e, hx''f', sub_zero]
  have hq_eq : q = b p q • (p - (p - b p q • q)) := by
    rw [show p - (p - b p q • q) = b p q • q by abel, smul_smul, hβ, one_smul]
  have hxhyp : ∀ y, b y y = 1 → b y p = 0 → b y h₁ = 0 → b y h₂ = 0 → b x'' y = 0 := by
    intro y hy hyp hy₁ hy₂
    have hye : b y (p - b p q • q) = 0 := by
      rw [he, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.add_right, hy₁, hy₂]
      ring
    have hyq : b y q = 0 := by
      rw [hq_eq, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.sub_right, hyp, hye]
      ring
    have h0 := hx y hy hyp hyq
    have hyp' : b p y = 0 := by rw [hsym]; exact hyp
    have hye' : b (p - b p q • q) y = 0 := by
      rw [hsym]
      exact hye
    simp only [hx'', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, hyp', hye', h0, mul_zero, sub_zero, sub_self]
  have hx''0 : x'' = 0 :=
    eq_zero_of_forall_norm_one_perp_triple hsym hnd hn hp0 h₁₁ h₂₂ hp₁ hp₂ h₁₂ hx''p hx''h₁
      hx''h₂ hxhyp
  exact eq_pair_of_sub_perp_eq_zero (by rw [← hx'']; exact hx''0)

private theorem mem_pair_of_forall_perp_of_sq_ne_one (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) (hqp : q ≠ p) (hqp' : q ≠ -p)
    (hx : ∀ y, b y y = 1 → b y p = 0 → b y q = 0 → b x y = 0)
    (hβ : b p q * b p q ≠ 1) : ∃ l m : ZMod 5, x = l • p + m • q := by
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  obtain ⟨q', hq'⟩ : ∃ q', q' = q - b p q • p := ⟨_, rfl⟩
  have hpq' : b p q' = 0 := by rw [hq']; exact perp_component_left hp
  have hq'0 : b q' q' ≠ 0 := by
    rw [hq', perp_component_norm hsym hp hq]
    intro h
    exact hβ (sub_eq_zero.1 h).symm
  obtain ⟨l, m, hx'p, hx'q⟩ := exists_gram_coefficients hsym hp hq hβ
  obtain ⟨x', hx'⟩ : ∃ x', x' = x - l • p - m • q := ⟨_, rfl⟩
  have hx'p' : b x' p = 0 := by rw [hx']; exact hx'p
  have hx'q' : b x' q = 0 := by rw [hx']; exact hx'q
  have hx'q'' : b x' q' = 0 := by
    rw [hq', perp_component_right hx'p']
    exact hx'q'
  have hxhyp : ∀ y, b y y = 1 → b y p = 0 → b y q' = 0 → b x' y = 0 := by
    intro y hy hyp hyq'
    have hyq : b y q = 0 := by
      have hqq : q = q' + b p q • p := by rw [hq']; abel
      rw [hqq, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hyq', hyp]
      ring
    have h0 := hx y hy hyp hyq
    have hyp' : b p y = 0 := by rw [hsym]; exact hyp
    have hyq'ry : b q y = 0 := by rw [hsym]; exact hyq
    simp only [hx', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, hyp', hyq'ry, h0, mul_zero, sub_zero, sub_self]
  have hx'0 : x' = 0 :=
    eq_zero_of_forall_norm_one_perp_pair hsym hnd hn hp0 hq'0 hpq' hx'p' hx'q'' hxhyp
  exact ⟨l, m, eq_pair_of_sub_eq_zero (by rw [← hx']; exact hx'0)⟩

theorem mem_pair_of_forall_perp (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) (hqp : q ≠ p) (hqp' : q ≠ -p)
    (hx : ∀ y, b y y = 1 → b y p = 0 → b y q = 0 → b x y = 0) :
    ∃ l m : ZMod 5, x = l • p + m • q := by
  by_cases hβ : b p q * b p q = 1
  · exact mem_pair_of_forall_perp_of_sq_eq_one hsym hnd hn hp hq hpq0 hqp hqp' hx hβ
  · exact mem_pair_of_forall_perp_of_sq_ne_one hsym hnd hn hp hq hpq0 hqp hqp' hx hβ

private theorem exists_norm_one_pairing_zero (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p : Fin n → ZMod 5}
    (hp : b p p = 1) : ∃ q, b q q = 1 ∧ b p q = 0 ∧ q ≠ p ∧ q ≠ -p := by
  have hp0 : b p p ≠ 0 := by rw [hp]; decide
  obtain ⟨q, hqp, hq⟩ :=
    exists_norm_eq_perp hsym hnd (by omega) (v := p) hp0 (c := 1) one_ne_zero
  have hpq : b p q = 0 := by rw [hsym]; exact hqp
  refine ⟨q, hq, hpq, ?_, ?_⟩
  · intro h
    rw [h, hp] at hpq
    exact absurd hpq (by decide)
  · intro h
    rw [h, LinearMap.BilinForm.neg_right, hp] at hpq
    exact absurd hpq (by decide)

private theorem exists_norm_one_pairing_two (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p : Fin n → ZMod 5}
    (hp : b p p = 1) : ∃ q, b q q = 1 ∧ b p q = 2 ∧ q ≠ p ∧ q ≠ -p := by
  obtain ⟨q, hq, hqp2⟩ := RootBlockFive.exists_pairing_two hsym hnd (by omega) hp
  have hpq : b p q = 2 := by rw [hsym]; exact hqp2
  refine ⟨q, hq, hpq, ?_, ?_⟩
  · intro h
    rw [h, hp] at hpq
    revert hpq
    decide
  · intro h
    rw [h, LinearMap.BilinForm.neg_right, hp] at hpq
    revert hpq
    decide

private theorem exists_norm_one_pairing_three (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p : Fin n → ZMod 5}
    (hp : b p p = 1) : ∃ q, b q q = 1 ∧ b p q = 3 ∧ q ≠ p ∧ q ≠ -p := by
  obtain ⟨z, hz, hzp⟩ := RootBlockFive.exists_pairing_two hsym hnd (by omega) hp
  have hpz : b p z = 2 := by rw [hsym]; exact hzp
  refine ⟨-z, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, hz, neg_neg]
  · rw [LinearMap.BilinForm.neg_right, hpz]
    decide
  · intro h
    have h1 : b p (-z) = b p p := by rw [h]
    rw [LinearMap.BilinForm.neg_right, hpz, hp] at h1
    revert h1
    decide
  · intro h
    have h1 : b p (-z) = b p (-p) := by rw [h]
    rw [LinearMap.BilinForm.neg_right, hpz, LinearMap.BilinForm.neg_right, hp] at h1
    revert h1
    decide

private theorem exists_norm_one_pairing_four (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p : Fin n → ZMod 5}
    (hp : b p p = 1) : ∃ q, b q q = 1 ∧ b p q = 4 ∧ q ≠ p ∧ q ≠ -p := by
  obtain ⟨q, hq, hpq, hqp, hqp'⟩ := exists_norm_one_pairing_one hsym hnd hn hp
  refine ⟨-q, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, hq, neg_neg]
  · rw [LinearMap.BilinForm.neg_right, hpq]
    decide
  · intro h
    apply hqp'
    have h' := congrArg Neg.neg h
    simpa using h'
  · intro h
    apply hqp
    have h' := congrArg Neg.neg h
    simpa using h'

theorem exists_norm_one_pairing (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {p : Fin n → ZMod 5} (hp : b p p = 1)
    (c : ZMod 5) : ∃ q, b q q = 1 ∧ b p q = c ∧ q ≠ p ∧ q ≠ -p := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
    revert c
    decide
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact exists_norm_one_pairing_zero hsym hnd hn hp
  · exact exists_norm_one_pairing_one hsym hnd hn hp
  · exact exists_norm_one_pairing_two hsym hnd hn hp
  · exact exists_norm_one_pairing_three hsym hnd hn hp
  · exact exists_norm_one_pairing_four hsym hnd hn hp

end FivePlane

end CFSG.OddTranspositions.PartFour

