module

public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace FiveRigid

open TableE1Five

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem sq_eq_sq_or_neg {a c : ZMod 5} (h : a * a = c * c) : a = c ∨ a = -c := by
  revert a c
  decide

private theorem mul_self_eq_one_or {c : ZMod 5} (h : c * c = 1) : c = 1 ∨ c = -1 := by
  revert c
  decide

private theorem gram_sign_fact : ∀ A B c d : ZMod 5, A ≠ 0 → B ≠ 0 → d * d = c * c →
    (A - 2 * c * B) * (A - 2 * c * B) = (A - 2 * d * B) * (A - 2 * d * B) → d = c := by
  decide

private theorem sub_eq_zero_or {a c : ZMod 5} (ha : a * a = 1) (hc : c * c = 1) :
    a - c = 0 ∨ a - c = 2 ∨ a - c = 3 := by
  revert a c
  decide

private theorem kappa_zero_fact {x c β : ZMod 5} (hx : x = 0 ∨ x = 2 ∨ x = 3)
    (hc : c * c = 1) (hβ : β ≠ 0) (h : x * x + 4 * x * c * β * β = 0) : x = 0 := by
  revert x c β
  decide

private theorem mul_self_smul {c x : ZMod 5} (h : c * c = 1) : (c * x) * (c * x) = x * x := by
  have h' : (c * x) * (c * x) = (c * c) * (x * x) := by ring
  rw [h', h, one_mul]

private theorem inv_mul_sq {e k : ZMod 5} (he : e ≠ 0) (h : e * e = k * k) :
    (e⁻¹ * k) * (e⁻¹ * k) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h' : (e⁻¹ * k) * (e⁻¹ * k) = (e * e)⁻¹ * (k * k) := by
    rw [mul_inv]
    ring
  rw [h', ← h, inv_mul_cancel₀ (mul_ne_zero he he)]

section Gram

open Module

variable {ι κ : Type*}

private theorem isometry_of_gram_basis {F G : ι → Fin n → ZMod 5}
    {B : Module.Basis κ (ZMod 5) (Fin n → ZMod 5)} {e : κ → ι}
    (hF : ∀ k, F (e k) = B k) (hgram : ∀ i j, b (F i) (F j) = b (G i) (G j))
    {φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)} (hφ : ∀ k, φ (B k) = G (e k)) :
    ∀ x y, b (φ x) (φ y) = b x y := by
  have hbasis : ∀ w : κ, ∀ y, b (φ (B w)) (φ y) = b (B w) y := by
    intro w y
    have h1 : (b (φ (B w))).comp φ = b (B w) := by
      refine B.ext fun z => ?_
      simp only [LinearMap.comp_apply]
      rw [hφ w, hφ z, ← hF w, ← hF z]
      exact (hgram _ _).symm
    exact LinearMap.congr_fun h1 y
  intro x y
  have h2 : (b.flip (φ y)).comp φ = b.flip y := by
    refine B.ext fun z => ?_
    simpa only [LinearMap.comp_apply, LinearMap.BilinForm.flip_apply] using hbasis z y
  simpa only [LinearMap.comp_apply, LinearMap.BilinForm.flip_apply] using LinearMap.congr_fun h2 x

private theorem values_of_gram_basis {F G : ι → Fin n → ZMod 5}
    {B : Module.Basis κ (ZMod 5) (Fin n → ZMod 5)} {e : κ → ι}
    (hF : ∀ k, F (e k) = B k) (hgram : ∀ i j, b (F i) (F j) = b (G i) (G j))
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hiso : ∀ x y, b (φ x) (φ y) = b x y) (hφ : ∀ k, φ (B k) = G (e k)) :
    ∀ i, φ (F i) = G i := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hGy : ∀ j y, b (G j) (φ y) = b (F j) y := by
    intro j y
    have hlin : (b (G j)).comp φ = b (F j) := by
      refine B.ext fun z => ?_
      simp only [LinearMap.comp_apply]
      rw [hφ z, ← hF z]
      exact (hgram j _).symm
    exact LinearMap.congr_fun hlin y
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hzero : x - y = 0 := by
      apply hnd
      intro z
      rw [← hiso (x - y) z, map_sub, hxy, sub_self]
      simp
    exact sub_eq_zero.1 hzero
  have hsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.1 hinj
  intro j
  have hz : φ (F j) - G j = 0 := by
    apply hnd
    intro y
    obtain ⟨w, rfl⟩ := hsurj y
    rw [LinearMap.BilinForm.sub_left, hiso (F j) w, hGy j w, sub_self]
  exact sub_eq_zero.1 hz

private theorem exists_linearMap_of_gram {F G : ι → Fin n → ZMod 5}
    (hspan : Submodule.span (ZMod 5) (Set.range F) = ⊤)
    (hgram : ∀ i j, b (F i) (F j) = b (G i) (G j))
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5),
      (∀ i, φ (F i) = G i) ∧ ∀ x y, b (φ x) (φ y) = b x y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  classical
  obtain ⟨s, hs_sub, hspan_s, hli⟩ := exists_linearIndependent (K := ZMod 5) (t := Set.range F)
  have hspan_s' : Submodule.span (ZMod 5) s = ⊤ := by rw [hspan_s, hspan]
  let B : Module.Basis s (ZMod 5) (Fin n → ZMod 5) :=
    Module.Basis.mk hli (by simpa using hspan_s'.ge)
  have hB : ∀ x : s, B x = (x : Fin n → ZMod 5) := fun x => Module.Basis.mk_apply hli _ x
  let e : s → ι := fun x => Classical.choose (hs_sub x.2)
  have he : ∀ x : s, F (e x) = B x := fun x => by
    rw [hB]
    exact Classical.choose_spec (hs_sub x.2)
  let φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5) := B.constr (ZMod 5) fun x => G (e x)
  have hφ : ∀ x : s, φ (B x) = G (e x) := fun x =>
    Module.Basis.constr_basis B (ZMod 5) (fun x => G (e x)) x
  exact ⟨φ, values_of_gram_basis he hgram hnd (isometry_of_gram_basis he hgram hφ) hφ,
    isometry_of_gram_basis he hgram hφ⟩

end Gram

private theorem exists_gl_of_isometry {φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hiso : ∀ x y, b (φ x) (φ y) = b x y) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ g : GL (Fin n) (ZMod 5), (∀ x, act g x = φ x) ∧ g ∈ isomGroup b := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hzero : x - y = 0 := by
      apply hnd
      intro z
      rw [← hiso (x - y) z, map_sub, hxy, sub_self]
      simp
    exact sub_eq_zero.1 hzero
  have hbij : Function.Bijective φ := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  let e : (Fin n → ZMod 5) ≃ₗ[ZMod 5] (Fin n → ZMod 5) := LinearEquiv.ofBijective φ hbij
  let g : GL (Fin n) (ZMod 5) :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hgact : ∀ x, act g x = φ x := by
    intro x
    have h1 : Matrix.GeneralLinearGroup.toLin g = LinearMap.GeneralLinearGroup.ofLinearEquiv e := by
      simp [g]
    have h2 : (Matrix.GeneralLinearGroup.toLin g :
        (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)) = e.toLinearMap := by
      rw [h1]
      rfl
    calc act g x = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) (ZMod 5)) x := by
          rw [act, Matrix.mulVecLin_apply]
      _ = (Matrix.GeneralLinearGroup.toLin g : (Fin n → ZMod 5) →ₗ[ZMod 5]
            (Fin n → ZMod 5)) x := (Matrix.GeneralLinearGroup.toLin_apply g x).symm
      _ = e.toLinearMap x := by rw [h2]
      _ = φ x := rfl
  refine ⟨g, hgact, ?_⟩
  rw [mem_isomGroup]
  intro x y
  rw [hgact, hgact, hiso]

variable {α : Type*} {S : Set α} {f g : α → Fin n → ZMod 5}

private theorem exists_mem_S (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 3 ≤ n) {v : Fin n → ZMod 5}
    (hv : b v v = 1) (hf : ∀ x ∈ S, b (f x) (f x) = 1 ∧ b (f x) v = 0)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y) :
    ∃ x₀ ∈ S, b (f x₀) (f x₀) = 1 ∧ b (f x₀) v = 0 := by
  have hv0 : b v v ≠ 0 := by rw [hv]; decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hyv, hyy⟩ := exists_norm_eq_perp hsym hnd hn (v := v) hv0 (c := 1) one_ne_zero
  obtain ⟨x₀, hx₀S, -⟩ := hsurj y hyy hyv
  exact ⟨x₀, hx₀S, (hf x₀ hx₀S).1, (hf x₀ hx₀S).2⟩

private def signOf (x₀ x : α) : ZMod 5 :=
  if b (g x) (g x₀) = b (f x) (f x₀) then 1 else -1

private theorem signOf_sq (x₀ x : α) :
    signOf (b := b) (f := f) (g := g) x₀ x * signOf (b := b) (f := f) (g := g) x₀ x = 1 := by
  unfold signOf
  split_ifs <;> decide

private theorem signOf_spec (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    {x₀ : α} (hx₀ : x₀ ∈ S) {x : α} (hx : x ∈ S) :
    b (g x) (g x₀) = signOf (b := b) (f := f) (g := g) x₀ x * b (f x) (f x₀) := by
  have h := hsq x hx x₀ hx₀
  rw [pow_two, pow_two] at h
  have h' : b (g x) (g x₀) = b (f x) (f x₀) ∨ b (g x) (g x₀) = -b (f x) (f x₀) :=
    sq_eq_sq_or_neg h.symm
  unfold signOf
  by_cases hc : b (g x) (g x₀) = b (f x) (f x₀)
  · rw [if_pos hc, one_mul, hc]
  · rw [if_neg hc, neg_one_mul]
    rcases h' with h' | h'
    · exact absurd h' hc
    · rw [h']

private theorem sq_of_eq_or_neg {s w : ZMod 5} (h : s = w ∨ s = -w) : s * s = w * w := by
  obtain rfl | rfl := h
  · ring
  · ring

private theorem b_act_refl {a c a₀ : Fin n → ZMod 5} (ha : b a a = 1) :
    b (act (refl b a) c) a₀ = b c a₀ - 2 * b c a * b a a₀ := by
  rw [act_refl ha, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  ring

private theorem norm_add_add_two_smul (hsym : ∀ x y, b x y = b y x) {a c d : Fin n → ZMod 5}
    (ha : b a a = 1) (hc : b c c = 1) (hd : b d d = 1) (hac : b a c = 0) (had : b a d = 0)
    (hcd : b c d = 0) : b (a + c + (2 : ZMod 5) • d) (a + c + (2 : ZMod 5) • d) = 1 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, ha, hc, hd, hac,
    hsym c a, had, hsym d a, hcd, hsym d c]
  decide

private theorem pairing_add_add_two_smul (hsym : ∀ x y, b x y = b y x) {a c d : Fin n → ZMod 5}
    (ha : b a a = 1) (hac : b a c = 0) (had : b a d = 0) :
    b (a + c + (2 : ZMod 5) • d) a = 1 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, ha, hac, hsym c a,
    had, hsym d a]
  decide

private theorem exists_norm_one_perp_ne_ne (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {v w₁ w₂ : Fin n → ZMod 5}
    (hv : b v v = 1) (hw₁ : b w₁ w₁ = 1) (hw₂ : b w₂ w₂ = 1) (hw₁v : b w₁ v = 0)
    (hw₂v : b w₂ v = 0) (hw₁w₂ : b w₁ w₂ = 0) :
    ∃ x, b x x = 1 ∧ b x v = 0 ∧ b x w₁ ≠ 0 ∧ b x w₂ ≠ 0 := by
  obtain ⟨z, hzv, hzw₁, hzw₂, hzz⟩ := exists_aniso_perp₃ hsym hnd hn
    (by rw [hv]; decide) (by rw [hw₁]; decide) (by rw [hw₂]; decide)
    (by rw [hsym]; exact hw₁v) (by rw [hsym]; exact hw₂v) hw₁w₂
  have key : ∀ β : ZMod 5, β ≠ 0 → ∃ α γ δ : ZMod 5, α ≠ 0 ∧ γ ≠ 0 ∧
      α * α + γ * γ + δ * δ * β = 1 := by decide
  obtain ⟨α, γ, δ, hα, hγ, hsum⟩ := key _ hzz
  refine ⟨α • w₁ + γ • w₂ + δ • z, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw₁, hw₂, hw₁w₂,
      hsym w₂ w₁, hzw₁, hzw₂, hsym w₁ z, hsym w₂ z]
    linear_combination hsum
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₁v, hw₂v, hzv]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₁, hsym w₂ w₁,
      hw₁w₂, hzw₁]
    rw [show α * 1 + γ * 0 + δ * 0 = α by ring]
    exact hα
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₂, hw₁w₂, hzw₂]
    rw [show α * 0 + γ * 1 + δ * 0 = γ by ring]
    exact hγ

private theorem b_add_add_two_smul_eq_zero (hsym : ∀ x y, b x y = b y x)
    {v a z t w : Fin n → ZMod 5}
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    (hwN : ∀ x ∈ S, b (f x) a ≠ 0 → b w (f x) = 0)
    (ha : b a a = 1) (hz : b z z = 1) (ht : b t t = 1)
    (hav : b a v = 0) (hzv : b z v = 0) (htv : b t v = 0)
    (haz : b a z = 0) (hat : b a t = 0) (hzt : b z t = 0) :
    b w (a + z + (2 : ZMod 5) • t) = 0 := by
  have hp_norm : b (a + z + (2 : ZMod 5) • t) (a + z + (2 : ZMod 5) • t) = 1 :=
    norm_add_add_two_smul hsym ha hz ht haz hat hzt
  have hp_v : b (a + z + (2 : ZMod 5) • t) v = 0 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hav, hzv, htv]
    ring
  have hp_pair : b (a + z + (2 : ZMod 5) • t) a = 1 :=
    pairing_add_add_two_smul hsym ha haz hat
  obtain ⟨x₂, hx₂S, hx₂⟩ := hsurj _ hp_norm hp_v
  have hx₂N : b (f x₂) a ≠ 0 := by
    rcases hx₂ with h | h
    · rw [h, hp_pair]; decide
    · rw [h, LinearMap.BilinForm.neg_left, hp_pair]; decide
  have h := hwN x₂ hx₂S hx₂N
  rcases hx₂ with h' | h'
  · rwa [h'] at h
  · rw [h', LinearMap.BilinForm.neg_right] at h
    exact neg_eq_zero.1 h

private theorem b_eq_zero_of_perp_base (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v w : Fin n → ZMod 5}
    (hv : b v v = 1)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    {x₀ : α} (hfx₀ : b (f x₀) (f x₀) = 1) (hfx₀v : b (f x₀) v = 0)
    (hwN : ∀ x ∈ S, b (f x) (f x₀) ≠ 0 → b w (f x) = 0)
    {z : Fin n → ZMod 5} (hzz : b z z = 1) (hzv : b z v = 0)
    (hz₀ : b z (f x₀) = 0) : b w z = 0 := by
  obtain ⟨t, htv, hta, htz, htt⟩ := RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn
    (by rw [hv]; decide) (by rw [hfx₀]; decide) (by rw [hzz]; decide)
    (by rw [hsym]; exact hfx₀v) (by rw [hsym]; exact hzv) (by rw [hsym]; exact hz₀) (c := 1)
  have hta' : b (f x₀) t = 0 := by rw [hsym]; exact hta
  have htz' : b z t = 0 := by rw [hsym]; exact htz
  have hz₀' : b (f x₀) z = 0 := by rw [hsym]; exact hz₀
  have hp : b w (f x₀ + z + (2 : ZMod 5) • t) = 0 :=
    b_add_add_two_smul_eq_zero hsym hsurj hwN hfx₀ hzz htt hfx₀v hzv htv hz₀' hta' htz'
  have hm : b w (f x₀ + (-z) + (2 : ZMod 5) • t) = 0 := by
    refine b_add_add_two_smul_eq_zero hsym hsurj hwN hfx₀ ?_ htt hfx₀v ?_ htv ?_ hta' ?_
    · rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, hzz]; decide
    · rw [LinearMap.BilinForm.neg_left, hzv, neg_zero]
    · rw [LinearMap.BilinForm.neg_right, hz₀', neg_zero]
    · rw [LinearMap.BilinForm.neg_left, htz', neg_zero]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.neg_right] at hp hm
  have h3 : (2 : ZMod 5) * b w z = 0 := by linear_combination hp - hm
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact (mul_eq_zero.1 h3).resolve_left h2ne

private theorem eq_zero_of_orthogonal_family (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v : Fin n → ZMod 5}
    (hv : b v v = 1)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    {x₀ : α} (hfx₀ : b (f x₀) (f x₀) = 1) (hfx₀v : b (f x₀) v = 0)
    {w : Fin n → ZMod 5} (hwv : b w v = 0)
    (hwN : ∀ x ∈ S, b (f x) (f x₀) ≠ 0 → b w (f x) = 0) : w = 0 := by
  refine eq_zero_of_forall_norm_one_perp hsym hnd (by omega) hv ?_ ?_
  · exact hwv
  · intro z hzz hzv
    by_cases hz₀ : b z (f x₀) = 0
    · exact b_eq_zero_of_perp_base hsym hnd hn hv hsurj hfx₀ hfx₀v hwN hzz hzv hz₀
    ·
      obtain ⟨x₁, hx₁S, hx₁⟩ := hsurj z hzz hzv
      have hx₁N : b (f x₁) (f x₀) ≠ 0 := by
        rcases hx₁ with h | h
        · rwa [h]
        · rw [h, LinearMap.BilinForm.neg_left]; exact neg_ne_zero.mpr hz₀
      have h := hwN x₁ hx₁S hx₁N
      rcases hx₁ with h' | h'
      · rwa [h'] at h
      · rw [h', LinearMap.BilinForm.neg_right] at h
        exact neg_eq_zero.1 h

private theorem norm_identity {κ σ τ' γ β : ZMod 5} (hσ : σ * σ = 1) (hτ' : τ' * τ' = 1)
    (hγ : γ * γ = β * β) :
    κ * (κ * 1 + 2 * σ * τ' * γ * γ) + 2 * σ * τ' * γ * (κ * γ + 2 * σ * τ' * γ * 1) =
      κ * κ + 4 * κ * (σ * τ') * (β * β) + 4 * (β * β) := by
  revert κ σ τ' γ β
  decide

private theorem kappa_eq_zero_of_relation (hsym : ∀ x y, b x y = b y x)
    {X Y Z : Fin n → ZMod 5} {τ τ' σ σ' κ β γ : ZMod 5}
    (hτ : τ * τ = 1) (hτ' : τ' * τ' = 1) (hσ : σ * σ = 1) (hσ' : σ' * σ' = 1)
    (hβ : β ≠ 0) (hγ : γ * γ = β * β) (hYZ : b Y Z = γ)
    (hX : b X X = 1) (hY : b Y Y = 1) (hZ : b Z Z = 1)
    (hκ : κ = τ * σ' - σ * τ')
    (hrel : (2 * τ * β) • X = κ • Y + (2 * σ * τ' * γ) • Z) : κ = 0 := by
  have hZY : b Z Y = γ := by rw [hsym]; exact hYZ
  have hnorm1 : b ((2 * τ * β) • X) ((2 * τ * β) • X) = 4 * (β * β) := by
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hX]
    rw [show (2 * τ * β) * ((2 * τ * β) * 1) = 4 * (τ * τ) * (β * β) by ring, hτ]
    ring
  have hnorm2 : b (κ • Y + (2 * σ * τ' * γ) • Z) (κ • Y + (2 * σ * τ' * γ) • Z) =
      κ * κ + 4 * κ * (σ * τ') * (β * β) + 4 * (β * β) := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hY, hZ, hYZ, hZY]
    exact norm_identity hσ hτ' hγ
  have hkey : κ * κ + 4 * κ * (σ * τ') * β * β = 0 := by
    have h1 : b (κ • Y + (2 * σ * τ' * γ) • Z) (κ • Y + (2 * σ * τ' * γ) • Z) = 4 * (β * β) := by
      rw [← hrel]
      exact hnorm1
    rw [hnorm2] at h1
    linear_combination h1
  have hκ3 : κ = 0 ∨ κ = 2 ∨ κ = 3 := by
    rw [hκ]
    refine sub_eq_zero_or ?_ ?_
    · rw [show (τ * σ') * (τ * σ') = (τ * τ) * (σ' * σ') by ring, hτ, hσ', one_mul]
    · rw [show (σ * τ') * (σ * τ') = (σ * σ) * (τ' * τ') by ring, hσ, hτ', one_mul]
  refine kappa_zero_fact hκ3 ?_ hβ hkey
  rw [show (σ * τ') * (σ * τ') = (σ * σ) * (τ' * τ') by ring, hσ, hτ', one_mul]

private theorem eq_or_neg_of_relation (hsym : ∀ x y, b x y = b y x)
    {X Y Z : Fin n → ZMod 5} {τ τ' σ σ' κ β γ : ZMod 5}
    (hτ : τ * τ = 1) (hτ' : τ' * τ' = 1) (hσ : σ * σ = 1) (hσ' : σ' * σ' = 1)
    (hβ : β ≠ 0) (hγ : γ * γ = β * β) (hYZ : b Y Z = γ)
    (hX : b X X = 1) (hY : b Y Y = 1) (hZ : b Z Z = 1)
    (hκ : κ = τ * σ' - σ * τ')
    (hrel : (2 * τ * β) • X = κ • Y + (2 * σ * τ' * γ) • Z) :
    Z = X ∨ Z = -X := by
  have hκ0 : κ = 0 :=
    kappa_eq_zero_of_relation hsym hτ hτ' hσ hσ' hβ hγ hYZ hX hY hZ hκ hrel
  have hrel' : (2 * τ * β) • X = (2 * σ * τ' * γ) • Z := by rw [hκ0] at hrel; simpa using hrel
  have hτ0 : τ ≠ 0 := by rintro rfl; exact absurd hτ (by decide)
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have he : (2 * τ * β) ≠ 0 := mul_ne_zero (mul_ne_zero h2ne hτ0) hβ
  have hXZ : X = ((2 * τ * β)⁻¹ * (2 * σ * τ' * γ)) • Z := by
    have h := congrArg (fun v => (2 * τ * β)⁻¹ • v) hrel'
    rw [smul_smul, smul_smul, inv_mul_cancel₀ he, one_smul] at h
    simpa using h
  have hlam : ((2 * τ * β)⁻¹ * (2 * σ * τ' * γ)) * ((2 * τ * β)⁻¹ * (2 * σ * τ' * γ)) = 1 := by
    refine inv_mul_sq he ?_
    have h1 : (2 * τ * β) * (2 * τ * β) = 4 * (β * β) := by
      rw [show (2 * τ * β) * (2 * τ * β) = 4 * (τ * τ) * (β * β) by ring, hτ]
      ring
    have h2 : (2 * σ * τ' * γ) * (2 * σ * τ' * γ) = 4 * (β * β) := by
      rw [show (2 * σ * τ' * γ) * (2 * σ * τ' * γ) = 4 * (σ * σ) * (τ' * τ') * (γ * γ) by
        ring, hσ, hτ', hγ]
      ring
    rw [h1, h2]
  rcases mul_self_eq_one_or hlam with h | h
  · left
    rw [h, one_smul] at hXZ
    exact hXZ.symm
  · right
    rw [h, neg_one_smul] at hXZ
    rw [hXZ, neg_neg]

private theorem off_N_exists_data (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v : Fin n → ZMod 5}
    (hv : b v v = 1) (hf : ∀ x ∈ S, b (f x) (f x) = 1 ∧ b (f x) v = 0)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    {x₀ : α} (hfx₀ : b (f x₀) (f x₀) = 1) (hfx₀v : b (f x₀) v = 0)
    {φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hφN : ∀ z ∈ S, b (f z) (f x₀) ≠ 0 →
      φ (f z) = signOf (b := b) (f := f) (g := g) x₀ z • g z)
    {x : α} (hxS : x ∈ S) (hB0 : b (f x) (f x₀) = 0) :
    ∃ (y₁ u : α) (τ τ' σu σ₁ : ZMod 5),
      y₁ ∈ S ∧ b (f y₁) (f x) ≠ 0 ∧
      τ * τ = 1 ∧ τ' * τ' = 1 ∧ σu * σu = 1 ∧ σ₁ * σ₁ = 1 ∧
      f u = τ • act (refl b (f x)) (f y₁) ∧
      g u = τ' • act (refl b (g x)) (g y₁) ∧
      φ (f u) = σu • g u ∧ φ (f y₁) = σ₁ • g y₁ := by
  have hfx : b (f x) (f x) = 1 := (hf x hxS).1
  obtain ⟨t, htt, htv, hta, htz⟩ := exists_norm_one_perp_ne_ne hsym hnd (by omega) hv hfx₀ hfx
    hfx₀v (hf x hxS).2 (by rw [hsym]; exact hB0)
  obtain ⟨y₁, hy₁S, hy₁⟩ := hsurj t htt htv
  have hy₁N : b (f y₁) (f x₀) ≠ 0 := by
    rcases hy₁ with h | h
    · rw [h]; exact hta
    · rw [h, LinearMap.BilinForm.neg_left]; exact neg_ne_zero.mpr hta
  have hβ : b (f y₁) (f x) ≠ 0 := by
    rcases hy₁ with h | h
    · rw [h]; exact htz
    · rw [h, LinearMap.BilinForm.neg_left]; exact neg_ne_zero.mpr htz
  obtain ⟨u, huS, hfu, hgu⟩ := hconj x hxS y₁ hy₁S
  have huN : b (f u) (f x₀) ≠ 0 := by
    have hw : b (act (refl b (f x)) (f y₁)) (f x₀)
        = b (f y₁) (f x₀) - 2 * b (f y₁) (f x) * b (f x) (f x₀) := b_act_refl hfx
    rcases hfu with h | h
    · rw [h, hw, hB0, mul_zero, sub_zero]; exact hy₁N
    · rw [h, LinearMap.BilinForm.neg_left, hw, hB0, mul_zero, sub_zero]
      exact neg_ne_zero.mpr hy₁N
  obtain ⟨τ, hτ, hτeq⟩ : ∃ τ : ZMod 5, τ * τ = 1 ∧ f u = τ • act (refl b (f x)) (f y₁) := by
    rcases hfu with h | h
    · exact ⟨1, by decide, by rw [h, one_smul]⟩
    · exact ⟨-1, by decide, by rw [h, neg_one_smul]⟩
  obtain ⟨τ', hτ', hτ'eq⟩ : ∃ τ' : ZMod 5, τ' * τ' = 1 ∧
      g u = τ' • act (refl b (g x)) (g y₁) := by
    rcases hgu with h | h
    · exact ⟨1, by decide, by rw [h, one_smul]⟩
    · exact ⟨-1, by decide, by rw [h, neg_one_smul]⟩
  exact ⟨y₁, u, τ, τ', signOf (b := b) (f := f) (g := g) x₀ u,
    signOf (b := b) (f := f) (g := g) x₀ y₁, hy₁S, hβ, hτ, hτ',
    signOf_sq (b := b) (f := f) (g := g) x₀ u,
    signOf_sq (b := b) (f := f) (g := g) x₀ y₁, hτeq, hτ'eq,
    hφN u huS huN, hφN y₁ hy₁S hy₁N⟩

private theorem off_N_relation {x y₁ u : α} {τ τ' σu σ₁ : ZMod 5}
    {φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hfx : b (f x) (f x) = 1) (hgx : b (g x) (g x) = 1)
    (hτeq : f u = τ • act (refl b (f x)) (f y₁))
    (hτ'eq : g u = τ' • act (refl b (g x)) (g y₁))
    (hu_spec : φ (f u) = σu • g u) (hy_spec : φ (f y₁) = σ₁ • g y₁) :
    (2 * τ * b (f y₁) (f x)) • φ (f x) =
      (τ * σ₁ - σu * τ') • g y₁ + (2 * σu * τ' * b (g y₁) (g x)) • g x := by
  have hL : φ (f u) = (τ * σ₁) • g y₁ + (-2 * (τ * b (f y₁) (f x))) • φ (f x) := by
    rw [hτeq, map_smul, act_refl hfx, map_add, map_smul, hy_spec]
    module
  have hR : φ (f u) = (σu * τ') • g y₁ + (-2 * (σu * τ' * b (g y₁) (g x))) • g x := by
    rw [hu_spec, hτ'eq]
    rw [← mul_smul]
    rw [act_refl hgx]
    rw [smul_add]
    rw [← mul_smul]
    module
  have hsum : (τ * σ₁) • g y₁ + (-2 * (τ * b (f y₁) (f x))) • φ (f x)
      = (σu * τ') • g y₁ + (-2 * (σu * τ' * b (g y₁) (g x))) • g x := by
    rw [← hL, hR]
  linear_combination (norm := module) -hsum

private theorem off_N_eq_or_neg (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v : Fin n → ZMod 5}
    (hv : b v v = 1) (hf : ∀ x ∈ S, b (f x) (f x) = 1 ∧ b (f x) v = 0)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    {x₀ : α} (hfx₀ : b (f x₀) (f x₀) = 1) (hfx₀v : b (f x₀) v = 0)
    {φ : (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hφiso : ∀ a c, b (φ a) (φ c) = b a c)
    (hφN : ∀ z ∈ S, b (f z) (f x₀) ≠ 0 →
      φ (f z) = signOf (b := b) (f := f) (g := g) x₀ z • g z)
    {x : α} (hxS : x ∈ S) (hB0 : b (f x) (f x₀) = 0) :
    g x = φ (f x) ∨ g x = -φ (f x) := by
  have hfx : b (f x) (f x) = 1 := (hf x hxS).1
  have hgx : b (g x) (g x) = 1 := hg x hxS
  obtain ⟨y₁, u, τ, τ', σu, σ₁, hy₁S, hβ, hτ, hτ', hσu1, hσ11, hτeq, hτ'eq,
    hu_spec, hy_spec⟩ :=
    off_N_exists_data hsym hnd hn hv hf hsurj hconj hfx₀ hfx₀v hφN hxS hB0
  have hrel := off_N_relation hfx hgx hτeq hτ'eq hu_spec hy_spec
  have hγ : b (g y₁) (g x) * b (g y₁) (g x) = b (f y₁) (f x) * b (f y₁) (f x) := by
    have h := hsq y₁ hy₁S x hxS
    rw [pow_two, pow_two] at h
    exact h.symm
  have hX : b (φ (f x)) (φ (f x)) = 1 := by rw [hφiso, hfx]
  exact eq_or_neg_of_relation hsym (X := φ (f x)) (Y := g y₁) (Z := g x) (τ := τ) (τ' := τ')
    (σ := σu) (σ' := σ₁) (κ := τ * σ₁ - σu * τ') (β := b (f y₁) (f x))
    (γ := b (g y₁) (g x)) hτ hτ' hσu1 hσ11 hβ hγ rfl hX (hg y₁ hy₁S) hgx rfl hrel

private theorem gram_on_N_sq_pairing (hsym : ∀ x y, b x y = b y x)
    (hf : ∀ x ∈ S, b (f x) (f x) = 1)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    {x₀ : α} (hx₀ : x₀ ∈ S)
    {x : α} (hxS : x ∈ S) {y : α} (hyS : y ∈ S) :
    (b (f y) (f x₀) - 2 * b (f x) (f y) * b (f x) (f x₀)) *
        (b (f y) (f x₀) - 2 * b (f x) (f y) * b (f x) (f x₀)) =
      (signOf (b := b) (f := f) (g := g) x₀ y * b (f y) (f x₀) -
          2 * b (g x) (g y) *
            (signOf (b := b) (f := f) (g := g) x₀ x * b (f x) (f x₀))) *
        (signOf (b := b) (f := f) (g := g) x₀ y * b (f y) (f x₀) -
          2 * b (g x) (g y) *
            (signOf (b := b) (f := f) (g := g) x₀ x * b (f x) (f x₀))) := by
  obtain ⟨u, huS, hfu, hgu⟩ := hconj x hxS y hyS
  have hfx : b (f x) (f x) = 1 := hf x hxS
  have hgx : b (g x) (g x) = 1 := hg x hxS
  set σx : ZMod 5 := signOf (b := b) (f := f) (g := g) x₀ x with hσx
  set σy : ZMod 5 := signOf (b := b) (f := f) (g := g) x₀ y with hσy
  set A : ZMod 5 := b (f y) (f x₀) with hA
  set B : ZMod 5 := b (f x) (f x₀) with hB
  set c : ZMod 5 := b (f x) (f y) with hc
  set c' : ZMod 5 := b (g x) (g y) with hc'
  have hx_spec : b (g x) (g x₀) = σx * B := signOf_spec hsq hx₀ hxS
  have hy_spec : b (g y) (g x₀) = σy * A := signOf_spec hsq hx₀ hyS
  have hf1 : b (f u) (f x₀) * b (f u) (f x₀) = (A - 2 * c * B) * (A - 2 * c * B) := by
    have h' : b (f u) (f x₀) = b (act (refl b (f x)) (f y)) (f x₀) ∨
        b (f u) (f x₀) = -b (act (refl b (f x)) (f y)) (f x₀) := by
      rcases hfu with h | h
      · left; rw [h]
      · right; rw [h, LinearMap.BilinForm.neg_left]
    rw [sq_of_eq_or_neg h', b_act_refl hfx, hsym (f y) (f x), ← hc, ← hA, ← hB]
  have hg1 : b (g u) (g x₀) * b (g u) (g x₀) =
      (σy * A - 2 * c' * (σx * B)) * (σy * A - 2 * c' * (σx * B)) := by
    have h' : b (g u) (g x₀) = b (act (refl b (g x)) (g y)) (g x₀) ∨
        b (g u) (g x₀) = -b (act (refl b (g x)) (g y)) (g x₀) := by
      rcases hgu with h | h
      · left; rw [h]
      · right; rw [h, LinearMap.BilinForm.neg_left]
    rw [sq_of_eq_or_neg h', b_act_refl hgx, hsym (g y) (g x), ← hc', hy_spec, hx_spec]
  have hsq_u : b (f u) (f x₀) * b (f u) (f x₀) = b (g u) (g x₀) * b (g u) (g x₀) := by
    have h := hsq u huS x₀ hx₀
    rw [pow_two, pow_two] at h
    exact h
  rw [hf1, hg1] at hsq_u
  simpa only [← hσx, ← hσy, ← hA, ← hB, ← hc, ← hc'] using hsq_u

private theorem gram_on_N_sq {x₀ : α}
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    {x y : α} (hxS : x ∈ S) (hyS : y ∈ S) :
    (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) *
        (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) =
      b (f x) (f y) * b (f x) (f y) := by
  have hσx1 : signOf (b := b) (f := f) (g := g) x₀ x *
      signOf (b := b) (f := f) (g := g) x₀ x = 1 := signOf_sq x₀ x
  have hσy1 : signOf (b := b) (f := f) (g := g) x₀ y *
      signOf (b := b) (f := f) (g := g) x₀ y = 1 := signOf_sq x₀ y
  have hc'sq : b (g x) (g y) * b (g x) (g y) = b (f x) (f y) * b (f x) (f y) := by
    have h := hsq x hxS y hyS
    rw [pow_two, pow_two] at h
    exact h.symm
  have h3 : (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) *
        (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) =
      (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ x) *
        (signOf (b := b) (f := f) (g := g) x₀ y *
          signOf (b := b) (f := f) (g := g) x₀ y) *
        (b (g x) (g y) * b (g x) (g y)) := by ring
  rw [h3, hσx1, hσy1, hc'sq]
  ring

private theorem gram_on_N_step (hsym : ∀ x y, b x y = b y x)
    (hf : ∀ x ∈ S, b (f x) (f x) = 1)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    {x₀ : α} (hx₀ : x₀ ∈ S)
    {x : α} (hxS : x ∈ S) {y : α} (hyS : y ∈ S) :
    (b (f y) (f x₀) - 2 * b (f x) (f y) * b (f x) (f x₀)) *
        (b (f y) (f x₀) - 2 * b (f x) (f y) * b (f x) (f x₀)) =
      (b (f y) (f x₀) - 2 * (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) * b (f x) (f x₀)) *
        (b (f y) (f x₀) - 2 * (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) * b (f x) (f x₀)) := by
  have hsq_u := gram_on_N_sq_pairing hsym hf hg hconj hsq hx₀ hxS hyS
  have hσy1 : signOf (b := b) (f := f) (g := g) x₀ y *
      signOf (b := b) (f := f) (g := g) x₀ y = 1 := signOf_sq x₀ y
  rw [hsq_u]
  have hfac : signOf (b := b) (f := f) (g := g) x₀ y * b (f y) (f x₀) -
        2 * b (g x) (g y) *
          (signOf (b := b) (f := f) (g := g) x₀ x * b (f x) (f x₀)) =
      signOf (b := b) (f := f) (g := g) x₀ y *
        (b (f y) (f x₀) - 2 * (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) *
            b (f x) (f x₀)) := by
    calc signOf (b := b) (f := f) (g := g) x₀ y * b (f y) (f x₀) -
          2 * b (g x) (g y) *
            (signOf (b := b) (f := f) (g := g) x₀ x * b (f x) (f x₀))
        = signOf (b := b) (f := f) (g := g) x₀ y * b (f y) (f x₀) -
            2 * (signOf (b := b) (f := f) (g := g) x₀ x *
              (signOf (b := b) (f := f) (g := g) x₀ y *
                signOf (b := b) (f := f) (g := g) x₀ y) * b (g x) (g y)) *
              b (f x) (f x₀) := by rw [hσy1]; ring
      _ = signOf (b := b) (f := f) (g := g) x₀ y *
            (b (f y) (f x₀) - 2 * (signOf (b := b) (f := f) (g := g) x₀ x *
              signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) *
                b (f x) (f x₀)) := by ring
  rw [hfac, mul_self_smul hσy1]

private theorem gram_on_N (hsym : ∀ x y, b x y = b y x)
    (hf : ∀ x ∈ S, b (f x) (f x) = 1)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    {x₀ : α} (hx₀ : x₀ ∈ S)
    {x : α} (hxS : x ∈ S) (hxB : b (f x) (f x₀) ≠ 0)
    {y : α} (hyS : y ∈ S) (hyB : b (f y) (f x₀) ≠ 0) :
    b (g x) (g y) = signOf (b := b) (f := f) (g := g) x₀ x *
      signOf (b := b) (f := f) (g := g) x₀ y * b (f x) (f y) := by
  have hd := gram_on_N_sq (x₀ := x₀) hsq hxS hyS
  have hstep := gram_on_N_step hsym hf hg hconj hsq hx₀ hxS hyS
  have hmain : signOf (b := b) (f := f) (g := g) x₀ x *
      signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y) = b (f x) (f y) :=
    gram_sign_fact (b (f y) (f x₀)) (b (f x) (f x₀)) (b (f x) (f y))
      (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) hyB hxB hd hstep
  have hσx1 : signOf (b := b) (f := f) (g := g) x₀ x *
      signOf (b := b) (f := f) (g := g) x₀ x = 1 := signOf_sq x₀ x
  have hσy1 : signOf (b := b) (f := f) (g := g) x₀ y *
      signOf (b := b) (f := f) (g := g) x₀ y = 1 := signOf_sq x₀ y
  have hσ2 : (signOf (b := b) (f := f) (g := g) x₀ x *
      signOf (b := b) (f := f) (g := g) x₀ y) *
      (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y) = 1 := by
    have h3 : (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y) *
          (signOf (b := b) (f := f) (g := g) x₀ x *
            signOf (b := b) (f := f) (g := g) x₀ y) =
        (signOf (b := b) (f := f) (g := g) x₀ x *
            signOf (b := b) (f := f) (g := g) x₀ x) *
          (signOf (b := b) (f := f) (g := g) x₀ y *
            signOf (b := b) (f := f) (g := g) x₀ y) := by ring
    rw [h3, hσx1, hσy1, one_mul]
  calc b (g x) (g y) = (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y) *
        (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y) * b (g x) (g y) := by rw [hσ2, one_mul]
    _ = (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y) *
        (signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ y * b (g x) (g y)) := by ring
    _ = (signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y) * b (f x) (f y) := by rw [hmain]
    _ = signOf (b := b) (f := f) (g := g) x₀ x *
        signOf (b := b) (f := f) (g := g) x₀ y * b (f x) (f y) := by ring

private theorem signOf_mul_sq {x₀ x y : α} :
    (signOf (b := b) (f := f) (g := g) x₀ x * signOf (b := b) (f := f) (g := g) x₀ y) *
      (signOf (b := b) (f := f) (g := g) x₀ x * signOf (b := b) (f := f) (g := g) x₀ y) = 1 := by
  set a := signOf (b := b) (f := f) (g := g) x₀ x with ha
  set c := signOf (b := b) (f := f) (g := g) x₀ y with hc
  have h1 : a * a = 1 := signOf_sq (b := b) (f := f) (g := g) x₀ x
  have h2 : c * c = 1 := signOf_sq (b := b) (f := f) (g := g) x₀ y
  rw [show (a * c) * (a * c) = (a * a) * (c * c) by ring, h1, h2, one_mul]

private theorem gram_option {v p : Fin n → ZMod 5} {x₀ : α}
    {F G : Option {x // x ∈ S ∧ b (f x) (f x₀) ≠ 0} → Fin n → ZMod 5}
    (hFn : F none = v) (hGn : G none = p)
    (hFs : ∀ x, F (some x) = f x.1)
    (hGs : ∀ x, G (some x) = signOf (b := b) (f := f) (g := g) x₀ x.1 • g x.1)
    (hsym : ∀ x y, b x y = b y x)
    (hf : ∀ x ∈ S, b (f x) (f x) = 1 ∧ b (f x) v = 0)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1 ∧ b (g x) p = 0)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    (hv : b v v = 1) (hp : b p p = 1) (hx₀S : x₀ ∈ S) :
    ∀ i j, b (F i) (F j) = b (G i) (G j) := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => rw [hFn, hGn, hv, hp]
    | some y =>
      rw [hFn, hFs y, hGn, hGs y, hsym v (f y.1), (hf y.1 y.2.1).2,
        LinearMap.BilinForm.smul_right, hsym p (g y.1), (hg y.1 y.2.1).2, mul_zero]
  | some x =>
    cases j with
    | none =>
      rw [hFs x, hFn, hGs x, hGn, LinearMap.BilinForm.smul_left,
        (hg x.1 x.2.1).2, (hf x.1 x.2.1).2, mul_zero]
    | some y =>
      have h4 := signOf_mul_sq (b := b) (f := f) (g := g) (x₀ := x₀) (x := x.1) (y := y.1)
      rw [hFs x, hFs y, hGs x, hGs y, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right,
        gram_on_N (b := b) hsym (fun z hz => (hf z hz).1) (fun z hz => (hg z hz).1) hconj hsq
          hx₀S x.2.1 x.2.2 y.2.1 y.2.2]
      calc b (f x.1) (f y.1) = ((signOf x₀ x.1 * signOf x₀ y.1) *
            (signOf x₀ x.1 * signOf x₀ y.1)) * b (f x.1) (f y.1) := by rw [h4, one_mul]
        _ = signOf x₀ x.1 *
            (signOf x₀ y.1 * (signOf x₀ x.1 * signOf x₀ y.1 * b (f x.1) (f y.1))) := by ring

private theorem span_option {v : Fin n → ZMod 5} {x₀ : α}
    {F : Option {x // x ∈ S ∧ b (f x) (f x₀) ≠ 0} → Fin n → ZMod 5}
    (hFn : F none = v) (hFs : ∀ x, F (some x) = f x.1)
    (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) (hv : b v v = 1)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    (hfx₀ : b (f x₀) (f x₀) = 1) (hfx₀v : b (f x₀) v = 0) :
    Submodule.span (ZMod 5) (Set.range F) = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hBnd : b.Nondegenerate :=
    ⟨hnd, fun y hy => hnd y (fun x => by rw [hsym y x]; exact hy x)⟩
  have hBref : b.IsRefl := LinearMap.BilinForm.IsSymm.isRefl ⟨hsym⟩
  have hbot : b.orthogonal (Submodule.span (ZMod 5) (Set.range F)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    refine eq_zero_of_orthogonal_family (b := b) hsym hnd hn hv hsurj hfx₀ hfx₀v ?_ ?_
    · have hmem : F none ∈ Submodule.span (ZMod 5) (Set.range F) :=
        Submodule.subset_span (Set.mem_range_self none)
      have hvw : b v w = 0 := by simpa only [hFn] using hw (F none) hmem
      rwa [hsym] at hvw
    · intro x hxS hxB
      have hxN : x ∈ S ∧ b (f x) (f x₀) ≠ 0 := ⟨hxS, hxB⟩
      have hmem : F (some (⟨x, hxN⟩ : {y : α // y ∈ S ∧ b (f y) (f x₀) ≠ 0})) ∈
          Submodule.span (ZMod 5) (Set.range F) :=
        Submodule.subset_span (Set.mem_range_self _)
      have hxw : b (f x) w = 0 := by
        have h := hw (F (some (⟨x, hxN⟩ : {y : α // y ∈ S ∧ b (f y) (f x₀) ≠ 0}))) hmem
        simpa only [hFs] using h
      rwa [hsym] at hxw
  calc Submodule.span (ZMod 5) (Set.range F)
      = b.orthogonal (b.orthogonal (Submodule.span (ZMod 5) (Set.range F))) :=
        (LinearMap.BilinForm.orthogonal_orthogonal hBnd hBref _).symm
    _ = b.orthogonal ⊥ := by rw [hbot]
    _ = ⊤ := LinearMap.BilinForm.orthogonal_bot (B := b)

theorem exists_isom_of_reflClosed (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v p : Fin n → ZMod 5}
    (hv : b v v = 1) (hp : b p p = 1) {α : Type*} {S : Set α} {f g : α → Fin n → ZMod 5}
    (hf : ∀ x ∈ S, b (f x) (f x) = 1 ∧ b (f x) v = 0)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1 ∧ b (g x) p = 0)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y))) :
    ∃ φ ∈ isomGroup b, act φ v = p ∧ ∀ x ∈ S, g x = act φ (f x) ∨ g x = -act φ (f x) := by
  classical
  obtain ⟨x₀, hx₀S, hfx₀, hfx₀v⟩ := exists_mem_S (b := b) hsym hnd (by omega) hv hf hsurj
  have hf1 : ∀ x ∈ S, b (f x) (f x) = 1 := fun x hx => (hf x hx).1
  have hg1 : ∀ x ∈ S, b (g x) (g x) = 1 := fun x hx => (hg x hx).1
  let F : Option {x // x ∈ S ∧ b (f x) (f x₀) ≠ 0} → Fin n → ZMod 5
    | none => v
    | some x => f x.1
  let G : Option {x // x ∈ S ∧ b (f x) (f x₀) ≠ 0} → Fin n → ZMod 5
    | none => p
    | some x => signOf (b := b) (f := f) (g := g) x₀ x.1 • g x.1
  have hgram : ∀ i j, b (F i) (F j) = b (G i) (G j) :=
    gram_option (v := v) (p := p) (x₀ := x₀) (F := F) (G := G) rfl rfl (fun _ => rfl)
      (fun _ => rfl) hsym hf hg hconj hsq hv hp hx₀S
  have hspan : Submodule.span (ZMod 5) (Set.range F) = ⊤ :=
    span_option (v := v) (x₀ := x₀) (F := F) rfl (fun _ => rfl) hsym hnd hn hv hsurj hfx₀ hfx₀v
  obtain ⟨φ, hφF, hφiso⟩ := exists_linearMap_of_gram (b := b) hspan hgram hnd
  obtain ⟨ψ, hψact, hψmem⟩ := exists_gl_of_isometry (b := b) hφiso hnd
  refine ⟨ψ, hψmem, ?_, ?_⟩
  · rw [hψact]
    simpa [F, G] using hφF (none : Option {x // x ∈ S ∧ b (f x) (f x₀) ≠ 0})
  · intro x hxS
    by_cases hxB : b (f x) (f x₀) = 0
    · have hres := off_N_eq_or_neg (b := b) hsym hnd hn hv hf hg1 hsurj hconj hsq hfx₀
        hfx₀v hφiso (fun z hzS hzB => hφF (some ⟨z, hzS, hzB⟩)) hxS hxB
      rcases hres with h | h
      · left; rwa [hψact]
      · right; rwa [hψact]
    · have hval := hφF (some ⟨x, hxS, hxB⟩)
      have hσ : signOf (b := b) (f := f) (g := g) x₀ x *
          signOf (b := b) (f := f) (g := g) x₀ x = 1 :=
        signOf_sq (b := b) (f := f) (g := g) x₀ x
      have hgx : g x = signOf (b := b) (f := f) (g := g) x₀ x • φ (f x) := by
        simp only [F, G] at hval
        rw [hval, ← mul_smul, hσ, one_smul]
      rcases mul_self_eq_one_or hσ with h | h
      · left; rw [hgx, h, one_smul, hψact]
      · right; rw [hgx, h, neg_one_smul, hψact]

theorem exists_perp_iff_of_reflClosed (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v p : Fin n → ZMod 5}
    (hv : b v v = 1) (hp : b p p = 1) {α : Type*} {S : Set α} {f g : α → Fin n → ZMod 5}
    (hf : ∀ x ∈ S, b (f x) (f x) = 1 ∧ b (f x) v = 0)
    (hg : ∀ x ∈ S, b (g x) (g x) = 1 ∧ b (g x) p = 0)
    (hsurj : ∀ y, b y y = 1 → b y v = 0 → ∃ x ∈ S, f x = y ∨ f x = -y)
    (hsq : ∀ x ∈ S, ∀ y ∈ S, b (f x) (f y) ^ 2 = b (g x) (g y) ^ 2)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, ∃ u ∈ S,
      (f u = act (refl b (f x)) (f y) ∨ f u = -act (refl b (f x)) (f y)) ∧
        (g u = act (refl b (g x)) (g y) ∨ g u = -act (refl b (g x)) (g y)))
    {q : Fin n → ZMod 5} (hq : b q p = 0) :
    ∃ z, b z v = 0 ∧ b z z = b q q ∧ (z = 0 ↔ q = 0) ∧
      ∀ x ∈ S, (b (f x) z = 0 ↔ b (g x) q = 0) := by
  obtain ⟨φ, hφmem, hφv, hsign⟩ :=
    exists_isom_of_reflClosed hsym hnd hn hv hp hf hg hsurj hsq hconj
  refine ⟨act φ⁻¹ q, ?_, ?_, ?_, ?_⟩
  · rw [isom_inv_left hφmem q v, hφv, hq]
  · exact isom_norm ((isomGroup b).inv_mem hφmem) q
  · constructor
    · intro hz
      calc q = act φ (act φ⁻¹ q) := (act_act_inv φ q).symm
        _ = act φ 0 := by rw [hz]
        _ = 0 := by simp [act]
    · intro hq0
      rw [hq0]
      simp [act]
  · intro x hxS
    have h1 : b (act φ (f x)) q = b (f x) (act φ⁻¹ q) := by
      rw [← hφmem (f x) (act φ⁻¹ q), act_act_inv]
    rcases hsign x hxS with h | h
    · rw [show b (g x) q = b (f x) (act φ⁻¹ q) by rw [h]; exact h1]
    · rw [show b (g x) q = -b (f x) (act φ⁻¹ q) by
        rw [h, LinearMap.BilinForm.neg_left, h1]]
      rw [neg_eq_zero]

end FiveRigid

end CFSG.OddTranspositions.PartFour
