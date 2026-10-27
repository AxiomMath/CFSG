module

public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
import CFSG.OddTranspositions.PartFour.Fourteen.FivePlanePerp
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace FiveEichler

open TableE1Five

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

@[expose] def eich (b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)) (e β y : Fin n → ZMod 5) :
    Fin n → ZMod 5 :=
  y + b y e • β - b y β • e - (3 * b β β * b y e) • e

theorem eich_zero (e y : Fin n → ZMod 5) : eich b e 0 y = y := by
  rw [eich]
  simp

theorem eich_neg (e β y : Fin n → ZMod 5) : eich b e β (-y) = -eich b e β y := by
  rw [eich, eich, LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_left]
  module

theorem eich_eich (hsym : ∀ x y, b x y = b y x) {e β β' : Fin n → ZMod 5} (he : b e e = 0)
    (hβ : b β e = 0) (hβ' : b β' e = 0) (y : Fin n → ZMod 5) :
    eich b e β (eich b e β' y) = eich b e (β + β') y := by
  simp only [eich, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.smul_left,
    hβ, hβ', he, hsym e β, hsym β' β, mul_zero, sub_zero,
    add_zero]
  have hcoef : (3 : ZMod 5) * (b β β + b β β' + (b β β' + b β' β')) * b y e =
      3 * b β β * b y e + b β β' * b y e + 3 * b β' β' * b y e := by
    generalize b β β = Q
    generalize b β β' = Q'
    generalize b β' β' = Q''
    generalize b y e = m
    revert Q Q' Q'' m
    decide
  rw [hcoef]
  module

theorem eich_isom (hsym : ∀ x y, b x y = b y x) {e β : Fin n → ZMod 5} (he : b e e = 0)
    (hβ : b β e = 0) (x y : Fin n → ZMod 5) : b (eich b e β x) (eich b e β y) = b x y := by
  simp only [eich, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hβ, he, mul_zero,
    sub_zero, add_zero, hsym e β, hsym β y, hsym e y]
  generalize b x y = u1
  generalize b x e = u2
  generalize b x β = u3
  generalize b y e = u4
  generalize b y β = u5
  generalize b β β = u6
  revert u1 u2 u3 u4 u5 u6
  decide

theorem act_refl_act_refl (hsym : ∀ x y, b x y = b y x) {p e : Fin n → ZMod 5} (hp : b p p = 1)
    (hpe : b p e = 0) (he : b e e = 0) (t : ZMod 5) (y : Fin n → ZMod 5) :
    act (refl b p) (act (refl b (p + t • e)) y) = eich b e ((2 * t) • p) y := by
  have hp' : b (p + t • e) (p + t • e) = 1 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hsym e p, hp, hpe, he,
      mul_zero, add_zero]
  rw [act_refl hp', act_refl hp, eich]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hsym e p, hp, hpe]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  generalize b y p = u1
  generalize b y e = u2
  generalize y i = u3
  generalize p i = u4
  generalize e i = u5
  clear hp'
  revert u1 u2 u3 u4 u5 t
  decide

theorem act_refl_eich (hsym : ∀ x y, b x y = b y x) {a e : Fin n → ZMod 5} (ha : b a a = 1)
    (hae : b a e = 0) (β y : Fin n → ZMod 5) :
    act (refl b a) (eich b e β (act (refl b a) y)) = eich b e (act (refl b a) β) y := by
  have hea : b e a = 0 := by rw [hsym]; exact hae
  have hge : act (refl b a) e = e := act_refl_of_perp ha hea
  have hgg : act (refl b a) (act (refl b a) y) = y := by
    rw [← act_mul, refl_mul_self, act_one]
  have hisom : refl b a ∈ isomGroup b := refl_mem_isomGroup hsym a
  have h1 : b (act (refl b a) y) e = b y e := by
    calc b (act (refl b a) y) e = b (act (refl b a) y) (act (refl b a) e) := by rw [hge]
      _ = b y e := hisom y e
  have h2 : b (act (refl b a) y) β = b y (act (refl b a) β) := by
    have hyβ : act (refl b a) (act (refl b a) β) = β := by
      rw [← act_mul, refl_mul_self, act_one]
    calc b (act (refl b a) y) β =
        b (act (refl b a) y) (act (refl b a) (act (refl b a) β)) := by rw [hyβ]
      _ = b y (act (refl b a) β) := hisom y (act (refl b a) β)
  have h3 : b (act (refl b a) β) (act (refl b a) β) = b β β := isom_norm hisom β
  simp only [eich, act_add, act_smul, act_neg, sub_eq_add_neg, hge, hgg, h1, h2, h3]

theorem b_act_refl_eich_eq_zero_and_ne_zero (hsym : ∀ x y, b x y = b y x)
    {v₀ e x β : Fin n → ZMod 5} (hv₀ : b v₀ v₀ = 1) (he : b e e = 0) (hev₀ : b e v₀ = 0)
    (hx : b x x = 1) (hβv₀ : b β v₀ = 0) (hβe : b β e = 0)
    (hβ : 2 * b x v₀ ^ 2 * b x e ^ 2 * b β β = 1) :
    b (act (refl b (eich b e β x)) (act (refl b x) v₀)) v₀ = 0 ∧
      b (act (refl b (eich b e β x)) (act (refl b x) v₀)) e ≠ 0 := by
  have hx' : b (eich b e β x) (eich b e β x) = 1 := by
    rw [eich_isom hsym he hβe x x, hx]
  constructor
  · rw [act_refl hx', act_refl hx, eich]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      hv₀, hev₀, hx, hβv₀, hsym v₀ x, hsym v₀ e, hsym v₀ β,
      mul_zero, sub_zero, add_zero]
    generalize b x v₀ = u1 at hβ ⊢
    generalize b x e = u2 at hβ ⊢
    generalize b x β = u3
    generalize b β β = u4 at hβ ⊢
    revert u1 u2 u3 u4
    decide
  · rw [act_refl hx', act_refl hx, eich]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      he, hev₀, hx, hβv₀, hβe, hsym v₀ x, hsym v₀ e, hsym v₀ β,
      mul_zero, sub_zero, add_zero]
    generalize b x v₀ = u1 at hβ ⊢
    generalize b x e = u2 at hβ ⊢
    generalize b x β = u3
    generalize b β β = u4 at hβ ⊢
    revert u1 u2 u3 u4
    decide

theorem eich_neg_ne (hsym : ∀ x y, b x y = b y x) {e a y : Fin n → ZMod 5} (he : b e e = 0)
    (ha : b a a = 1) (hae : b a e = 0) (hye : b y e ≠ 0) :
    eich b e (-a) y ≠ eich b e a y ∧ eich b e (-a) y ≠ -eich b e a y := by
  have hdiff : eich b e a y - eich b e (-a) y = (2 * b y e) • a - (2 * b y a) • e := by
    rw [eich, eich]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right,
      ha]
    generalize b y a = u1
    generalize b y e = u2
    generalize y i = u3
    generalize a i = u4
    generalize e i = u5
    revert u1 u2 u3 u4 u5
    decide
  have hsum : eich b e (-a) y + eich b e a y = (2 : ZMod 5) • y - b y e • e := by
    rw [eich, eich]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right,
      ha]
    generalize b y a = u1
    generalize b y e = u2
    generalize y i = u3
    generalize a i = u4
    generalize e i = u5
    revert u1 u2 u3 u4 u5
    decide
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  constructor
  · intro h
    have h0 : (2 * b y e) • a - (2 * b y a) • e = 0 := by rw [← hdiff, h, sub_self]
    have h1 : b ((2 * b y e) • a - (2 * b y a) • e) a = 0 := by rw [h0]; simp
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, ha, hsym e a,
      hae, mul_zero, mul_one, sub_zero] at h1
    rcases mul_eq_zero.1 h1 with h2 | hμ
    · exact h2ne h2
    · exact hye hμ
  · intro h
    have h0 : (2 : ZMod 5) • y - b y e • e = 0 := by
      rw [← hsum, h]
      abel
    have h1 : b ((2 : ZMod 5) • y - b y e • e) e = 0 := by rw [h0]; simp
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, he, mul_zero,
      sub_zero] at h1
    rcases mul_eq_zero.1 h1 with h2 | hμ
    · exact h2ne h2
    · exact hye hμ

theorem exists_add_smul_norm_sq (hsym : ∀ x y, b x y = b y x) {p : Fin n → ZMod 5} (hp : b p p = 1)
    (β : Fin n → ZMod 5) :
    ∃ s t : ZMod 5, t ≠ 0 ∧ b (β + s • p) (β + s • p) = t * t := by
  have key : ∀ N B : ZMod 5, ∃ s t : ZMod 5, t ≠ 0 ∧ N + 2 * s * B + s * s = t * t := by
    decide
  obtain ⟨s, t, ht, hst⟩ := key (b β β) (b β p)
  refine ⟨s, t, ht, ?_⟩
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hp, hsym p β, mul_one]
  linear_combination hst

private theorem exists_singular_partner (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {v₀ e : Fin n → ZMod 5} (hv₀ : b v₀ v₀ = 1)
    (he : b e e = 0) (he0 : e ≠ 0) (hev₀ : b e v₀ = 0) :
    ∃ f, b f v₀ = 0 ∧ b f e = 1 ∧ b f f = 0 := by
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, b e f₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact he0 (hnd e h)
  obtain ⟨f₁, hf₁⟩ : ∃ f₁, f₁ = f₀ - b f₀ v₀ • v₀ := ⟨_, rfl⟩
  have hf₁v₀ : b f₁ v₀ = 0 := by
    rw [hf₁, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv₀]
    ring
  have hef₁ : b e f₁ ≠ 0 := by
    rw [hf₁, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hev₀, mul_zero,
      sub_zero]
    exact hf₀
  obtain ⟨g, hg⟩ : ∃ g, g = (b e f₁)⁻¹ • f₁ := ⟨_, rfl⟩
  have hge : b e g = 1 := by
    rw [hg, LinearMap.BilinForm.smul_right]
    exact inv_mul_cancel₀ hef₁
  have hfg : b g e = 1 := by rw [hsym]; exact hge
  have hgv₀ : b g v₀ = 0 := by
    rw [hg, LinearMap.BilinForm.smul_left, hf₁v₀, mul_zero]
  obtain ⟨f, hf⟩ : ∃ f, f = g - (3 * b g g) • e := ⟨_, rfl⟩
  have hfv₀ : b f v₀ = 0 := by
    rw [hf, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hgv₀, hev₀, mul_zero,
      sub_zero]
  have hfe : b f e = 1 := by
    rw [hf, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, he, mul_zero, sub_zero]
    exact hfg
  have hff : b f f = 0 := by
    simp only [hf, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, he, hfg, hge,
      mul_zero, sub_zero]
    generalize b g g = u at ⊢
    revert u
    decide
  exact ⟨f, hfv₀, hfe, hff⟩

theorem exists_norm_perp_of_singular (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v₀ e : Fin n → ZMod 5}
    (hv₀ : b v₀ v₀ = 1) (he : b e e = 0) (he0 : e ≠ 0) (hev₀ : b e v₀ = 0) (c : ZMod 5) :
    ∃ β, b β v₀ = 0 ∧ b β e = 0 ∧ b β β = c := by
  obtain ⟨f, hfv₀, hfe, hff⟩ := exists_singular_partner hsym hnd hv₀ he he0 hev₀
  have hpp : b (e + f) (e + f) = 2 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, he, hsym e f, hfe, hff]
    ring
  have hmm : b (e - f) (e - f) = -2 := by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.sub_right, he, hsym e f, hfe, hff]
    ring
  have hpq : b (e + f) (e - f) = 0 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.sub_right, he, hsym e f, hfe, hff]
    ring
  have h1v : b (e + f) v₀ = 0 := by
    rw [LinearMap.BilinForm.add_left, hev₀, hfv₀, add_zero]
  have h3v : b (e - f) v₀ = 0 := by
    rw [LinearMap.BilinForm.sub_left, hev₀, hfv₀, sub_zero]
  obtain ⟨y, hyv₀, hy1, hy2, hyy⟩ := RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn
    (u₁ := v₀) (u₂ := e + f) (u₃ := e - f)
    (by rw [hv₀]; decide) (by rw [hpp]; decide) (by rw [hmm]; decide)
    (by rw [hsym]; exact h1v) (by rw [hsym]; exact h3v) hpq (c := c)
  rw [LinearMap.BilinForm.add_right] at hy1
  rw [LinearMap.BilinForm.sub_right] at hy2
  have h2e : (2 : ZMod 5) * b y e = 0 := by linear_combination hy1 + hy2
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨y, hyv₀, ?_, hyy⟩
  exact (mul_eq_zero.1 h2e).resolve_left h2ne

theorem eq_smul_of_forall_perp_singular (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {u z e : Fin n → ZMod 5}
    (hu : b u u = 1) (hz : b z z = 0) (hz0 : z ≠ 0) (hzu : b z u = 0) (heu : b e u = 0)
    (h : ∀ y, b y y = 1 → b y u = 0 → b y z = 0 → b y e = 0) : ∃ l : ZMod 5, e = l • z := by
  have huz : b u z = 0 := by rw [hsym]; exact hzu
  have hq : b (u + z) (u + z) = 1 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, hu, huz, hzu, hz]
    ring
  have hpq : b u (u + z) = 1 := by
    rw [LinearMap.BilinForm.add_right, hu, huz, add_zero]
  have hqp : u + z ≠ u := by
    intro h'
    have h1 : u + z = u + 0 := by simpa using h'
    exact hz0 (add_left_cancel h1)
  have hqp' : u + z ≠ -u := by
    intro h'
    have hz' : z = (-2 : ZMod 5) • u := by
      linear_combination (norm := module) h'
    rw [hz'] at hz
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hu] at hz
    revert hz
    decide
  obtain ⟨l, m, heq⟩ := FivePlane.mem_pair_of_forall_perp hsym hnd hn hu hq
    (by rw [hpq]; decide) hqp hqp'
    (fun y hy hyu hyq => by
      have hyz : b y z = 0 := by
        have h1 : b y (u + z) = 0 := hyq
        rw [LinearMap.BilinForm.add_right, hyu, zero_add] at h1
        exact h1
      rw [hsym]
      exact h y hy hyu hyz)
  have hlum : l + m = 0 := by
    have h2 : b (l • u + m • (u + z)) u = 0 := by rw [← heq]; exact heu
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left, hu, hzu, add_zero,
      mul_one] at h2
    linear_combination h2
  refine ⟨m, ?_⟩
  rw [heq]
  have hsplit : l • u + m • (u + z) = (l + m) • u + m • z := by module
  rw [hsplit, hlum, zero_smul, zero_add]

end FiveEichler

end CFSG.OddTranspositions.PartFour
