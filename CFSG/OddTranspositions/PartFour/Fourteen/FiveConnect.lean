module

public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive
import CFSG.OddTranspositions.PartFour.Fourteen.FivePlanePerp

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace FiveConnect

open TableE1Five

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

theorem exists_norm_one_perp_aniso (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {x z : Fin n → ZMod 5}
    (hz : b z z = 2) (hx : b x x = 1) : ∃ u, b u u = 1 ∧ b u z = 0 ∧ b u x = 0 := by
  have hx0 : b x x ≠ 0 := by rw [hx]; decide
  have hquad : ∀ γ : ZMod 5, (2 : ZMod 5) - γ * γ ≠ 0 := by decide
  let z' := z - b z x • x
  have hz'def : z' = z - b z x • x := rfl
  have hz'x : b z' x = 0 := by
    simp only [z', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hx]
    ring
  have hz' : b z' z' = 2 - b z x * b z x := by
    simp only [z', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hz, hx, hsym x z]
    ring
  have hz'0 : b z' z' ≠ 0 := by rw [hz']; exact hquad _
  have hxz' : b x z' = 0 := by rw [hsym]; exact hz'x
  obtain ⟨e, hex, hez', hee⟩ :=
    exists_aniso_perp₂ hsym hnd (by omega) (u₁ := x) (u₂ := z') hx0 hz'0 hxz'
  have hxe : b x e = 0 := by rw [hsym]; exact hex
  have hz'e : b z' e = 0 := by rw [hsym]; exact hez'
  obtain ⟨u, hux, huz', -, huu⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := x) (u₂ := z') (u₃ := e) hx0 hz'0 hee
      hxz' hxe hz'e (c := 1)
  have hz_eq : z = z' + b z x • x := by rw [hz'def]; abel
  refine ⟨u, huu, ?_, hux⟩
  rw [hz_eq, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, huz', hux]
  ring

private theorem exists_norm_one_not_sq_one (hsym : ∀ x y, b x y = b y x)
    {u₀ t y₁ y₂ z : Fin n → ZMod 5} (hu₀ : b u₀ u₀ = 1) (hu₀z : b u₀ z = 0)
    (htz : b t z = 0) (htt : b t t = 2) (htu₀ : b t u₀ = 0) (hy₁u₀ : b y₁ u₀ = 0)
    (hy₁t : b y₁ t = 0) :
    ∃ u₁, b u₁ u₁ = 1 ∧ b u₁ z = 0 ∧ b y₁ u₁ = 0 ∧ b u₁ y₂ * b u₁ y₂ ≠ 1 := by
  have htu₀' : b u₀ t = 0 := by rw [hsym]; exact htu₀
  have hplus_norm : b ((2 : ZMod 5) • u₀ + t) ((2 : ZMod 5) • u₀ + t) = 1 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hu₀, htu₀', htu₀, htt]
    decide
  have hplus_z : b ((2 : ZMod 5) • u₀ + t) z = 0 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu₀z, htz]
    decide
  have hplus_y₁ : b y₁ ((2 : ZMod 5) • u₀ + t) = 0 := by
    simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hy₁u₀, hy₁t]
    decide
  have hplus_y₂ : b ((2 : ZMod 5) • u₀ + t) y₂ = 2 * b u₀ y₂ + b t y₂ := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  have hminus_norm : b ((2 : ZMod 5) • u₀ + (-1 : ZMod 5) • t)
      ((2 : ZMod 5) • u₀ + (-1 : ZMod 5) • t) = 1 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hu₀, htu₀', htu₀, htt]
    decide
  have hminus_z : b ((2 : ZMod 5) • u₀ + (-1 : ZMod 5) • t) z = 0 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu₀z, htz]
    decide
  have hminus_y₁ : b y₁ ((2 : ZMod 5) • u₀ + (-1 : ZMod 5) • t) = 0 := by
    simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hy₁u₀, hy₁t]
    decide
  have hminus_y₂ : b ((2 : ZMod 5) • u₀ + (-1 : ZMod 5) • t) y₂ = 2 * b u₀ y₂ - b t y₂ := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
    ring
  have hnotboth : ∀ γ τ : ZMod 5, γ * γ = 1 →
      ¬((2 * γ + τ) * (2 * γ + τ) = 1 ∧ (2 * γ - τ) * (2 * γ - τ) = 1) := by
    decide
  by_cases h₀ : b u₀ y₂ * b u₀ y₂ = 1
  · by_cases hp : (2 * b u₀ y₂ + b t y₂) * (2 * b u₀ y₂ + b t y₂) = 1
    · have hm : (2 * b u₀ y₂ - b t y₂) * (2 * b u₀ y₂ - b t y₂) ≠ 1 :=
        fun hmm => hnotboth _ _ h₀ ⟨hp, hmm⟩
      exact ⟨(2 : ZMod 5) • u₀ + (-1 : ZMod 5) • t, hminus_norm, hminus_z, hminus_y₁, by
        rw [hminus_y₂]; exact hm⟩
    · exact ⟨(2 : ZMod 5) • u₀ + t, hplus_norm, hplus_z, hplus_y₁, by
        rw [hplus_y₂]; exact hp⟩
  · exact ⟨u₀, hu₀, hu₀z, hy₁u₀, h₀⟩

theorem exists_walk_three (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {z y₁ y₂ : Fin n → ZMod 5}
    (hz : b z z = 2) (hy₁ : b y₁ y₁ = 1) (hy₁z : b y₁ z = 0) (hy₂ : b y₂ y₂ = 1)
    (hy₂z : b y₂ z = 0) :
    ∃ u₁ u₂, b u₁ u₁ = 1 ∧ b u₁ z = 0 ∧ b u₂ u₂ = 1 ∧ b u₂ z = 0 ∧ b y₁ u₁ = 0 ∧
      b u₁ u₂ = 0 ∧ b u₂ y₂ = 0 := by
  have hz0 : b z z ≠ 0 := by rw [hz]; decide
  have hy₁0 : b y₁ y₁ ≠ 0 := by rw [hy₁]; decide
  obtain ⟨u₀, hu₀, hu₀z, hu₀y₁⟩ :=
    exists_norm_one_perp_aniso hsym hnd hn (x := y₁) (z := z) hz hy₁
  have hu₀0 : b u₀ u₀ ≠ 0 := by rw [hu₀]; decide
  have hy₁u₀ : b y₁ u₀ = 0 := by rw [hsym]; exact hu₀y₁
  obtain ⟨t, htz, hty₁, htu₀, htt⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := z) (u₂ := y₁) (u₃ := u₀)
      hz0 hy₁0 hu₀0 (by rw [hsym]; exact hy₁z) (by rw [hsym]; exact hu₀z) hy₁u₀ (c := 2)
  have hy₁t : b y₁ t = 0 := by rw [hsym]; exact hty₁
  obtain ⟨u₁, hu₁, hu₁z, hy₁u₁, hbad₁⟩ :=
    exists_norm_one_not_sq_one hsym hu₀ hu₀z htz htt htu₀ hy₁u₀ hy₁t
  let y₂' := y₂ - b y₂ u₁ • u₁
  have hy₂'def : y₂' = y₂ - b y₂ u₁ • u₁ := rfl
  have hy₂'u₁ : b y₂' u₁ = 0 := by
    simp only [y₂', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hu₁]
    ring
  have hy₂'z : b y₂' z = 0 := by
    simp only [y₂', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hy₂z, hu₁z]
    ring
  have hbady₂ : b y₂ u₁ * b y₂ u₁ ≠ 1 := by
    rw [hsym u₁ y₂] at hbad₁
    exact hbad₁
  have hnorm : b y₂' y₂' = 1 - b y₂ u₁ * b y₂ u₁ := by
    simp only [y₂', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hy₂, hu₁, hsym u₁ y₂]
    ring
  have hy₂'0 : b y₂' y₂' ≠ 0 := by
    have hkey : ∀ c : ZMod 5, c * c ≠ 1 → (1 : ZMod 5) - c * c ≠ 0 := by decide
    rw [hnorm]
    exact hkey _ hbady₂
  have hu₁0 : b u₁ u₁ ≠ 0 := by rw [hu₁]; decide
  have hzu₁ : b z u₁ = 0 := by rw [hsym]; exact hu₁z
  have hzy₂' : b z y₂' = 0 := by rw [hsym]; exact hy₂'z
  have hu₁y₂' : b u₁ y₂' = 0 := by rw [hsym]; exact hy₂'u₁
  obtain ⟨u₂, hu₂z, hu₂u₁, hu₂y₂', hu₂⟩ :=
    RootBlockFive.exists_norm_eq_perp₃ hsym hnd hn (u₁ := z) (u₂ := u₁) (u₃ := y₂')
      hz0 hu₁0 hy₂'0 hzu₁ hzy₂' hu₁y₂' (c := 1)
  refine ⟨u₁, u₂, hu₁, hu₁z, hu₂, hu₂z, hy₁u₁, ?_, ?_⟩
  · rw [hsym]; exact hu₂u₁
  · have hy₂eq : y₂ = y₂' + b y₂ u₁ • u₁ := by rw [hy₂'def]; abel
    rw [hy₂eq, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hu₂y₂', hu₂u₁]
    ring

theorem eq_smul_of_forall_perp_aniso (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {u x z z' : Fin n → ZMod 5}
    (hu : b u u = 1) (hx : b x x = 1) (hux : b u x = 0) (hz : b z z = 2) (hzu : b z u = 0)
    (hzx : b z x = 0) (hz'u : b z' u = 0) (hz'x : b z' x = 0)
    (h : ∀ y, b y y = 1 → b y u = 0 → b y x = 0 → b y z = 0 → b y z' = 0) :
    ∃ l : ZMod 5, z' = l • z := by
  have hz0 : b z z ≠ 0 := by rw [hz]; decide
  have hu0 : b u u ≠ 0 := by rw [hu]; decide
  have hx0 : b x x ≠ 0 := by rw [hx]; decide
  have huz : b u z = 0 := by rw [hsym]; exact hzu
  have hxz : b x z = 0 := by rw [hsym]; exact hzx
  let l : ZMod 5 := 3 * b z' z
  have h2l : (2 : ZMod 5) * l = b z' z := by
    dsimp only [l]
    rw [← mul_assoc, show (2 * 3 : ZMod 5) = 1 by decide, one_mul]
  let y : Fin n → ZMod 5 := z' - l • z
  have hyu : b y u = 0 := by
    simp only [y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz'u, hzu]
    ring
  have hyx : b y x = 0 := by
    simp only [y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz'x, hzx]
    ring
  have hyz : b y z = 0 := by
    have hcomm : l * 2 = b z' z := by rw [mul_comm]; exact h2l
    simp only [y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz, hcomm]
    ring
  have hyw : ∀ w, b w w = 1 → b w u = 0 → b w x = 0 → b w z = 0 → b y w = 0 := by
    intro w hw hwu hwx hwz
    have hwz' : b w z' = 0 := h w hw hwu hwx hwz
    rw [hsym]
    simp only [y, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hwz', hwz]
    ring
  have hy0 : y = 0 :=
    FivePlane.eq_zero_of_forall_norm_one_perp_triple hsym hnd hn hu0 hx0 hz0 hux huz hxz hyu hyx
      hyz hyw
  refine ⟨l, ?_⟩
  have hy : z' - l • z = 0 := hy0
  exact sub_eq_zero.1 hy

end FiveConnect

end CFSG.OddTranspositions.PartFour
