module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin

namespace S153E59

section Fix

variable {W : Type*} [CommGroup W] [Finite W]

theorem four_le_rk_fix {a : MulAut W} {E₁ E₂ C Ax : Subgroup W} (hE : E₁ ⊓ E₂ = ⊥)
    (hr₁ : rk E₁ = 3) (hr₂ : rk E₂ = 3) (hC : rk C ≤ 1) (hc : ∀ w ∈ E₁, a w * w⁻¹ ∈ C)
    (hAxE : Ax ≤ E₂) (hAxfix : ∀ w ∈ Ax, a w = w) (hax : ∀ w ∈ E₂, a w * w⁻¹ ∈ Ax) :
    4 ≤ rk (fixV (Subgroup.zpowers a)) := by
  have hker : (commHom a).ker = fixV (Subgroup.zpowers a) := ker_commHom a
  have h1 := rk_map_add_rk_inf_ker (commHom a) E₁
  have h1le : rk (E₁.map (commHom a)) ≤ 1 := by
    refine (rk_mono ?_).trans hC
    rintro _ ⟨w, hw, rfl⟩
    exact hc w hw
  have h2 := rk_map_add_rk_inf_ker (commHom a) E₂
  have hAxker : Ax ≤ E₂ ⊓ (commHom a).ker := fun w hw =>
    ⟨hAxE hw, MonoidHom.mem_ker.mpr (by rw [commHom_apply, hAxfix w hw, mul_inv_cancel])⟩
  have h2le : rk (E₂.map (commHom a)) ≤ rk (E₂ ⊓ (commHom a).ker : Subgroup W) := by
    refine (rk_mono ?_).trans (rk_mono hAxker)
    rintro _ ⟨w, hw, rfl⟩
    exact hax w hw
  have h3 := rk_sup_add_rk_inf (E₁ ⊓ (commHom a).ker) (E₂ ⊓ (commHom a).ker)
  have hinf : (E₁ ⊓ (commHom a).ker) ⊓ (E₂ ⊓ (commHom a).ker) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← hE]
    intro w hw
    exact ⟨hw.1.1, hw.2.1⟩
  have hsup : rk ((E₁ ⊓ (commHom a).ker) ⊔ (E₂ ⊓ (commHom a).ker) : Subgroup W) ≤
      rk (commHom a).ker :=
    rk_mono (sup_le inf_le_right inf_le_right)
  rw [hinf, rk_bot] at h3
  rw [← hker]
  omega

theorem rk_fix_le_of_swap {a : MulAut W} {W₁ W₂ : Subgroup W} (hint : W₁ ⊓ W₂ = ⊥)
    (hsup : W₁ ⊔ W₂ = ⊤) (h12 : ∀ w ∈ W₁, a w ∈ W₂) (h21 : ∀ w ∈ W₂, a w ∈ W₁) :
    rk (fixV (Subgroup.zpowers a)) ≤ rk W₁ := by
  let φ : W →* W := MonoidHom.mk' (fun y => y * a y) (fun x y => by
    rw [map_mul]
    exact mul_mul_mul_comm x y (a x) (a y))
  have hfix : fixV (Subgroup.zpowers a) ≤ W₁.map φ := by
    intro w hw
    have haw : a w = w := (mem_fixV.mp hw) a (Subgroup.mem_zpowers a)
    have hmem : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hmem
    refine ⟨y, hy, ?_⟩
    show y * a y = y * z
    congr 1
    have e1 : a z * y⁻¹ = z * (a y)⁻¹ := by
      have : a y * a z = y * z := by rw [← map_mul]; exact haw
      calc a z * y⁻¹ = (a y)⁻¹ * (a y * a z) * y⁻¹ := by group
        _ = (a y)⁻¹ * (y * z) * y⁻¹ := by rw [this]
        _ = (a y)⁻¹ * (z * y) * y⁻¹ := by rw [mul_comm y z]
        _ = (a y)⁻¹ * z := by group
        _ = z * (a y)⁻¹ := mul_comm _ _
    have e2 : a z * y⁻¹ ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.mul_mem (h21 z hz) (W₁.inv_mem hy), ?_⟩
      rw [e1]
      exact W₂.mul_mem hz (W₂.inv_mem (h12 y hy))
    rw [hint, Subgroup.mem_bot, e1, mul_inv_eq_one] at e2
    exact e2.symm
  refine (rk_mono hfix).trans ?_
  have := rk_map_add_rk_inf_ker φ W₁
  omega

end Fix

section Swap

variable {W : Type*} [Group W]

theorem swap_of_index_two {A A₀ : Subgroup (MulAut W)} (hidx : A₀.relIndex A = 2)
    {W₁ W₂ : Subgroup W} (h₁ : ∀ a ∈ A₀, ∀ w ∈ W₁, a w ∈ W₁)
    (hint : W₁ ⊓ W₂ = ⊥) (hne : W₁ ≠ ⊥) {x₀ : MulAut W} (hx₀A : x₀ ∈ A)
    (hx₀ : ∀ w, w ∈ W₂ ↔ ∃ v ∈ W₁, x₀ v = w) {x : MulAut W} (hxA : x ∈ A) (hxA₀ : x ∉ A₀) :
    (∀ w ∈ W₁, x w ∈ W₂) ∧ (∀ w ∈ W₂, x w ∈ W₁) := by
  have hI : (A₀.subgroupOf A).index = 2 := hidx
  have hx₀A₀ : x₀ ∉ A₀ := by
    intro h
    obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hm : x₀ w ∈ W₁ ⊓ W₂ := ⟨h₁ x₀ h w w.2, (hx₀ _).mpr ⟨w, w.2, rfl⟩⟩
    rw [hint, Subgroup.mem_bot] at hm
    exact hw1 (Subtype.ext (x₀.injective (by rw [hm, Subgroup.coe_one, map_one])))
  have hkey : ∀ {y z : MulAut W}, y ∈ A → z ∈ A → y ∉ A₀ → z ∉ A₀ → y * z ∈ A₀ := by
    intro y z hy hz hy' hz'
    have := (Subgroup.mul_mem_iff_of_index_two hI (a := ⟨y, hy⟩) (b := ⟨z, hz⟩)).mpr
      (iff_of_false (fun h => hy' h) (fun h => hz' h))
    exact this
  have hm1 : x₀⁻¹ * x ∈ A₀ :=
    hkey (A.inv_mem hx₀A) hxA (fun h => hx₀A₀ (by simpa using A₀.inv_mem h)) hxA₀
  have hm2 : x * x₀ ∈ A₀ := hkey hxA hx₀A hxA₀ hx₀A₀
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have h1 : (x₀⁻¹ * x) w ∈ W₁ := h₁ _ hm1 w hw
    have h2 : x w = x₀ ((x₀⁻¹ * x) w) := by simp [MulAut.mul_apply]
    rw [h2]
    exact (hx₀ _).mpr ⟨_, h1, rfl⟩
  · obtain ⟨v, hv, rfl⟩ := (hx₀ w).mp hw
    have : x (x₀ v) = (x * x₀) v := rfl
    rw [this]
    exact h₁ _ hm2 v hv

end Swap

end S153E59

end CFSG.Quasithin
