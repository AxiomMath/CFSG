module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

private theorem s145_conj_eq_of_mem_NOf_of_mem_L (h : Hyp65 n M V₀ V g) {x e : G}
    (hxL : x ∈ LOf V g) (he : e ∈ NOf M V g) : x * e * x⁻¹ = e := by
  have hc := h.N_le_centralizer_L he
  have hcomm := Subgroup.mem_centralizer_iff.1 hc x hxL
  rw [hcomm]; group

private theorem s145_conj_mem_K_of_mem_L (h : Hyp65 n M V₀ V g) {x l : G}
    (hlL : l ∈ LOf V g) (hx : x ∈ KOf M V g) : l * x * l⁻¹ ∈ KOf M V g :=
  (Subgroup.mem_normalizer_iff.1 (h.L_le_normalizer_K hlL) x).1 hx

private theorem s145_commutator_mem_N (h : Hyp65 n M V₀ V g) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ KOf M V g) (hk₂ : k₂ ∈ KOf M V g) : ⁅k₁, k₂⁆ ∈ NOf M V g := by
  rw [commutatorElement_def]
  exact h.commutator_K_K_mem_N k₁ hk₁ k₂ hk₂

private theorem s145_S_mul (h : Hyp65 n M V₀ V g) {f x z : G}
    (hxL : x ∈ LOf V g) (hzL : z ∈ LOf V g)
    (hx : ⁅x, f⁆ ∈ NOf M V g) (hz : ⁅z, f⁆ ∈ NOf M V g) :
    ⁅x * z, f⁆ ∈ NOf M V g := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [s145_conj_eq_of_mem_NOf_of_mem_L h hxL hz]
  exact (NOf M V g).mul_mem hz hx

private theorem s145_S_inv (h : Hyp65 n M V₀ V g) {f x : G} (hxL : x ∈ LOf V g)
    (hx : ⁅x, f⁆ ∈ NOf M V g) : ⁅x⁻¹, f⁆ ∈ NOf M V g := by
  have hfx : ⁅f, x⁆ ∈ NOf M V g := by
    rw [← commutatorElement_inv]
    exact (NOf M V g).inv_mem hx
  rw [commutatorElement_inv_left]
  have h := s145_conj_eq_of_mem_NOf_of_mem_L h ((LOf V g).inv_mem hxL) hfx
  rw [inv_inv] at h
  rwa [h]

private theorem s145_F_mul (h : Hyp65 n M V₀ V g) {y f₁ f₂ : G}
    (hf₁L : f₁ ∈ LOf V g) (hf₂L : f₂ ∈ LOf V g)
    (h₁ : ⁅y, f₁⁆ ∈ NOf M V g) (h₂ : ⁅y, f₂⁆ ∈ NOf M V g) :
    ⁅y, f₁ * f₂⁆ ∈ NOf M V g := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [show ⁅y, f₁⁆ * f₁ * ⁅y, f₂⁆ * f₁⁻¹
        = ⁅y, f₁⁆ * (f₁ * ⁅y, f₂⁆ * f₁⁻¹) from by group]
  rw [s145_conj_eq_of_mem_NOf_of_mem_L h hf₁L h₂]
  exact (NOf M V g).mul_mem h₁ h₂

private theorem s145_F_inv (h : Hyp65 n M V₀ V g) {y f : G} (hfL : f ∈ LOf V g)
    (hfy : ⁅y, f⁆ ∈ NOf M V g) : ⁅y, f⁻¹⁆ ∈ NOf M V g := by
  have hfy' : ⁅f, y⁆ ∈ NOf M V g := by
    rw [← commutatorElement_inv]
    exact (NOf M V g).inv_mem hfy
  rw [commutatorElement_inv_right]
  have h := s145_conj_eq_of_mem_NOf_of_mem_L h ((LOf V g).inv_mem hfL) hfy'
  rw [inv_inv] at h
  rwa [h]

private theorem s145_mem_N_of_commutator_mem (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l)
    {t₁ t₂ f : G} (ht₁ : t₁ ∈ V) (ht₁U : t₁ ∉ UOf M V g)
    (ht₂ : t₂ ∈ conjSubgroup V g) (ht₂B : t₂ ∉ BOf M V g)
    (hfK : f ∈ KOf M V g)
    (h₁ : ⁅t₁, f⁆ ∈ NOf M V g) (h₂ : ⁅t₂, f⁆ ∈ NOf M V g) :
    f ∈ NOf M V g := by
  have hU : f ∈ UOf M V g :=
    h.stepB hgen hlK ht₁ ht₁U f hfK (by
      rw [← commutatorElement_inv t₁ f]
      exact (NOf M V g).inv_mem h₁)
  have hB : f ∈ BOf M V g :=
    h.stepA hgen hlK ht₂ ht₂B f hfK (by
      rw [← commutatorElement_inv t₂ f]
      exact (NOf M V g).inv_mem h₂)
  exact Subgroup.mem_inf.2 ⟨hU, hB⟩

theorem mem_N_of_conj_mul_inv_mem (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l)
    {t₁ t₂ y : G} (ht₁ : t₁ ∈ V) (ht₁U : t₁ ∉ UOf M V g) (ht₂ : t₂ ∈ conjSubgroup V g)
    (ht₂B : t₂ ∉ BOf M V g) (hy : (t₁ * t₂)⁻¹ * y ∈ KOf M V g) {k : G}
    (hk : k ∈ KOf M V g) (hyk : y * k * y⁻¹ * k⁻¹ ∈ NOf M V g) :
    k ∈ NOf M V g := by
  have hKL := KOf_le_LOf (M := M) (V := V) (g := g)
  have ht₁L : t₁ ∈ LOf V g := Subgroup.mem_sup_left ht₁
  have ht₂L : t₂ ∈ LOf V g := Subgroup.mem_sup_right ht₂
  have ht₁2 : t₁ * t₁ = 1 := h.elemAbelian.mul_self_eq_one ht₁
  have ht₂2 : t₂ * t₂ = 1 := h.swap.elemAbelian.mul_self_eq_one ht₂
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁2
  have ht₂inv : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right ht₂2
  obtain ⟨k₀, hk₀, hy_eq⟩ : ∃ k₀ : G, k₀ ∈ KOf M V g ∧ y = t₁ * t₂ * k₀ :=
    ⟨(t₁ * t₂)⁻¹ * y, hy, by group⟩
  have hk₀L : k₀ ∈ LOf V g := hKL hk₀
  have hyL : y ∈ LOf V g := by
    rw [hy_eq]
    exact (LOf V g).mul_mem ((LOf V g).mul_mem ht₁L ht₂L) hk₀L
  have hkF : ⁅y, k⁆ ∈ NOf M V g := by rw [commutatorElement_def]; exact hyk
  have hkey : t₁ * (t₁ * y * t₁⁻¹) * t₁⁻¹ = y := by
    rw [ht₁inv]
    calc t₁ * (t₁ * y * t₁) * t₁ = (t₁ * t₁) * y * (t₁ * t₁) := by group
      _ = y := by rw [ht₁2, one_mul, mul_one]
  have hconjF : ∀ f : G, f ∈ KOf M V g → ⁅y, f⁆ ∈ NOf M V g →
      ⁅y, t₁ * f * t₁⁻¹⁆ ∈ NOf M V g := by
    intro f hfK hyf
    have hyy'K : y * (t₁ * y * t₁⁻¹) ∈ KOf M V g := by
      have h₁ : t₂ * k₀ * t₂ ∈ KOf M V g := by
        simpa only [ht₂inv] using s145_conj_mem_K_of_mem_L h ht₂L hk₀
      have h₂ : t₁ * (t₂ * k₀ * t₂) * t₁⁻¹ ∈ KOf M V g :=
        s145_conj_mem_K_of_mem_L h ht₁L h₁
      have h₃ : t₁ * k₀ * t₁⁻¹ ∈ KOf M V g :=
        s145_conj_mem_K_of_mem_L h ht₁L hk₀
      have hL : y * (t₁ * y * t₁⁻¹) = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by
        rw [hy_eq, ht₁inv]
        calc (t₁ * t₂ * k₀) * (t₁ * (t₁ * t₂ * k₀) * t₁)
            = t₁ * t₂ * k₀ * (t₁ * t₁) * t₂ * k₀ * t₁ := by group
          _ = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by rw [ht₁2, mul_one]
      have hR : (t₁ * (t₂ * k₀ * t₂) * t₁⁻¹) * (t₁ * k₀ * t₁⁻¹)
          = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by
        rw [ht₁inv]
        calc (t₁ * (t₂ * k₀ * t₂) * t₁) * (t₁ * k₀ * t₁)
            = t₁ * t₂ * k₀ * t₂ * (t₁ * t₁) * k₀ * t₁ := by group
          _ = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by rw [ht₁2, mul_one]
      rw [hL, ← hR]
      exact (KOf M V g).mul_mem h₂ h₃
    have hy'L : t₁ * y * t₁⁻¹ ∈ LOf V g :=
      (LOf V g).mul_mem ((LOf V g).mul_mem ht₁L hyL) ((LOf V g).inv_mem ht₁L)
    have hy'f : ⁅t₁ * y * t₁⁻¹, f⁆ ∈ NOf M V g := by
      have h1 : ⁅y⁻¹, f⁆ ∈ NOf M V g := s145_S_inv h hyL hyf
      have h2 : ⁅y * (t₁ * y * t₁⁻¹), f⁆ ∈ NOf M V g :=
        s145_commutator_mem_N h hyy'K hfK
      have hy'eq : t₁ * y * t₁⁻¹ = y⁻¹ * (y * (t₁ * y * t₁⁻¹)) := by group
      rw [hy'eq]
      exact s145_S_mul h ((LOf V g).inv_mem hyL) ((LOf V g).mul_mem hyL hy'L) h1 h2
    have hident : ⁅y, t₁ * f * t₁⁻¹⁆ = t₁ * ⁅t₁ * y * t₁⁻¹, f⁆ * t₁⁻¹ := by
      conv_lhs => rw [← hkey]
      exact (conjugate_commutatorElement (t₁ * y * t₁⁻¹) f t₁).symm
    rw [hident]
    rw [s145_conj_eq_of_mem_NOf_of_mem_L h ht₁L hy'f]
    exact hy'f
  have hF_mul : ∀ f₁ f₂ : G, f₁ ∈ KOf M V g → f₂ ∈ KOf M V g →
      ⁅y, f₁⁆ ∈ NOf M V g → ⁅y, f₂⁆ ∈ NOf M V g →
      ⁅y, f₁ * f₂⁆ ∈ NOf M V g := by
    intro f₁ f₂ hf₁ hf₂ h₁ h₂
    exact s145_F_mul h (hKL hf₁) (hKL hf₂) h₁ h₂
  have hF_inv : ∀ f : G, f ∈ KOf M V g → ⁅y, f⁆ ∈ NOf M V g →
      ⁅y, f⁻¹⁆ ∈ NOf M V g := by
    intro f hf hfy
    exact s145_F_inv h (hKL hf) hfy
  by_contra hkE
  by_cases hcase : ⁅t₁, k⁆ ∈ NOf M V g
  · have ht₂k : ⁅t₂, k⁆ ∈ NOf M V g := by
      have h1 : ⁅t₁⁻¹, k⁆ ∈ NOf M V g := s145_S_inv h ht₁L hcase
      have h3 : ⁅k₀⁻¹, k⁆ ∈ NOf M V g :=
        s145_S_inv h hk₀L (s145_commutator_mem_N h hk₀ hk)
      have h12 : ⁅t₁⁻¹ * y, k⁆ ∈ NOf M V g :=
        s145_S_mul h ((LOf V g).inv_mem ht₁L) hyL h1 hkF
      have ht₂eq : t₂ = t₁⁻¹ * y * k₀⁻¹ := by rw [hy_eq]; group
      rw [ht₂eq]
      exact s145_S_mul h ((LOf V g).mul_mem ((LOf V g).inv_mem ht₁L) hyL)
        ((LOf V g).inv_mem hk₀L) h12 h3
    exact absurd (s145_mem_N_of_commutator_mem h hgen hlK ht₁ ht₁U ht₂ ht₂B hk
      hcase ht₂k) hkE
  · set f : G := (t₁ * k * t₁⁻¹) * k⁻¹ with hfdef
    have hfK : f ∈ KOf M V g := by
      rw [hfdef]
      exact (KOf M V g).mul_mem
        (s145_conj_mem_K_of_mem_L h ht₁L hk) ((KOf M V g).inv_mem hk)
    have hfE : f ∉ NOf M V g := by
      rw [hfdef, ← commutatorElement_def]
      exact hcase
    have ht₁f : ⁅t₁, f⁆ ∈ NOf M V g := by
      have hc : k * (t₁ * k⁻¹ * t₁⁻¹) ∈ KOf M V g :=
        (KOf M V g).mul_mem hk
          (s145_conj_mem_K_of_mem_L h ht₁L ((KOf M V g).inv_mem hk))
      have hcc : (k * (t₁ * k⁻¹ * t₁⁻¹)) * (k * (t₁ * k⁻¹ * t₁⁻¹)) ∈ NOf M V g :=
        h.sq_K_mem_N (k * (t₁ * k⁻¹ * t₁⁻¹)) hc
      have heq : ⁅t₁, f⁆ = (k * (t₁ * k⁻¹ * t₁⁻¹)) * (k * (t₁ * k⁻¹ * t₁⁻¹)) := by
        rw [hfdef, commutatorElement_def, ht₁inv]
        rw [show ((t₁ * k * t₁) * k⁻¹)⁻¹ = k * (t₁ * k⁻¹ * t₁) from by
          simp only [mul_inv_rev, inv_inv, ht₁inv, mul_assoc]]
        calc t₁ * ((t₁ * k * t₁) * k⁻¹) * t₁ * (k * (t₁ * k⁻¹ * t₁))
            = (t₁ * t₁) * k * t₁ * k⁻¹ * t₁ * k * (t₁ * k⁻¹ * t₁) := by group
          _ = (k * (t₁ * k⁻¹ * t₁)) * (k * (t₁ * k⁻¹ * t₁)) := by
                rw [ht₁2, one_mul]; group
      rw [heq]
      exact hcc
    have hyf : ⁅y, f⁆ ∈ NOf M V g := by
      have h1 : ⁅y, t₁ * k * t₁⁻¹⁆ ∈ NOf M V g := hconjF k hk hkF
      have h2 : ⁅y, k⁻¹⁆ ∈ NOf M V g := hF_inv k hk hkF
      have h3 : ⁅y, (t₁ * k * t₁⁻¹) * k⁻¹⁆ ∈ NOf M V g :=
        hF_mul (t₁ * k * t₁⁻¹) k⁻¹ (s145_conj_mem_K_of_mem_L h ht₁L hk)
          ((KOf M V g).inv_mem hk) h1 h2
      rw [hfdef]
      exact h3
    have ht₂f : ⁅t₂, f⁆ ∈ NOf M V g := by
      have h1 : ⁅t₁⁻¹, f⁆ ∈ NOf M V g := s145_S_inv h ht₁L ht₁f
      have h3 : ⁅k₀⁻¹, f⁆ ∈ NOf M V g :=
        s145_S_inv h hk₀L (s145_commutator_mem_N h hk₀ hfK)
      have h12 : ⁅t₁⁻¹ * y, f⁆ ∈ NOf M V g :=
        s145_S_mul h ((LOf V g).inv_mem ht₁L) hyL h1 hyf
      have ht₂eq : t₂ = t₁⁻¹ * y * k₀⁻¹ := by rw [hy_eq]; group
      rw [ht₂eq]
      exact s145_S_mul h ((LOf V g).mul_mem ((LOf V g).inv_mem ht₁L) hyL)
        ((LOf V g).inv_mem hk₀L) h12 h3
    exact absurd (s145_mem_N_of_commutator_mem h hgen hlK ht₁ ht₁U ht₂ ht₂B hfK
      ht₁f ht₂f) hfE

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
