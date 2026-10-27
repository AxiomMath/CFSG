module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpFin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChFin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin6
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin8
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin10

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem mem_Tsub_of_not_swap {D : Subgroup (Perm (Fin 5))} {x : Perm (Fin 5)} (hx : x ∈ D)
    (hxx : x * x = 1) (hs : ¬ x.IsSwap) : x ∈ Tsub D :=
  Subgroup.mem_inf.mpr ⟨hx, even_of_not_swap hxx hs⟩

theorem isDoubleSwap_of_mem_Tsub {D : Subgroup (Perm (Fin 5))} {x : Perm (Fin 5)}
    (hx : x ∈ Tsub D) (hx1 : x ≠ 1) (hxx : x * x = 1) : IsDoubleSwap x :=
  ⟨hx1, by rw [pow_two]; exact hxx, Perm.mem_alternatingGroup.mp (Subgroup.mem_inf.mp hx).2⟩

theorem quad_noswap_cases {A : Subgroup (Perm (Fin 5))} (hA : IsElemAb A) (hq : IsQuad A)
    (hns : ∀ a ∈ A, ¬ a.IsSwap) :
    A = ⊥ ∨ ∃ x, x ≠ 1 ∧ x * x = 1 ∧ A = Subgroup.zpowers x := by
  rcases (isQuad_elemAb_iff hA).mp hq with h | h | ⟨s, t, -, -, hs, -, hA'⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hs (hns s (hA' ▸ Subgroup.subset_closure (by simp)))

theorem le_That_of_quad {D : Subgroup (Perm (Fin 5))} {A : Subgroup (Perm (Fin 5))} (hle : A ≤ D)
    (hA : IsElemAb A) (hq : IsQuad A) {s : Perm (Fin 5)} (hs : s ∈ A) (hsw : s.IsSwap) :
    A ≤ That D := by
  rcases (isQuad_elemAb_iff hA).mp hq with h | ⟨x, hx1, hxx, hAx⟩ | ⟨s', t', -, -, hs', ht', hA'⟩
  · rw [h] at hs
    exact absurd (Subgroup.mem_bot.mp hs) (isSwap_iff_mul_self.mp hsw).1
  · have hsx : s = x := by
      rw [hAx] at hs
      rcases (mem_zpowers_iff_of_mul_self hxx).mp hs with h | h
      · exact absurd h (isSwap_iff_mul_self.mp hsw).1
      · exact h
    rw [hAx, Subgroup.zpowers_le, ← hsx]
    exact swap_mem_That (hle hs) hsw
  · rw [hA', Subgroup.closure_le]
    intro y hy
    have hyA : y ∈ A := hA' ▸ Subgroup.subset_closure hy
    rcases hy with rfl | rfl
    · exact swap_mem_That (hle hyA) hs'
    · exact swap_mem_That (hle hyA) ht'

theorem comm_le_of_cen_inv {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {x : Perm (Fin 5)} (hx : x ∈ Tsub D) (hx1 : x ≠ 1) {g : Perm (Fin 5)} (hg : g ∈ D)
    (hcen : ∀ w ∈ commW orth (Subgroup.zpowers x) ⊤, orth.act g w = w) (w : orth.W) :
    orth.act g w * w⁻¹ ∈ commW orth (Subgroup.zpowers x) ⊤ := by
  by_cases hxz : x = zc D
  · subst hxz
    exact comm_le_of_cen hD hg hcen w
  · have h := inf_cenW_commW_zpowers hD (isCentInv_zc hD) hx hx1 hxz
    have hg' : g ∈ D ⊓ cenW (commW orth (Subgroup.zpowers x) ⊤) :=
      Subgroup.mem_inf.mpr ⟨hg, mem_cenW.mpr hcen⟩
    rw [h] at hg'
    exact Subgroup.subset_closure ⟨g, hg', w, Subgroup.mem_top w, rfl⟩

theorem not_swap_of_mem_Cfour {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {σ : Perm (Fin 5)} (h : σ ∈ Cfour D) : ¬ σ.IsSwap := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [← cj_Cfour, Cfour_std, mem_cj] at h
  rw [← isSwap_conj g⁻¹, inv_inv]
  have h4 : S5g ^ 4 = 1 := by decide +kernel
  rw [mem_zpowers_iff_of_pow_eq_one h4 (by norm_num)] at h
  obtain ⟨k, hk, hkσ⟩ := h
  rw [← hkσ]
  interval_cases k <;> (rw [isSwap_iff_mul_self]; decide +kernel)

theorem That_le_of_normal {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {B : Subgroup (Perm (Fin 5))} (hle : B ≤ D) (hn : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ ∈ B)
    {s : Perm (Fin 5)} (hs : s ∈ B) (hsw : s.IsSwap) : That D ≤ B := by
  rcases normal_cases hD (isCentInv_zc hD) hle hn with h | h | h | h | h | h
  · rw [h] at hs
    exact absurd (Subgroup.mem_bot.mp hs) (isSwap_iff_mul_self.mp hsw).1
  · rw [h] at hs
    rcases (mem_zpowers_iff_of_mul_self (zc_sq hD)).mp hs with h' | h'
    · exact absurd h' (isSwap_iff_mul_self.mp hsw).1
    · exact absurd (h' ▸ hsw) (zc_not_isSwap hD)
  · rw [h] at hs
    have h1 := Perm.mem_alternatingGroup.mp (Subgroup.mem_inf.mp hs).2
    have h2 := (isSwap_iff_mul_self.mp hsw).2.2
    exact absurd h1 h2
  · exact h.ge
  · rw [h] at hs
    exact absurd hsw (not_swap_of_mem_Cfour hD hs)
  · rw [h]
    exact That_le D

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
