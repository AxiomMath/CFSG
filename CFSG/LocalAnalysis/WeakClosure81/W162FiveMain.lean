module

public import CFSG.LocalAnalysis.WeakClosure81.W162FiveSetup
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem w162_inf_conj_V_eq (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) :
    V ⊓ conjSubgroup V g = U := by
  have hUC : U ≤ V ⊓ conjSubgroup V g := le_inf h.le (h.U_le_conj hg)
  have hnot : ¬ centralizer ((V ⊓ conjSubgroup V g : Subgroup G) : Set G) ≤ M := by
    intro hle
    refine h.w162_not_conj_le_M h1 hS hg hc fun y hy => hle ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup h.hyp.h6.elemAbelian g) hz.2 hy
  exact h.w162_eq_of_not_centralizer_le hUC inf_le_left hnot

section Certified


theorem w162_V₀_le_K (h1 : W16One G) (h152 : Thm152 G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    {g : G} (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) : V₀ ≤ KOf M V g := by
  have h65 := h.w162_hyp65 h1 hS hg hc
  rcases h65.six_five_three with hK | ⟨-, -, -, hr⟩
  · exact hK
  · exfalso
    have h2 := h.rMV_eq
    rw [hr] at h2
    have h3 : mSub V₀ = E3.mQuot V (U ⊔ V₀) + mSub V₀ := by exact_mod_cast h2
    have h4 := h.one_le_n h152
    omega

theorem w162_not_inCalOStar (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) :
    ¬ InCalOStar (E3.mQuot V U) M V₀ V g := by
  intro hstar
  have h65 := h.w162_hyp65 h1 hS hg hc
  have h64 : Hyp64 (E3.mQuot V U) M V₀ V g :=
    ⟨h65.elemAbelian, h65.le, h65.normalizer_eq, h65.normalizer₀.symm.le,
      fun _ => h65.isTI, fun _ => h65.normalizer₀, hstar⟩
  have h5 := six_four_five_uncond h64
  have hB : BOf M V g ≤ F11.CTilde M V₀ V := h.w162_inf_conj_le_cTilde hg
  have hrel : (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g) = 1 :=
    Subgroup.relIndex_eq_one.2 fun x hx => ⟨hx, hB hx⟩
  rw [hrel, one_mul] at h5
  have hUle : UOf M V g ≤ V ⊓ centralizer (BOf M V g : Set G) := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hu.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbC : b ∈ F11.CTilde M V₀ V := hB hb
    have h1' : b * u * b⁻¹ * u⁻¹ ∈ V₀ := (FourteenTwo.mem_cTilde_iff_comm.1 hbC).2.2 u hu.1
    have huN : u ∈ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, h65.normalizer_eq]
      exact hu.2
    have hubu : u * b * u⁻¹ ∈ conjSubgroup V g := (Subgroup.mem_normalizer_iff.1 huN b).1 hb.1
    have h2 : b * u * b⁻¹ * u⁻¹ ∈ conjSubgroup V g := by
      have e : b * u * b⁻¹ * u⁻¹ = b * (u * b * u⁻¹)⁻¹ := by group
      rw [e]
      exact (conjSubgroup V g).mul_mem hb.1 ((conjSubgroup V g).inv_mem hubu)
    have h3 : b * u * b⁻¹ * u⁻¹ ∈ V₀ ⊓ conjSubgroup V g := ⟨h1', h2⟩
    rw [h65.V₀_inf_conjV, Subgroup.mem_bot] at h3
    calc b * u = (b * u * b⁻¹ * u⁻¹) * (u * b) := by group
      _ = u * b := by rw [h3]; group
  have hCle : V ⊓ centralizer (BOf M V g : Set G) ≤ UOf M V g := by
    have e := Subgroup.relIndex_mul_relIndex (UOf M V g) (V ⊓ centralizer (BOf M V g : Set G)) V
      hUle inf_le_left
    rw [h5] at e
    haveI : (V ⊓ centralizer (BOf M V g : Set G)).IsFiniteRelIndex V :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    have hpos : 0 < (V ⊓ centralizer (BOf M V g : Set G)).relIndex V :=
      Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
    have e1 : (UOf M V g).relIndex (V ⊓ centralizer (BOf M V g : Set G)) = 1 := by
      have := Nat.eq_of_mul_eq_mul_right hpos (e.trans (one_mul _).symm)
      exact this
    exact Subgroup.relIndex_eq_one.1 e1
  obtain ⟨-, K, -, -, -, -, -, hcent, hne⟩ := hstar
  exact hne (hcent.symm.trans (le_antisymm hCle hUle))

theorem w162_inf_conjSubgroup_eq_sup (h1 : W16One G) (h152 : Thm152 G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) :
    V ⊓ conjSubgroup M g = V₀ ⊔ (V ⊓ conjSubgroup V g) := by
  have h65 := h.w162_hyp65 h1 hS hg hc
  have hK := h.w162_V₀_le_K h1 h152 hS hg hc
  have hnot := h.w162_not_inCalOStar h1 hS hg hc
  obtain ⟨hU, -⟩ := h65.six_five_four hK hnot
  rw [NOf_eq M V g h65.le_M] at hU
  exact hU

end Certified

end Cex16

section Certified


theorem w16Five_of_one (h1 : W16One G) (h152 : Thm152 G) : W16Five G := by
  intro hS M V₀ V U S H h hF _ g hgH hc
  have hg : g ∈ centralizer (U : Set G) := hF.2.1 hgH
  rw [h.w162_inf_conjSubgroup_eq_sup h1 h152 hS hg hc, h.w162_inf_conj_V_eq h1 hS hg hc,
    sup_comm]

end Certified

end CFSG.LocalAnalysis.WeakClosure81
