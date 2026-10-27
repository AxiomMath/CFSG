module

public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
import CFSG.Quasithin.Vol2.Ch11SecU1Main
import CFSG.CGT.Timmesfeld75.Config
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.Vol2.Ch11.SecU1

variable {G : Type} [Group G] [Finite G]

theorem exists_generators_of_not_two_involutions {L : Subgroup G}
    (h : SecU1.Setting L) {A : Subgroup G} (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (hI : ∀ x ∈ A, x ∈ L → x ≠ 1 → ∀ y ∈ A, y ∈ L → y ≠ 1 → x = y) :
    ∃ v b : G, v ∈ A ∧ v ∈ L ∧ v ≠ 1 ∧ b ∈ A ∧ b ∉ L ∧
      ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => hA.mul_self_eq_one hx
  have hord : ∀ x ∈ A, x ≠ 1 → orderOf x = 2 := fun x hx hx1 => orderOf_eq_prime (hA.2 x hx) hx1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hA.comm hx hy
  obtain ⟨x₁, hx₁A, hx₁1, -⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card A) 1 1
  obtain ⟨x₂, hx₂A, hx₂1, hx₂x₁⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card A) 1 x₁
  have hne1 : ∀ x ∈ A, x ∉ L → x ≠ 1 := fun x _ hxL hx => hxL (hx ▸ L.one_mem)
  have hpair : ∀ t₁ ∈ A, ∀ t₂ ∈ A, t₁ ∉ L → t₂ ∉ L → t₁ * t₂ ∈ L :=
    fun t₁ h₁ t₂ h₂ h₁L h₂L => h.outer_pair t₁ t₂ h₁L h₂L (hord t₁ h₁ (hne1 t₁ h₁ h₁L))
      (hord t₂ h₂ (hne1 t₂ h₂ h₂L)) (hcomm t₁ h₁ t₂ h₂)
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx => CFSG.CGT.Timmesfeld75.elemAbelian_inv hA hx
  obtain ⟨v, hvA, hvL, hv1⟩ : ∃ v ∈ A, v ∈ L ∧ v ≠ 1 := by
    by_cases h₁ : x₁ ∈ L
    · exact ⟨x₁, hx₁A, h₁, hx₁1⟩
    by_cases h₂ : x₂ ∈ L
    · exact ⟨x₂, hx₂A, h₂, hx₂1⟩
    refine ⟨x₁ * x₂, A.mul_mem hx₁A hx₂A, hpair x₁ hx₁A x₂ hx₂A h₁ h₂, fun e => hx₂x₁ ?_⟩
    calc x₂ = x₁⁻¹ * (x₁ * x₂) := by group
      _ = x₁ := by rw [e, mul_one, hinv x₁ hx₁A]
  obtain ⟨b, hbA, hbL⟩ : ∃ b ∈ A, b ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hx₂x₁ (hI x₂ hx₂A (hcon x₂ hx₂A) hx₂1 x₁ hx₁A (hcon x₁ hx₁A) hx₁1)
  have hA4' : ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    by_cases hxL : x ∈ L
    · exact Or.inr (Or.inl (hI x hx hxL hx1 v hvA hvL hv1))
    have hxb : x * b ∈ L := hpair x hx b hbA hxL hbL
    have hxe : x = x * b * b := by rw [mul_assoc, hsq b hbA, mul_one]
    by_cases hxb1 : x * b = 1
    · exact Or.inr (Or.inr (Or.inl (by rw [hxe, hxb1, one_mul])))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [hxe, hI (x * b) (A.mul_mem hx hbA) hxb hxb1 v hvA hvL hv1])))
  exact ⟨v, b, hvA, hvL, hv1, hbA, hbL, hA4'⟩

end CFSG.LocalAnalysis.WeakClosure81
