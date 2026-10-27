module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrArith

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

section WeylA

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}

theorem ggWeylOfType_A_card {A : Subgroup (MulAut ↥Bs)} {m : ℕ}
    (h : GGWeylOfType p (CoxeterMatrix.A m) A) : Nat.card ↥A = (m + 1).factorial := by
  obtain ⟨Ê, -⟩ := exists_permEquiv_of_ggWeylOfType_A h
  rw [← Nat.card_congr Ê.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem ggWeylOfType_A_no_frame [Fact p.Prime] [Finite ↥Bs] (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) {A : Subgroup (MulAut ↥Bs)} {m : ℕ}
    (h : GGWeylOfType p (CoxeterMatrix.A m) A) {c₁ c₂ : MulAut ↥Bs} (h₁ : c₁ ∈ A) (h₂ : c₂ ∈ A)
    (r₁ : GGIsReflection p c₁) (r₂ : GGIsReflection p c₂) : ¬ 4 ∣ orderOf (c₁ * c₂) := by
  obtain ⟨Ê, hÊ⟩ := exists_permEquiv_of_ggWeylOfType_A h
  let E : Equiv.Perm (Fin (m + 1)) →* MulAut ↥Bs := A.subtype.comp Ê.toMonoidHom
  have hinj : Function.Injective E := Subtype.val_injective.comp Ê.injective
  have hm : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    subst hm0
    have : Subsingleton (Equiv.Perm (Fin 1)) := inferInstance
    have e₁ : c₁ = 1 := by
      have h' : Ê (Ê.symm ⟨c₁, h₁⟩) = ⟨c₁, h₁⟩ := Ê.apply_symm_apply _
      have hs : Ê.symm ⟨c₁, h₁⟩ = 1 := Subsingleton.elim _ _
      rw [hs, map_one] at h'
      exact congrArg Subtype.val h'.symm
    rw [e₁] at r₁
    obtain ⟨-, hfix⟩ := r₁
    have hcard : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs := by
      simp
    rw [hcard] at hfix
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have := Fact.out (p := p.Prime)
    nlinarith [this.two_le]
  have hsw : ∀ x y : Fin (m + 1), x ≠ y → GGIsReflection p (E (Equiv.swap x y)) := by
    intro x y hxy
    refine ggIsReflection_swap_of_swap E (a := ((⟨0, hm⟩ : Fin m).castSucc))
      (b := ((⟨0, hm⟩ : Fin m).succ)) ?_ (hÊ ⟨0, hm⟩) hxy
    exact (Fin.castSucc_lt_succ).ne
  obtain ⟨π₁, hπ₁⟩ : ∃ π, E π = c₁ := ⟨Ê.symm ⟨c₁, h₁⟩, by
    show ((Ê (Ê.symm ⟨c₁, h₁⟩) : A) : MulAut ↥Bs) = c₁
    rw [Ê.apply_symm_apply]⟩
  obtain ⟨π₂, hπ₂⟩ : ∃ π, E π = c₂ := ⟨Ê.symm ⟨c₂, h₂⟩, by
    show ((Ê (Ê.symm ⟨c₂, h₂⟩) : A) : MulAut ↥Bs) = c₂
    rw [Ê.apply_symm_apply]⟩
  subst hπ₁ hπ₂
  obtain ⟨a, b, -, rfl⟩ := isSwap_of_ggIsReflection hp2 hBs E hinj hsw r₁
  obtain ⟨c, d, -, rfl⟩ := isSwap_of_ggIsReflection hp2 hBs E hinj hsw r₂
  rw [← map_mul, orderOf_injective E hinj]
  exact not_four_dvd_orderOf_swap_mul_swap a b c d

theorem ggWeylOfType_A_no_order_nine {A : Subgroup (MulAut ↥Bs)} {m : ℕ} (hm : m ≤ 4)
    (h : GGWeylOfType p (CoxeterMatrix.A m) A) {c : MulAut ↥Bs} (hc : c ∈ A) :
    ¬ 9 ∣ orderOf c := fun h9 => by
  have h1 : orderOf (⟨c, hc⟩ : ↥A) ∣ Nat.card ↥A := orderOf_dvd_natCard _
  rw [ggWeylOfType_A_card h, Subgroup.orderOf_mk] at h1
  have h2 := h9.trans h1
  interval_cases m <;> revert h2 <;> decide

end WeylA

theorem ggAutomizer_fix_of_centralizes {G : Type} [Group G] {Bs K' : Subgroup G} {y' : G}
    (hy : y' ∈ Bs) (hc : ∀ k ∈ K', y' * k = k * y') {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer K' Bs) : φ ⟨y', hy⟩ = ⟨y', hy⟩ := by
  have hle : ggAutomizer K' Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨y', hy⟩ : ↥Bs) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨g, hgK, hgN, hφg⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show ((φ ⟨y', hy⟩ : ↥Bs) : G) = y'
    rw [hφg ⟨y', hy⟩]
    have := hc g hgK
    calc g * y' * g⁻¹ = (g * y') * g⁻¹ := rfl
      _ = (y' * g) * g⁻¹ := by rw [← this]
      _ = y' := by group
  exact MulAction.mem_stabilizer_iff.mp (hle hφ)

end CFSG.StandardType

end
