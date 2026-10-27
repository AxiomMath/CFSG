module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

theorem sl2_transitive : ∀ u v : Fin 2 → ZMod 2, u ≠ 0 → v ≠ 0 → ∃ A : SL(2, ZMod 2), A • u = v := by
  decide +kernel

theorem perm3_commuting_involutions : ∀ x y : Equiv.Perm (Fin 3), x * x = 1 → y * y = 1 →
    x * y = y * x → x = 1 ∨ y = 1 ∨ x = y := by
  decide

theorem perm3_invert : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
    a * b * a⁻¹ * b = 1 := by
  decide

set_option synthInstance.maxSize 2048 in
theorem finite_check_E8 : ∀ a : Matrix (Fin 3) (Fin 3) (ZMod 2), a * a = 1 → a ≠ 1 →
    ∀ b : Matrix (Fin 3) (Fin 3) (ZMod 2), b * b = 1 → b ≠ 1 → a ≠ b → a * b = b * a →
    ∀ c : Matrix (Fin 3) (Fin 3) (ZMod 2), c * c = 1 → c ≠ 1 → c ≠ a → c ≠ b → c ≠ a * b →
      a * c = c * a → b * c = c * b → False := by
  decide +kernel

theorem card_le_four_of_elemAbelian {Γ : Type*} [Group Γ] (e : Γ ≃* ↥(StatedSL 3 (ZMod 2)))
    (A : Subgroup Γ) (hsq : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hfin : Finite Γ := Finite.of_equiv _ e.symm.toEquiv
  have hcardA : (A : Set Γ).ncard = Nat.card A := (_root_.Nat.card_coe_set_eq (A : Set Γ)).symm
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    have h1 : ({1} : Set Γ).ncard < (A : Set Γ).ncard := by
      rw [Set.ncard_singleton, hcardA]; omega
    obtain ⟨a, haA, ha⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
    exact ⟨a, haA, by simpa using ha⟩
  obtain ⟨b, hbA, hb1, hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    have h1 : ({1, a} : Set Γ).ncard < (A : Set Γ).ncard := by
      have h2 := Set.ncard_insert_le (1 : Γ) ({a} : Set Γ)
      have h3 := Set.ncard_singleton a
      rw [hcardA]; omega
    obtain ⟨b, hbA, hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
    exact ⟨b, hbA, hb.1, hb.2⟩
  obtain ⟨c, hcA, hc1, hca, hcb, hcab⟩ : ∃ c ∈ A, c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b := by
    have h1 : ({1, a, b, a * b} : Set Γ).ncard < (A : Set Γ).ncard := by
      have h2 := Set.ncard_insert_le (1 : Γ) ({a, b, a * b} : Set Γ)
      have h3 := Set.ncard_insert_le a ({b, a * b} : Set Γ)
      have h4 := Set.ncard_insert_le b ({a * b} : Set Γ)
      have h5 := Set.ncard_singleton (a * b)
      rw [hcardA]; omega
    obtain ⟨c, hcA, hc⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
    exact ⟨c, hcA, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  let m : Γ → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun x => ((e x : ↥(StatedSL 3 (ZMod 2))) :
    GL (Fin 3) (ZMod 2)).val
  have hm_mul : ∀ x y, m (x * y) = m x * m y := fun x y => by
    simp [m]
  have hm_one : m 1 = 1 := by simp [m]
  have hm_inj : ∀ x y, m x = m y → x = y := fun x y h => by
    apply e.injective
    apply Subtype.ext
    exact Units.ext h
  have hm_sq : ∀ x ∈ A, m x * m x = 1 := fun x hx => by
    rw [← hm_mul, hsq x hx, hm_one]
  have hm_comm : ∀ x ∈ A, ∀ y ∈ A, m x * m y = m y * m x := fun x hx y hy => by
    rw [← hm_mul, ← hm_mul, hc x hx y hy]
  refine finite_check_E8 (m a) (hm_sq a haA) (fun h => ha1 (hm_inj _ _ (h.trans hm_one.symm)))
    (m b) (hm_sq b hbA) (fun h => hb1 (hm_inj _ _ (h.trans hm_one.symm)))
    (fun h => hba (hm_inj _ _ h).symm) (hm_comm a haA b hbA)
    (m c) (hm_sq c hcA) (fun h => hc1 (hm_inj _ _ (h.trans hm_one.symm)))
    (fun h => hca (hm_inj _ _ h)) (fun h => hcb (hm_inj _ _ h))
    (fun h => hcab (hm_inj _ _ (h.trans (hm_mul a b).symm))) (hm_comm a haA c hcA) (hm_comm b hbA c hcA)

end S153E61D

end CFSG.Quasithin
