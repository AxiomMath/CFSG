module

public import CFSG.Sporadic.Co2HeavyInputs
public import CFSG.Sporadic.Co2Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Sporadic.Co2Heavy

open CFSG.Sporadic.Co2Inv CFSG.Sporadic.Co2Rank CFSG.Sporadic.SmallF2.Native CFSG.Blueprint
open CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.Sporadic.SmallF2

theorem card_le_card_finset {α : Type*} [Finite α] (T : Finset ℕ) (φ : α → ℕ)
    (hφ : Function.Injective φ) (hmem : ∀ x, φ x ∈ T) : Nat.card α ≤ T.card := by
  have h := Nat.card_le_card_of_injective (fun x => (⟨φ x, hmem x⟩ : T))
    (fun x y hxy => hφ (congrArg Subtype.val hxy))
  simpa using h

theorem conj_mul_conj {G : Type*} [Group G] (h a b : G) :
    (h * a * h⁻¹) * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group

theorem conj_conj {G : Type*} [Group G] (s g z : G) :
    s * g * z * (s * g)⁻¹ = s * (g * z * g⁻¹) * s⁻¹ := by group

theorem eq_conj_of_mul_eq {G : Type*} [Group G] {s a r : G} (h : s * a = r * s) :
    r = s * a * s⁻¹ := by
  rw [h, mul_inv_cancel_right]

theorem mul_comm_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mul_self_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) {a : G} (ha : a ∈ E) : a * a = 1 := by
  have := hE.2 a ha
  rwa [pow_two] at this

section Rows

set_option linter.unusedSectionVars false

theorem eltS_val_hRow {k : ℕ} (hk : k < sOrder) :
    (eltS k).val.val = rowsMatrix 22 (hRow k) := eltS_val k hk

end Rows

section Conj

theorem exists_conj_mem_sylowS_of_isPGroup {E : Subgroup NativeSporadic.Co2}
    (hE : IsPGroup 2 E) : ∃ g : NativeSporadic.Co2, ∀ x ∈ E, g * x * g⁻¹ ∈ sylowS := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq NativeSporadic.Co2 Q sylowS'
  refine ⟨g, fun x hx => ?_⟩
  rw [← coe_sylowS', ← hg, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup NativeSporadic.Co2)
    (hQ hx)

end Conj

end CFSG.Sporadic.Co2Heavy
