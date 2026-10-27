module

public import CFSG.Quasithin.Vol2.Ch10SecBL32Over

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

theorem ea_le : ∀ k : Γ, IsEa k → IsKa k ∧ IsU k := by
  unfold IsEa IsKa IsPa IsU ent; decide +kernel
theorem eb_le : ∀ k : Γ, IsEb k → IsKb k ∧ IsU k := by
  unfold IsEb IsKb IsPb IsU ent; decide +kernel
theorem ka_normal : ∀ g k : Γ, IsPa g → IsKa k → IsKa (g * k * g⁻¹) := by
  unfold IsKa IsPa ent; decide +kernel
theorem ea_normal : ∀ g k : Γ, IsPa g → IsEa k → IsEa (g * k * g⁻¹) := by
  unfold IsEa IsPa ent; decide +kernel
theorem kb_normal : ∀ g k : Γ, IsPb g → IsKb k → IsKb (g * k * g⁻¹) := by
  unfold IsKb IsPb ent; decide +kernel
theorem eb_normal : ∀ g k : Γ, IsPb g → IsEb k → IsEb (g * k * g⁻¹) := by
  unfold IsEb IsPb ent; decide +kernel
theorem ka_cube : ∀ k : Γ, IsKa k → IsEa (k * k * k) := by
  unfold IsEa IsKa IsPa ent; decide +kernel
theorem kb_cube : ∀ k : Γ, IsKb k → IsEb (k * k * k) := by
  unfold IsEb IsKb IsPb ent; decide +kernel
theorem ka_out : ∀ g : Γ, IsPa g → ¬ IsKa g → g * g * g * g = 1 := by
  unfold IsKa IsPa ent; decide +kernel
theorem kb_out : ∀ g : Γ, IsPb g → ¬ IsKb g → g * g * g * g = 1 := by
  unfold IsKb IsPb ent; decide +kernel
theorem ka_two : ∀ k : Γ, IsKa k → k * k * k * k = 1 → IsEa k := by
  unfold IsEa IsKa IsPa ent; decide +kernel
theorem kb_two : ∀ k : Γ, IsKb k → k * k * k * k = 1 → IsEb k := by
  unfold IsEb IsKb IsPb ent; decide +kernel
theorem ka_gen : ∀ k : Γ, IsKa k → ∃ a : Γ, IsKa a ∧ a * a * a = 1 ∧
    a⁻¹ * k * (a⁻¹ * k) * (a⁻¹ * k) = 1 := by
  unfold IsKa IsPa ent; decide +kernel
theorem kb_gen : ∀ k : Γ, IsKb k → ∃ a : Γ, IsKb a ∧ a * a * a = 1 ∧
    a⁻¹ * k * (a⁻¹ * k) * (a⁻¹ * k) = 1 := by
  unfold IsKb IsPb ent; decide +kernel
theorem u_ka : ∀ g : Γ, IsU g → IsKa g → IsEa g := by
  unfold IsEa IsKa IsPa IsU ent; decide +kernel
theorem u_kb : ∀ g : Γ, IsU g → IsKb g → IsEb g := by
  unfold IsEb IsKb IsPb IsU ent; decide +kernel
theorem pa_pb : ∀ g : Γ, IsPa g → IsPb g → IsU g := by
  unfold IsPa IsPb IsU ent; decide +kernel
theorem ka_mul_u : ∀ g : Γ, IsPa g → ∃ u ∈ uList, IsKa (g * u) := by
  unfold uList IsKa IsPa ent; decide +kernel
theorem kb_mul_u : ∀ g : Γ, IsPb g → ∃ u ∈ uList, IsKb (g * u) := by
  unfold uList IsKb IsPb ent; decide +kernel

theorem ka_inv : ∃ d ∈ uList, ∀ k : Γ, IsKa k → IsEa (d * k * d⁻¹ * k) := by
  unfold uList IsEa IsKa IsPa ent; decide +kernel

theorem kb_inv : ∃ d ∈ uList, ∀ k : Γ, IsKb k → IsEb (d * k * d⁻¹ * k) := by
  unfold uList IsEb IsKb IsPb ent; decide +kernel

theorem card_U : (Finset.univ.filter IsU).card = 8 := by unfold IsU ent; decide +kernel
theorem card_Pa : (Finset.univ.filter IsPa).card = 24 := by unfold IsPa ent; decide +kernel
theorem card_Pb : (Finset.univ.filter IsPb).card = 24 := by unfold IsPb ent; decide +kernel
theorem card_Ka : (Finset.univ.filter IsKa).card = 12 := by
  unfold IsKa IsPa ent; decide +kernel
theorem card_Kb : (Finset.univ.filter IsKb).card = 12 := by
  unfold IsKb IsPb ent; decide +kernel
theorem card_Ea : (Finset.univ.filter IsEa).card = 4 := by
  unfold IsEa IsPa ent; decide +kernel
theorem card_Eb : (Finset.univ.filter IsEb).card = 4 := by
  unfold IsEb IsPb ent; decide +kernel

theorem u_not_normal_a : ∃ g : Γ, IsPa g ∧ ∃ u ∈ uList, ¬ IsU (g * u * g⁻¹) := by
  unfold uList IsPa IsU ent; decide +kernel

theorem u_not_normal_b : ∃ g : Γ, IsPb g ∧ ∃ u ∈ uList, ¬ IsU (g * u * g⁻¹) := by
  unfold uList IsPb IsU ent; decide +kernel

theorem graph_swap_a : ∀ A : Γ, (∀ u ∈ uList, IsU (A * (u⁻¹).transpose * A⁻¹)) →
    ∀ p : Γ, IsPa p → IsPb (A * (p⁻¹).transpose * A⁻¹) := by
  unfold uList IsPa IsPb IsU ent; decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
