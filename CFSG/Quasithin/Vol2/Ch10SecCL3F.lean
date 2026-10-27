module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.Vol2.Ch10SecBL32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.L3F

open CFSG.Quasithin.Vol2.Ch10.SecB.L32

abbrev e0 : L3.Vec := ![1, 0, 0]

abbrev e1 : L3.Vec := ![0, 1, 0]

@[expose] def γ1 : L3.Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def ebA : L3.Γ := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def ebB : L3.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

set_option maxRecDepth 100000 in
theorem act_e0_iff : ∀ γ : L3.Γ, L3.act γ e0 = e0 ↔ IsPa γ := by
  unfold L3.act IsPa ent; decide +kernel

set_option maxRecDepth 100000 in
theorem fix_U3 : ∀ x : L3.Vec, (∀ γ : L3.Γ, IsU γ → L3.act γ x = x) → x = 0 ∨ x = e0 := by
  unfold L3.act IsU ent; decide +kernel

set_option maxRecDepth 100000 in
theorem fix_Ea : ∀ x : L3.Vec, (∀ γ : L3.Γ, IsEa γ → L3.act γ x = x) → x = 0 ∨ x = e0 := by
  unfold L3.act IsEa IsPa ent; decide +kernel

set_option maxRecDepth 100000 in
theorem pa_mul_ka : ∀ γ : L3.Γ, IsPa γ → ¬ IsKa γ → IsKa (γ⁻¹ * γ1) := by
  unfold IsKa IsPa ent γ1; decide +kernel

set_option maxRecDepth 100000 in
theorem u3_pair : ∀ g h : L3.Γ, IsU g → IsU h → g * g = 1 → h * h = 1 → g * h = h * g →
    g ≠ 1 → h ≠ 1 → g ≠ h → (IsEa g ∧ IsEa h) ∨ (IsEb g ∧ IsEb h) := by
  unfold IsU IsEa IsEb IsPa IsPb ent; decide +kernel

set_option maxRecDepth 100000 in
theorem ebA_cim : ∀ x : L3.Vec, L3.act ebA x - x = 0 ∨ L3.act ebA x - x = e0 := by
  unfold L3.act ebA; decide

set_option maxRecDepth 100000 in
theorem ebB_cim : ∀ x : L3.Vec, L3.act ebB x - x = 0 ∨ L3.act ebB x - x = e1 := by
  unfold L3.act ebB; decide

set_option maxRecDepth 100000 in
theorem pa_comm_three : ∀ γ : L3.Γ, IsPa γ → ¬ IsEa γ →
    ∃ δ : L3.Γ, IsPa δ ∧ γ * δ * γ⁻¹ * δ⁻¹ ≠ 1 ∧
      (γ * δ * γ⁻¹ * δ⁻¹) * (γ * δ * γ⁻¹ * δ⁻¹) * (γ * δ * γ⁻¹ * δ⁻¹) = 1 := by
  unfold IsPa IsEa ent; decide +kernel

set_option maxRecDepth 100000 in
theorem eb_span : ∀ g h : L3.Γ, IsEb g → IsEb h → g ≠ 1 → h ≠ 1 → g ≠ h →
    (ebA = g ∨ ebA = h ∨ ebA = g * h) ∧ (ebB = g ∨ ebB = h ∨ ebB = g * h) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ea_span : ∀ g h : L3.Γ, IsEa g → IsEa h → g ≠ 1 → h ≠ 1 → g ≠ h →
    ∀ e : L3.Γ, IsEa e → e = 1 ∨ e = g ∨ e = h ∨ e = g * h := by
  decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecC.L3F
