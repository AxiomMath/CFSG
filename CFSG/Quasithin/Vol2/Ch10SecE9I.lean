module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch10SecBL32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace L32

theorem isU_of_normalizes : ∀ g : Γ, (∀ u : Γ, IsU u → IsU (g * u * g⁻¹)) → IsU g := by
  unfold IsU ent; decide +kernel

theorem ka_sign : ∀ u : Γ, IsU u → (∀ k : Γ, IsKa k → IsEa (u * k * u⁻¹ * k⁻¹)) ∨
    (∀ k : Γ, IsKa k → IsEa (u * k * u⁻¹ * k)) := by
  decide +kernel

theorem kb_sign : ∀ u : Γ, IsU u → (∀ k : Γ, IsKb k → IsEb (u * k * u⁻¹ * k⁻¹)) ∨
    (∀ k : Γ, IsKb k → IsEb (u * k * u⁻¹ * k)) := by
  decide +kernel

theorem ka_cyc : ∀ k k' : Γ, IsKa k → IsKa k' → ¬ IsEa k →
    IsEa k' ∨ IsEa (k' * k⁻¹) ∨ IsEa (k' * k) := by
  decide +kernel

theorem kb_cyc : ∀ k k' : Γ, IsKb k → IsKb k' → ¬ IsEb k →
    IsEb k' ∨ IsEb (k' * k⁻¹) ∨ IsEb (k' * k) := by
  decide +kernel

end L32

structure ParData2 (K E : Subgroup L32.Γ) : Prop where
  sign : ∀ u ∈ L32.U3, (∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ E) ∨ (∀ k ∈ K, u * k * u⁻¹ * k ∈ E)
  cyc : ∀ k ∈ K, ∀ k' ∈ K, k ∉ E → k' ∈ E ∨ k' * k⁻¹ ∈ E ∨ k' * k ∈ E

theorem parData2_a : ParData2 L32.Ka L32.Ea where
  sign := fun u hu => L32.ka_sign u hu
  cyc := fun k hk k' hk' hkE => L32.ka_cyc k k' hk hk' hkE

theorem parData2_b : ParData2 L32.Kb L32.Eb where
  sign := fun u hu => L32.kb_sign u hu
  cyc := fun k hk k' hk' hkE => L32.kb_cyc k k' hk hk' hkE

end CFSG.Quasithin.Vol2.Ch10.SecB
