module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

structure G2Loc {N : Type} [Group N] (P : Subgroup N) (z : N) (T Q Tp : Subgroup N) : Prop where
  z_ne : z ≠ 1
  z_sq : z * z = 1
  T_syl : IsSylowTwoOf T P
  T_card : Nat.card T = 64
  T_Z : ∀ w ∈ T, (∀ t ∈ T, t * w = w * t) → w = 1 ∨ w = z
  T_N : ∀ h ∈ P, (∀ t ∈ T, h * t * h⁻¹ ∈ T) → (∀ t ∈ T, h⁻¹ * t * h ∈ T) → h ∈ T
  Q_le : Q ≤ T
  Q_card : Nat.card Q = 32
  Q_norm : ∀ h ∈ P, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q
  Q_comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z
  Q_Z : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z
  Q_nonab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x
  Tp_le : Tp ≤ T
  Tp_card : Nat.card T = 2 * Nat.card Tp
  z_mem : z ∈ Tp
  Tp_norm : ∀ h ∈ P, ∀ q ∈ Q, (q ∈ Tp ↔ h * q * h⁻¹ ∈ Tp)
  out_ex : ∃ v ∈ Q, v ∉ Tp ∧ v * v = 1
  out_pair : ∀ v ∈ Q, v ∉ Tp → v * v = 1 →
    ∃ a ∈ Q, ∃ b ∈ Q, a * v = v * a ∧ b * v = v * b ∧ a * b * a⁻¹ * b⁻¹ = z
  out_t : ∀ v ∈ Q, v ∉ Tp → v * v = 1 →
    ∃ t ∈ T, t * v * t⁻¹ * v⁻¹ ≠ 1 ∧ t * v * t⁻¹ * v⁻¹ ≠ z

namespace G2Loc

variable {N : Type} [Group N] {P : Subgroup N} {z : N} {T Q Tp : Subgroup N}

theorem z_mem_P (L : G2Loc P z T Q Tp) : z ∈ P := L.T_syl.1 (L.Tp_le L.z_mem)

end G2Loc

theorem isSylowTwoOf_map_subgroupOf {N G : Type} [Group N] [Group G] {P T : Subgroup N}
    (φ : ↥P →* G) (hφ : Function.Injective φ) (h : IsSylowTwoOf T P) :
    IsSylowTwoOf ((T.subgroupOf P).map φ) φ.range := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h1 : IsPGroup 2 (T.subgroupOf P) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
    exact h1.of_equiv ((T.subgroupOf P).equivMapOfInjective φ hφ)
  · change ¬ 2 ∣ ((T.subgroupOf P).map φ).relIndex φ.range
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hφ,
      Subgroup.relIndex_top_right]
    exact hidx

theorem card_map_subgroupOf {N G : Type} [Group N] [Group G] {P X : Subgroup N}
    (φ : ↥P →* G) (hφ : Function.Injective φ) (hX : X ≤ P) :
    Nat.card ((X.subgroupOf P).map φ) = Nat.card X :=
  (Subgroup.card_map_of_injective hφ).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv)

end CFSG.Quasithin.H13.F431.G2Two
