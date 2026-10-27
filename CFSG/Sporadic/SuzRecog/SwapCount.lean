module

public import CFSG.Sporadic.Co1Patterson.SettingOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial

theorem card_sq_eq_of_swap {G : Type*} [Group G] {z w u : G} (h1 : u * z * u⁻¹ = w)
    (h2 : u * w * u⁻¹ = z) :
    Nat.card {x : G // x * z = z * x ∧ x * w = w * x ∧ x * x = z} =
      Nat.card {x : G // x * z = z * x ∧ x * w = w * x ∧ x * x = w} := by
  have key : ∀ {a b : G} (v : G), v * a * v⁻¹ = b → ∀ x : G, x * a = a * x →
      v * x * v⁻¹ * b = b * (v * x * v⁻¹) := by
    intro a b v hv x hx
    rw [← hv]
    calc v * x * v⁻¹ * (v * a * v⁻¹) = v * (x * a) * v⁻¹ := by group
      _ = v * (a * x) * v⁻¹ := by rw [hx]
      _ = v * a * v⁻¹ * (v * x * v⁻¹) := by group
  have h1' : u⁻¹ * w * u⁻¹⁻¹ = z := by rw [← h1]; group
  have h2' : u⁻¹ * z * u⁻¹⁻¹ = w := by rw [← h2]; group
  refine Nat.card_congr
    { toFun := fun x => ⟨u * x.1 * u⁻¹, key u h2 x.1 x.2.2.1, key u h1 x.1 x.2.1, ?_⟩
      invFun := fun x => ⟨u⁻¹ * x.1 * u⁻¹⁻¹, key u⁻¹ h1' x.1 x.2.2.1,
        key u⁻¹ h2' x.1 x.2.1, ?_⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  · calc u * x.1 * u⁻¹ * (u * x.1 * u⁻¹) = u * (x.1 * x.1) * u⁻¹ := by group
      _ = w := by rw [x.2.2.2, h1]
  · calc u⁻¹ * x.1 * u⁻¹⁻¹ * (u⁻¹ * x.1 * u⁻¹⁻¹) = u⁻¹ * (x.1 * x.1) * u⁻¹⁻¹ := by group
      _ = z := by rw [x.2.2.2, h1']

variable {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)

omit [Finite G] in
theorem card_M_sq_eq (w : S.M) (t : G) :
    Nat.card {x : S.M // x * w = w * x ∧ (x * x : S.M) = (t : G)} =
      Nat.card {x : G // x * S.z = S.z * x ∧ x * w = w * x ∧ x * x = t} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, S.mem_M_iff.mp x.1.2, congrArg Subtype.val x.2.1, x.2.2⟩
      invFun := fun x => ⟨⟨x.1, S.mem_M_iff.mpr x.2.1⟩, Subtype.ext x.2.2.1, x.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_sq_eq_of_mulEquiv (h5 : 5 ≤ finrank (ZMod 2) S.Qt)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) {T : Type*} [Group T]
    (σ : S.M ≃* T) {w : S.M} (hwQ : (w : G) ∈ S.QG) (hw2 : orderOf (w : G) = 2)
    (hwz : (w : G) ≠ S.z) :
    Nat.card {y : T // y * σ w = σ w * y ∧ y * y = σ S.zM} =
      Nat.card {y : T // y * σ w = σ w * y ∧ y * y = σ w} := by
  obtain ⟨g, hg, hne⟩ := hNWC
  have hconj := Co1Patterson.isConj_of_mem_QG_of_omega S h5 hΩ hg hne hwQ hw2
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨u, -, h1, h2⟩ := S.exists_swap hc hwQ hwz
  have hσ : ∀ t : S.M, Nat.card {y : T // y * σ w = σ w * y ∧ y * y = σ t} =
      Nat.card {x : S.M // x * w = w * x ∧ (x * x : S.M) = (t : G)} := fun t =>
    Nat.card_congr
      { toFun := fun y => ⟨σ.symm y.1, by
          refine ⟨σ.injective ?_, ?_⟩
          · rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
            exact y.2.1
          · rw [← map_mul, y.2.2, MulEquiv.symm_apply_apply]⟩
        invFun := fun x => ⟨σ x.1, by rw [← map_mul, ← map_mul, x.2.1], by
          rw [← map_mul]
          congr 1
          exact Subtype.ext x.2.2⟩
        left_inv := fun y => Subtype.ext (σ.apply_symm_apply _)
        right_inv := fun x => Subtype.ext (σ.symm_apply_apply _) }
  rw [hσ, hσ, card_M_sq_eq, card_M_sq_eq]
  exact card_sq_eq_of_swap h1 h2

end CFSG.Sporadic.SuzRecog
