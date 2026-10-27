module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem zpowers_a₂_fix_W₁ {x : MulAut (IntMod V hV)} (hx : x ∈ Subgroup.zpowers d.S.a₂)
    {w : IntMod V hV} (hw : w ∈ d.S.W₁) : x w = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  clear hx
  have h : d.S.a₂ w = w := d.S.a₂_fix_W₁ hw
  have h' : d.S.a₂.symm w = w := (MulEquiv.symm_apply_eq d.S.a₂).mpr h.symm
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
  | pred n ih => rw [zpow_sub_one, MulAut.mul_apply, MulAut.inv_apply, h', ih]

theorem W₂_eq_commSub_zpowers_a₂ :
    d.S.W₂ = commSub (⊤ : Subgroup (IntMod V hV)) (Subgroup.zpowers d.S.a₂) := by
  have h := d.S.swap.W₁_eq_commSub_a₁ (Or.inr rfl) (fun w => IntMod.sq_eq_one w)
  rwa [d.S.swap_W₁, d.S.swap_a₁] at h

theorem val_commutator_mem_of_mem_autI {Y : Subgroup G} {x : MulAut (IntMod V hV)}
    (hx : x ∈ autI hV Y) {u : IntMod V hV} (hu : u ∈ d.S.W₂) :
    IntMod.val (x u * u⁻¹) ∈ ⁅d.V₂, Y⁆ := by
  obtain ⟨⟨y, hyN⟩, hyY, rfl⟩ := (mem_autI hV).1 hx
  have h1 : IntMod.val (convI hV ⟨y, hyN⟩ u * u⁻¹) = ⁅y, IntMod.val u⁆ := by
    rw [IntMod.val_mul, IntMod.val_inv, ← conj_val hyN, commutatorElement_def]
  rw [h1, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hyY (d.val_mem_V₂ hu)

theorem comm_V₂_eq {Y : Subgroup G} (hY : Y ≤ M ⊓ g1_1516 d.Z₁)
    (hYa : autI hV Y = Subgroup.zpowers d.S.a₂) : ⁅d.V₂, Y⁆ = d.V₂ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    have hxK : x ∈ M ⊓ g1_1516 d.Z₁ := hY hx
    have hxN2 := d.mem_normalizer_V₂ hxK.1 (d.centralizer_le_normalizer ⟨hxK.1, hxK.2⟩)
    have h1 : x * v⁻¹ * x⁻¹ ∈ d.V₂ :=
      (Subgroup.mem_normalizer_iff.mp hxN2 v⁻¹).1 (d.V₂.inv_mem hv)
    have : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact d.V₂.mul_mem hv h1
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (d.mem_V₂_iff).1 hv
    have hle : d.S.W₂ ≤ (⁅d.V₂, Y⁆).comap (valHomI hV) := by
      rw [d.W₂_eq_commSub_zpowers_a₂, commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, u, -, rfl⟩
      have hu : u ∈ d.S.W₁ ⊔ d.S.W₂ := by
        rw [d.S.wsup]
        exact Subgroup.mem_top u
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
      have hcomm : x (u₁ * u₂) * (u₁ * u₂)⁻¹ = x u₂ * u₂⁻¹ := by
        rw [map_mul, d.zpowers_a₂_fix_W₁ hx hu₁, mul_inv_rev]
        calc u₁ * x u₂ * (u₂⁻¹ * u₁⁻¹) = (x u₂ * u₂⁻¹) * (u₁ * u₁⁻¹) := by ac_rfl
          _ = x u₂ * u₂⁻¹ := by rw [mul_inv_cancel, mul_one]
      show IntMod.val (x (u₁ * u₂) * (u₁ * u₂)⁻¹) ∈ ⁅d.V₂, Y⁆
      rw [hcomm]
      exact d.val_commutator_mem_of_mem_autI (hYa ▸ hx) hu₂
    exact hle hw

end Six5Data

end CFSG.Quasithin
