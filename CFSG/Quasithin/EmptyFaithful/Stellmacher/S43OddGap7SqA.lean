module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Gap7

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem comm_Wn_le_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α ρ : Geo H M}
    (hs : Sit43 α) (h3 : bMin H M = 3) (hρ : vtype ρ = false)
    (hS : ∀ δ ∈ nbrs ρ, Nat.card (Vn δ) = 2 ^ 6) : ⁅Wn ρ, Wn ρ⁆ ≤ Zv ρ := by
  obtain ⟨δ, hδ⟩ := exists_adj_of_vtype_false hA hρ
  exact (Subgroup.commutator_mono le_rfl ((hs.of_vtype_false hρ).Wn_le_Qv hA h3.ge)).trans
    (hs.comm_Wn_Qv_le hA h26 h3.ge hρ hδ (hS δ hδ))

theorem sq_Wn_mem_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α ρ : Geo H M}
    (hs : Sit43 α) (h3 : bMin H M = 3) (hρ : vtype ρ = false)
    (hS : ∀ δ ∈ nbrs ρ, Nat.card (Vn δ) = 2 ^ 6) : ∀ x ∈ Wn ρ, x * x ∈ Zv ρ := by
  have hcomm := comm_Wn_le_Zv hA h26 hs h3 hρ hS
  have hcen : ∀ y ∈ Zv ρ, ∀ w ∈ Wn ρ, w * y = y * w := fun y hy w hw =>
    Subgroup.mem_centralizer_iff.mp
      ((hs.of_vtype_false hρ).Wn_le_centralizer_Zv hA h3.ge hy) w hw
  intro x hx
  have hx' := hx
  rw [Sit43.Wn_eq_iSup ρ] at hx'
  refine (Subgroup.iSup_induction (fun l : {l : Geo H M // dist l ρ = 2} => Zv l.1)
    (C := fun x => x ∈ Wn ρ ∧ x * x ∈ Zv ρ) hx'
    (fun l y hy => ⟨Sit43.Zv_le_Wn_of_dist l.2 hy, ?_⟩) ⟨one_mem _, by simp⟩ ?_).2
  · have h2 := (isElemAbelian_Zv hA l.1).2 y hy
    rw [← pow_two, h2]
    exact one_mem _
  · rintro x y ⟨hxW, hx2⟩ ⟨hyW, hy2⟩
    refine ⟨Subgroup.mul_mem _ hxW hyW, ?_⟩
    have hc : x * y * x⁻¹ * y⁻¹ ∈ Zv ρ := hcomm (Subgroup.commutator_mem_commutator hxW hyW)
    have hyx2 : y * (x * x) = x * x * y := hcen _ hx2 y hyW
    have e : x * y * (x * y) = x * y * x⁻¹ * y⁻¹ * (x * x) * (y * y) := by
      calc x * y * (x * y) = x * y * x⁻¹ * y⁻¹ * (y * (x * x) * y) := by group
        _ = x * y * x⁻¹ * y⁻¹ * (x * x * y * y) := by rw [hyx2]
        _ = x * y * x⁻¹ * y⁻¹ * (x * x) * (y * y) := by simp only [mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx2) hy2

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
