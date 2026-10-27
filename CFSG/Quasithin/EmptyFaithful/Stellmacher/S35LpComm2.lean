module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpW

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

theorem bar_Vn_eq (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m) :
    c.bar (Vn β) = Subgroup.zpowers (zc (c.Dl m)) := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
    rcases imageA hS hneg hp hb c hpl ha a.2 with h | h
    · rw [show c.θ a = 1 from h]
      exact Subgroup.one_mem _
    · rw [show c.θ a = zc (c.Dl m) from h]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    obtain ⟨v, hv, hvs, hθ⟩ := exists_zc hS hneg hp hb c hpl
    rw [← hθ]
    exact c.mem_bar_of_mem hv hvs

theorem img_comm_eq (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m)
    (hZR : Zv α' ≤ ⁅Vn β, Vn α'⁆) :
    c.img ⁅Vn β, Vn α'⁆ = commW orth (Subgroup.zpowers (zc (c.Dl m))) ⊤ := by
  have hA : Vn β ≤ stab α' := (Std.PD_Vn_le_stab hS hp).1
  have h1 := c.img_commSec hA
  rw [bar_Vn_eq hS hneg hp hb c hpl] at h1
  rw [← h1]
  congr 1
  unfold commSec
  rw [Subgroup.commutator_comm (Vn α') (Vn β), sup_eq_left.mpr hZR]

theorem comm_Vn_Wb_le (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m)
    (hZR : Zv α' ≤ ⁅Vn β, Vn α'⁆) (hWQ : Wb β ≤ Qv m) :
    ∀ x ∈ Vn α', ∀ w ∈ Wb β, x * w * x⁻¹ * w⁻¹ ∈ Vn β := by
  intro x hx w hw
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hb.1
  have himg := img_comm_eq hS hneg hp hb c hpl hZR
  have hRV : ⁅Vn β, Vn α'⁆ ≤ Vn β ⊓ Vn α' := Std.PD_comm_le hS hp
  have hwm : w ∈ stab α' ⊓ stab m :=
    Subgroup.mem_inf.mpr ⟨Std.Qv_le_stab hS (Std.mem_nbrs_symm.mp hb.1) (hWQ hw),
      Ch.Qv_le_stab' m (hWQ hw)⟩
  have hws : w ∈ stab α' := hwm.1
  have hmem : c.θ ⟨w, hws⟩ ∈ c.Dl m := c.mem_bar_of_mem (a := w) hwm hws
  have hcen : ∀ y ∈ commW orth (Subgroup.zpowers (zc (c.Dl m))) ⊤,
      orth.act (c.θ ⟨w, hws⟩) y = y := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨x', hx', rfl⟩ := (c.mem_img_iff').mp hy
    refine (c.comm_mem_iff ⟨w, hws⟩ x').mp ?_
    have hc := comm_of_commutator_eq_bot (Std.comm_Vn_Wb hS β) (hRV hx').1 hw
    show w * (x' : G) * w⁻¹ * (x' : G)⁻¹ ∈ Zv α'
    rw [← hc]
    simp
  have hy : w * x * w⁻¹ * x⁻¹ ∈ Vn α' :=
    (Vn α').mul_mem (Ch.conj_mem_Vn hws hx) ((Vn α').inv_mem hx)
  have hπ : c.π ⟨w * x * w⁻¹ * x⁻¹, hy⟩ =
      orth.act (c.θ ⟨w, hws⟩) (c.π ⟨x, hx⟩) * (c.π ⟨x, hx⟩)⁻¹ := by
    rw [← c.π_conj ⟨w, hws⟩ ⟨x, hx⟩, ← map_inv, ← map_mul]
    rfl
  have hin : w * x * w⁻¹ * x⁻¹ ∈ ⁅Vn β, Vn α'⁆ := by
    refine (c.mem_img_iff hZR ⟨_, hy⟩).mp ?_
    rw [hπ, himg]
    exact comm_le_of_cen hD hmem hcen _
  have := (⁅Vn β, Vn α'⁆).inv_mem hin
  have e : (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ := by group
  rw [e] at this
  exact (hRV this).1

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin
