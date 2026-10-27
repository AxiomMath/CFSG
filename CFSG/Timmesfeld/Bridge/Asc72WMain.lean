module

public import CFSG.Timmesfeld.Bridge.Asc72WIso
public import CFSG.Timmesfeld.Bridge.Asc72WreathConn
public import CFSG.Timmesfeld.Bridge.Asc72Theorem

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open Equiv CFSG.Timmesfeld.Connectivity SemidirectProduct

theorem reach_of_reach_mulEquiv {X Y : Type*} [Group X] [Group Y] (Φ : X ≃* Y) {D : Set X}
    {E : Set Y} (hE : ∀ g ∈ E, Φ.symm g ∈ D) {a b : Y} (h : Reach E a b) :
    Reach D (Φ.symm a) (Φ.symm b) := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih =>
    exact reach_trans ih (reach_of_commute (hE _ hbc.1) (hE _ hbc.2.1) (hbc.2.2.map Φ.symm))

theorem wreathInput : WreathInput := by
  intro G _ _ D hS hrad hdisc M hM hMs
  have := hM.1
  obtain ⟨W⟩ := nonempty_wreathData hS hrad hM hMs
  obtain ⟨f, hf, Φ, hΦ⟩ := W.exists_mulEquiv_l2Wreath hS (centralizer_eq_bot_of_minimal hS hrad hM)
  refine ⟨f, W.r, hf, ?_, ⟨Φ⟩⟩
  have hr2 := W.two_le
  by_contra hn
  have hn' : W.r = 2 ∨ 5 ≤ W.r := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hdisc
  set τ : L2Wreath f W.r := inr (Equiv.swap (⟨0, by omega⟩ : Fin W.r) ⟨1, by omega⟩) with hτdef
  have hτ : ∀ u ∈ D, IsConj τ (Φ u) := by
    intro u hu
    obtain ⟨i, j, hij, h1, h2, h3⟩ := hΦ u hu
    exact (WreathConn.isConj_inr_swap_iff (by simp [Fin.ext_iff]) (Φ u)).mpr
      ⟨i, j, hij, h1, h2, h3⟩
  have hE : ∀ g ∈ {g : L2Wreath f W.r | IsConj τ g}, Φ.symm g ∈ D := by
    intro g hg
    obtain ⟨c, rfl⟩ := isConj_iff.mp ((hτ x hx).symm.trans hg)
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hS.conj_mem _ hx
  have hreach := reach_of_reach_mulEquiv Φ hE
    (reach_wreathClass hf hn' (Φ x) (Φ y) (hτ x hx) (hτ y hy))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at hreach
  exact hxy hreach

end CFSG.Timmesfeld.Bridge.Asc72
