module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transfer of a reflected odd subgroup into `U`

If an odd subgroup centralizes an outer involution `r`, while `t` inverts it,
and an element `y` in the centralizer of `tr` conjugates `r` to `t`, then the
conjugate subgroup `R^y` lies in `H = C_G(t)`.  The odd-subgroup decomposition
of `H = S U` then places it in `U`, and the same conjugation identities show
that it is inverted by `r`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Conjugate an odd reflected subgroup from `C_E(r)` into `U`, preserving
inversion by the outer involution. -/
public theorem secondCase_linear_outer_subgroup_transfer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    {r y : G} (R : Subgroup G)
    (hRcent : R ≤ Subgroup.centralizer ({r} : Set G))
    (hRodd : Odd (Nat.card R))
    (hconj : y * r * y⁻¹ = c.t)
    (htr : Commute c.t r)
    (hytr : Commute y (c.t * r))
    (htinv : ∀ x : G, x ∈ R → c.t * x * c.t⁻¹ = x⁻¹) :
    let Ry : Subgroup G := R.map (MulAut.conj y).toMonoidHom
    Ry ≤ c.U ∧
      (∀ x : G, x ∈ Ry → r * x * r⁻¹ = x⁻¹) := by
  let Ry : Subgroup G := R.map (MulAut.conj y).toMonoidHom
  have hprod : y * (c.t * r) * y⁻¹ = c.t * r := by
    rw [hytr.eq]
    group
  have hconjt : y * c.t * y⁻¹ = r := by
    calc
      y * c.t * y⁻¹ = (y * (c.t * r) * y⁻¹) *
          (y * r * y⁻¹)⁻¹ := by group
      _ = (c.t * r) * c.t⁻¹ := by rw [hprod, hconj]
      _ = r := by
        rw [htr.eq]
        rw [inv_eq_of_mul_eq_one_right
          (by simpa [pow_two] using c.t_involution.2)]
        calc
          r * c.t * c.t = r * (c.t * c.t) := by group
          _ = r := by
            rw [show c.t * c.t = 1 by
              simpa [pow_two] using c.t_involution.2]
            simp
  have hRyH : Ry ≤ c.H := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
    have hxr : x * r = r * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hRcent hx)
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    change (y * x * y⁻¹) * c.t = c.t * (y * x * y⁻¹)
    calc
      (y * x * y⁻¹) * c.t = (y * x * y⁻¹) *
          (y * r * y⁻¹) := by rw [hconj]
      _ = y * (x * r) * y⁻¹ := by group
      _ = y * (r * x) * y⁻¹ := by rw [hxr]
      _ = (y * r * y⁻¹) * (y * x * y⁻¹) := by group
      _ = c.t * (y * x * y⁻¹) := by rw [hconj]
  have hRycard : Nat.card Ry = Nat.card R := by
    dsimp [Ry]
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hRyodd : Odd (Nat.card Ry) := by
    rw [hRycard]
    exact hRodd
  have hRyU : Ry ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hRyH
      hRyodd.coprime_two_left
  refine ⟨hRyU, ?_⟩
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
  calc
    r * (y * x * y⁻¹) * r⁻¹ =
        (y * c.t * y⁻¹) * (y * x * y⁻¹) *
          (y * c.t * y⁻¹)⁻¹ := by rw [hconjt]
    _ = y * (c.t * x * c.t⁻¹) * y⁻¹ := by group
    _ = y * x⁻¹ * y⁻¹ := by rw [htinv x hx]
    _ = (y * x * y⁻¹)⁻¹ := by group

end CFSG.GorensteinWalter
