module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin

theorem relIndex_inf_stabilizer_eq_ncard_orbit {W : Type*} [CommGroup W]
    (P : Subgroup (MulAut W)) (w : W) :
    (P ⊓ MulAction.stabilizer (MulAut W) w).relIndex P = (MulAction.orbit ↥P w).ncard := by
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex, MulAction.stabilizer_subgroupOf,
    MulAction.index_stabilizer]

theorem mem_gammaCheck_of_orbit_subset {W : Type*} [CommGroup W] [Finite W]
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 P) {k : ℕ} {w : W} {S : Set W}
    (hS : ∀ g ∈ P, g w ∈ S) (hcard : S.ncard ≤ 2 ^ k) : w ∈ E3.gammaCheck k P := by
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  have hXP : P ⊓ MulAction.stabilizer (MulAut W) w ≤ P := inf_le_left
  have hw : w ∈ fixV (P ⊓ MulAction.stabilizer (MulAut W) w) := fun x hx =>
    MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hx).2
  have horb : MulAction.orbit ↥P w ⊆ S := by
    rintro _ ⟨g, rfl⟩
    exact hS g.1 g.2
  have hle : (P ⊓ MulAction.stabilizer (MulAut W) w).relIndex P ≤ 2 ^ k := by
    rw [relIndex_inf_stabilizer_eq_ncard_orbit]
    exact (Set.ncard_le_ncard horb (Set.toFinite S)).trans hcard
  have hm : E3.mQuot P (P ⊓ MulAction.stabilizer (MulAut W) w) ≤ k := by
    rw [E3.relIndex_eq_two_pow hP] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hle2 : fixV (P ⊓ MulAction.stabilizer (MulAut W) w) ≤ E3.gammaCheck k P :=
    le_iSup_of_le _ (le_iSup₂_of_le hXP hm le_rfl)
  exact hle2 hw

end CFSG.ASVolI.ChH
