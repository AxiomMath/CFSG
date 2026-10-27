module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Fix7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem exists_isElemAbelian_fix_of_ne_one (hK : Nat.card S.K = 8) {M : Type*} [Group M]
    [Finite M] (φ : M →* MulAut W) (hΩr : S.omega ≤ φ.range) {E : Subgroup M}
    (hE : IsElemAbelian 7 E) (hEc : 7 ^ 3 ≤ Nat.card E)
    (hker : ∀ E' : Subgroup M, IsElemAbelian 7 E' → E' ≤ φ.ker → Nat.card E' ≤ 7)
    (hrange : ¬ 7 ^ 3 ∣ Nat.card φ.range) {w : W} (hw : w ≠ 1) :
    ∃ E' : Subgroup M, IsElemAbelian 7 E' ∧ 7 ^ 2 ≤ Nat.card E' ∧ ∀ x ∈ E', φ x w = w := by
  obtain ⟨g, hg0, hg7, hgw⟩ := exists_orderOf_eq_seven_of_ne_one S hK hw
  have hgr : g ∈ φ.range := hΩr (omega0_le_omega S hg0)
  obtain ⟨E', hE', hE'c, hE'g⟩ :=
    Om8Lift.exists_isElemAbelian_map_le_zpowers φ Nat.prime_seven hE hEc hker hrange hgr hg7
  refine ⟨E', hE', hE'c, fun x hx => ?_⟩
  have hmem : φ x ∈ Subgroup.zpowers g := hE'g (Subgroup.mem_map_of_mem φ hx)
  have hstab : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut W) w :=
    Subgroup.zpowers_le.2 ((MulAction.mem_stabilizer_iff).2 hgw)
  exact (MulAction.mem_stabilizer_iff.1 (hstab hmem))

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
