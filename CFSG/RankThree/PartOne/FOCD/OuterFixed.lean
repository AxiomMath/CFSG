module

public import CFSG.RankThree.PartOne.TCF.Simple
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne

theorem mem_component_of_simple_layer {T : Type} [Group T] [Finite T] {F E : Subgroup T}
    (hE : IsComponentOf F E) (N : Subgroup ↥F) (hNs : IsSimpleGroup ↥N)
    (hNnc : ∃ a b : ↥N, a * b ≠ b * a) (hcomm : commutator ↥F ≤ N) (hsq : ∀ y : ↥F, y ^ 2 ∈ N)
    {p : ℕ} (hp : Odd p) (y : ↥F) (hyp : y ^ p = 1) : (y : T) ∈ E := by
  classical
  set N' : Subgroup T := N.map F.subtype with hN'
  have hN'F : N' ≤ F := Subgroup.map_subtype_le N
  have hFF : ⁅F, F⁆ = (commutator ↥F).map F.subtype := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hFN' : ⁅F, F⁆ ≤ N' := by
    rw [hFF]
    exact Subgroup.map_mono hcomm
  have hns : ¬ Group.IsSolvable ↥N := by
    intro h
    obtain ⟨a, b, hab⟩ := hNnc
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 h a b)
  have hsimple : TCF.SimpleOrBot N' :=
    TCF.simpleOrBot_of_mulEquiv_simple (G₀ := ↥N) hns
      (Subgroup.equivMapOfInjective N F.subtype F.subtype_injective)
  have hEN : E = N' := TCF.component_eq_of_simpleOrBot hN'F hFN' hsimple hE
  have hyN : y ∈ N := by
    obtain ⟨k, hk⟩ := hp
    have h3 : y = ((y ^ 2) ^ k)⁻¹ := by
      rw [← pow_mul]
      have h4 : y ^ (2 * k) * y = 1 := by
        rw [← pow_succ, ← hk]
        exact hyp
      exact eq_inv_of_mul_eq_one_right h4
    rw [h3]
    exact N.inv_mem (N.pow_mem (hsq y) k)
  rw [hEN]
  exact ⟨y, hyN, rfl⟩

end CFSG.RankThree.PartOne.FOCD
