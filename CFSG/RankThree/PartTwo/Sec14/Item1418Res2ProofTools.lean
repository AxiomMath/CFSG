module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Proof1418Res2

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_conj_self {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hyx' : y = x := by
      have h' := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using h'
    rwa [← hyx']

end Proof1418Res2

end CFSG.RankThree.PartTwo.Sec14
