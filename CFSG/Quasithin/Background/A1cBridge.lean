module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin

variable {G : Type*} [Group G]

theorem mem_pResidual_of_coprime {p : ℕ} {X : Type*} [Group X] {y : X}
    (hy : (orderOf y).Coprime p) : y ∈ pResidual p X := by
  refine Subgroup.mem_iInf.2 fun N => Subgroup.mem_iInf.2 fun hNn =>
    Subgroup.mem_iInf.2 fun hN => ?_
  obtain ⟨k, hk⟩ := hN y
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    ((Nat.Coprime.pow_right k hy).symm : (p ^ k).Coprime (orderOf y))
  rw [← hm]
  exact N.pow_mem hk m

theorem opResidual_le_pResidualOf {p : ℕ} (X : Subgroup G) : opResidual p X ≤ pResidualOf p X := by
  rw [opResidual, Subgroup.closure_le]
  rintro x ⟨hxX, hxc⟩
  exact ⟨⟨x, hxX⟩, mem_pResidual_of_coprime (by rwa [Subgroup.orderOf_mk]), rfl⟩

theorem pResidualOf_le_opResidual [Finite G] {p : ℕ} [Fact p.Prime] (X : Subgroup G) :
    pResidualOf p X ≤ opResidual p X := by
  have hN : ((opResidual p X).subgroupOf X).Normal := opResidual_normal p X
  rw [pResidualOf, Subgroup.map_le_iff_le_comap]
  refine pResidual_le (N := (opResidual p X).subgroupOf X) fun x => ?_
  obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := p) x.2
  exact ⟨k, hk⟩

theorem pResidualOf_eq_opResidual [Finite G] {p : ℕ} [Fact p.Prime] (X : Subgroup G) :
    pResidualOf p X = opResidual p X :=
  le_antisymm (pResidualOf_le_opResidual X) (opResidual_le_pResidualOf X)

end CFSG.Quasithin
