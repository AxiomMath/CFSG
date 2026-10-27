module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosG2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG23

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_elemAbelian_transport {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    {E : Subgroup Y} (hE : CFSG.Assembly.IsElemAbelian 3 E) (h81 : 81 ≤ Nat.card E) :
    ∃ E' : Subgroup X, IsMulCommutative E' ∧ (∀ x ∈ E', x ^ 3 = 1) ∧ 81 ≤ Nat.card E' := by
  obtain ⟨hcomm, hpow⟩ := hE
  have hg : Function.Injective f.symm.toMonoidHom := f.symm.injective
  refine ⟨E.map f.symm.toMonoidHom, ⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_, ?_⟩
  · show x * y = y * x
    apply Subtype.ext
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    have hab : a * b = b * a :=
      congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
    show (x : X) * (y : X) = (y : X) * (x : X)
    rw [← hax, ← hby, ← map_mul, ← map_mul, hab]
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hpow a ha, map_one]
  · rw [Subgroup.card_map_of_injective hg]
    exact h81

theorem exists_elemAbelian81_G23 {X : Type} [Group X]
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 3 1) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ 81 ≤ Nat.card E := by
  obtain ⟨f⟩ := CFSG.CGT.PushingUpLit.SolKNA.exists_equiv_H3 hX
  obtain ⟨D, hD, hD27⟩ := CFSG.RankThree.PartTwo.Sec4.Item434RemG23.exists_E27_R3
  obtain ⟨_, E, _, _, hE, hE81, _⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434RemG23.hE_R3 D hD hD27
  exact exists_elemAbelian_transport (Y := ↥(CFSG.RankThree.PartTwo.Census.Carrier.G2Three.R3))
    f hE hE81

end CFSG.RankThree.PartTwo.Sec11
