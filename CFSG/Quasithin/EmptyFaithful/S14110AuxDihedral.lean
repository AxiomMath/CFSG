module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.S14110

open DihedralGroup

private def dihedralFourPermFun : DihedralGroup 4 → Equiv.Perm (ZMod 4)
  | r i => Equiv.subRight i
  | sr i => Equiv.subLeft i

private def dihedralFourToPerm : DihedralGroup 4 →* Equiv.Perm (ZMod 4) where
  toFun := dihedralFourPermFun
  map_one' := by
    rw [one_def]
    ext x
    simp [dihedralFourPermFun]
  map_mul' := by
    rintro (i | i) (j | j) <;> ext x <;>
      simp [dihedralFourPermFun, r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;> ring

private theorem dihedralFourToPerm_injective : Function.Injective dihedralFourToPerm := by
  intro a b h
  revert a b
  decide

private theorem card_range_dihedralFourToPerm : Nat.card dihedralFourToPerm.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective dihedralFourToPerm_injective).toEquiv,
    DihedralGroup.nat_card]

private theorem card_perm_zmod_four : Nat.card (Equiv.Perm (ZMod 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card]
  rfl

private theorem isPGroup_range_dihedralFourToPerm : IsPGroup 2 dihedralFourToPerm.range :=
  IsPGroup.of_card (n := 3) (by rw [card_range_dihedralFourToPerm]; norm_num)

private theorem index_range_dihedralFourToPerm : dihedralFourToPerm.range.index = 3 := by
  have h := dihedralFourToPerm.range.card_mul_index
  rw [card_range_dihedralFourToPerm, card_perm_zmod_four] at h
  omega

theorem nonempty_mulEquiv_dihedralFour_of_sylow {G : Type*} [Group G] [Finite G] {H T : Subgroup G}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf H).index)
    (e : H ≃* Equiv.Perm (Fin 4)) : Nonempty (T ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : H ≃* Equiv.Perm (ZMod 4) := e
  let eT : T ≃* ((T.subgroupOf H).map (e' : H →* Equiv.Perm (ZMod 4))) :=
    (Subgroup.subgroupOfEquivOfLe hTH).symm.trans (e'.subgroupMap _)
  have hp : IsPGroup 2 ((T.subgroupOf H).map (e' : H →* Equiv.Perm (ZMod 4))) := hT2.of_equiv eT
  have hidx : ¬ 2 ∣ ((T.subgroupOf H).map (e' : H →* Equiv.Perm (ZMod 4))).index := by
    rwa [Subgroup.index_map_equiv]
  let Q : Sylow 2 (Equiv.Perm (ZMod 4)) := hp.toSylow hidx
  let P : Sylow 2 (Equiv.Perm (ZMod 4)) :=
    isPGroup_range_dihedralFourToPerm.toSylow (by
      rw [index_range_dihedralFourToPerm]
      decide)
  exact ⟨eT.trans ((Sylow.equiv Q P).trans
    (MonoidHom.ofInjective dihedralFourToPerm_injective).symm)⟩

end CFSG.Quasithin.S14110
