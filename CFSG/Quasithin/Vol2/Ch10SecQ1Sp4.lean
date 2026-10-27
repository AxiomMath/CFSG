module

public import CFSG.Quasithin.Vol2.Ch10SecQ1Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open C10P01 CFSG.Assembly.LowTwoRank

theorem factSp4TwoNormal_holds : FactSp4TwoNormal := by
  intro K _ _ hK N _ hNq
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let e := CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK'
  have hmap : (commutator ↥(StatedSp 2 K)).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq (by simp)]
  let eA : ↥(commutator ↥(StatedSp 2 K)) ≃* ↥(alternatingGroup (Fin 6)) :=
    ((commutator ↥(StatedSp 2 K)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hA6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥(commutator ↥(StatedSp 2 K)) := eA.isSimpleGroup
  have : Group.IsPerfect ↥N := hNq.1
  rw [eq_commutator_of_isPerfect N (ne_bot_of_isQuasisimple hNq) hs, Nat.card_congr eA.toEquiv,
    card_alt 6 (by norm_num)]
  rfl

theorem factB4aSp4Twisted_holds :
    FactB4aSp4Twisted := by
  intro K _ _ a ha hK X _ hX π
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hbij : Function.Bijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hsimple' : IsSimpleGroup ↥(StatedSp 2 K) := (MulEquiv.ofBijective _ hbij).isSimpleGroup
  exact not_surjective_of_isSimpleGroup hsimple'
    (by rw [card_Sp4_pow hK]; exact not_shapeCard_Sp4 (by omega)) hX π

end CFSG.Quasithin.Vol2.Ch10.SecA
