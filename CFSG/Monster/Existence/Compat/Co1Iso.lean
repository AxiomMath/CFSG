module

public import CFSG.Monster.Existence.Compat.Co0Iso
public import CFSG.Monster.Existence.TwoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Compat

open CFSG.Monster CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Open

theorem negOneO_mem_center : negOneO ∈ Subgroup.center latticeO := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mat_injective
  rw [mat_mul, mat_mul, mat_negOneO, mul_neg, mul_one, neg_mul, one_mul]

theorem center_latticeO :
    Subgroup.center latticeO = Subgroup.zpowers negOneO := by
  refine le_antisymm ?_ (Subgroup.zpowers_le.2 negOneO_mem_center)
  have : IsSimpleGroup OLq := isSimpleGroup_OLq
  have : Finite OLq := Nat.finite_of_card_ne_zero (by rw [natCard_OLq]; norm_num)
  let f : latticeO →* OLq := QuotientGroup.mk' (Subgroup.zpowers negOneO)
  have hn : ((Subgroup.center latticeO).map f).Normal :=
    Subgroup.Normal.map (inferInstance : (Subgroup.center latticeO).Normal) f
      (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · exfalso
    have hcomm : ∀ x y : OLq, x * y = y * x := by
      intro x y
      obtain ⟨a, ha, rfl⟩ : x ∈ (Subgroup.center latticeO).map f := htop ▸ Subgroup.mem_top x
      obtain ⟨b, hb, rfl⟩ : y ∈ (Subgroup.center latticeO).map f := htop ▸ Subgroup.mem_top y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ha b]
    let : CommGroup OLq := { (inferInstance : Group OLq) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := OLq)
    rw [natCard_OLq] at hp
    have := hp.eq_one_or_self_of_dvd 2 (by norm_num)
    omega

theorem center_monsterCo0 :
    Subgroup.center monsterCo0 = Subgroup.zpowers negCo0 := by
  rw [← center_map_mulEquiv co0Equiv, center_latticeO, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers co0Equiv_negOneO

@[expose] noncomputable def monsterCo1EquivOLq :
    OLq ≃* MonsterCo1 :=
  QuotientGroup.congr (Subgroup.zpowers negOneO) (Subgroup.center monsterCo0) co0Equiv (by
    rw [← center_map_mulEquiv co0Equiv, center_latticeO]
    rfl)

@[expose] noncomputable def co1EquivMonsterCo1 :
    Blueprint.NativeSporadic.Co1 ≃* MonsterCo1 :=
  Co1Bridge.co1EquivHvis.trans (OLqEquivHvis.symm.trans monsterCo1EquivOLq)

end CFSG.Monster.Existence.Compat
