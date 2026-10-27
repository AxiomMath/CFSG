module

public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365Normal
public import CFSG.Monster.GMS.S365Leech
public import CFSG.Monster.GMS.Facts.Section37
public import CFSG.Monster.GMS.Leech.Pairs
import CFSG.Assembly.Defs
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem card_eightCent_one
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x y t : G}
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) (hc : twoBCount z₀ x y t = 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)) = eightCentOrder 1 := by
  obtain ⟨w, hw, hwc, hxw, hyw, hxQ, hyQ⟩ := exists_pivot_one I hG hl he hc
  rw [centralizer_inf_inf_eq_of_mem_cosetSet hwc]
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hw
  have hx0 := mem_typeSet_zero_of_isConj I hG hw L hxQ hl.1
  have hy0 := mem_typeSet_zero_of_isConj I hG hw L hyQ hl.2.1
  have hxy0 : L.vec x + L.vec y ∈ co1Orbit 0 := by
    have := mem_typeSet_zero_of_isConj I hG hw L ((leechQ w).mul_mem hxQ hyQ) hl.2.2
    rw [L.mem_typeSet, L.vec_mul x hxQ y hyQ] at this
    exact this.2
  have hind : LinearIndependent (ZMod 2) ![L.vec x, L.vec y] :=
    Leech.linearIndependent_pair_of_add_mem (Leech.ne_zero_of_mem_co1Orbit hx0.2)
      (Leech.ne_zero_of_mem_co1Orbit hy0.2) hxy0
  have h2 := L.card_inf_centralizer_two hxQ hyQ hind
  have hre : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G) =
      Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [hre, h2, card_inf_stab_pair hx0.2 hy0.2 hxy0]
  norm_num [eightCentOrder]

end S365

end CFSG.Monster.GMS
