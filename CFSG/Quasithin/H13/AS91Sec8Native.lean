module

public import CFSG.Quasithin.H13.AS91Sec4Defs
public import CFSG.Quasithin.H13.J4TypeFinal

public section

namespace CFSG.Quasithin.H13.AS91

instance instFiniteNativeJ4 :
    Finite CFSG.Blueprint.NativeSporadic.J4 :=
  CFSG.Sporadic.J4.fam_j4_simplicity.1

theorem hypJ4_native_of_center
    (z : CFSG.Blueprint.NativeSporadic.J4) (hz : orderOf z = 2)
    (hS : ∃ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4,
      z ∈ (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
        (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype) :
    HypJ4 CFSG.Blueprint.NativeSporadic.J4 z := by
  have hcon := CFSG.Quasithin.H13.J4.concreteJ4_typeJ4
  obtain ⟨hsimp, hnonab, -, -, hcent⟩ := hcon
  obtain ⟨-, -, hcore, haut, g, hg1, hg2⟩ := hcent z hz hS
  exact ⟨hsimp, hnonab, hz, hcore, haut, ⟨g, hg1, hg2⟩⟩

theorem exists_hypJ4_native
    :
    ∃ z : CFSG.Blueprint.NativeSporadic.J4, HypJ4 CFSG.Blueprint.NativeSporadic.J4 z := by
  have hcon := CFSG.Quasithin.H13.J4.concreteJ4_typeJ4
  obtain ⟨S⟩ : Nonempty (Sylow 2 CFSG.Blueprint.NativeSporadic.J4) := inferInstance
  have hZ : Nat.card (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)) = 2 :=
    hcon.2.2.1 S
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (dvd_of_eq hZ.symm)
  have hz : orderOf ((x : (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)) :
      CFSG.Blueprint.NativeSporadic.J4) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  have hmem : ((x : (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)) :
      CFSG.Blueprint.NativeSporadic.J4) ∈
      (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
        (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype :=
    Subgroup.mem_map.2 ⟨(x : (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)), x.2, rfl⟩
  exact ⟨_, hypJ4_native_of_center _ hz ⟨S, hmem⟩⟩

end CFSG.Quasithin.H13.AS91
