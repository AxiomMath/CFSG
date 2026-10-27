module

public import CFSG.Quasithin.H13.KG14726L115
public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Quasithin.H13.KG14726Lie

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Blueprint

theorem kg14726SporadicInput_J4 :
    KG14726SporadicInput .J4 := by
  show TwoCentralConstrained NativeSporadic.J4
  have : Finite NativeSporadic.J4 := CFSG.Sporadic.J4.fam_j4_simplicity.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T t hT hTi htT htc ht
  set S : Sylow 2 NativeSporadic.J4 := hT.toSylow hTi with hSdef
  have hST : (S : Subgroup NativeSporadic.J4) = T := rfl
  have htS : t ∈ (center (S : Subgroup NativeSporadic.J4)).map
      (S : Subgroup NativeSporadic.J4).subtype := by
    rw [hST]
    exact ⟨⟨t, htT⟩, mem_center_iff.mpr fun g => Subtype.ext (htc g g.2), rfl⟩
  obtain ⟨-, -, ⟨hcore, -⟩, -⟩ := (J4.concreteJ4_typeJ4).2.2.2.2 t ht ⟨S, htS⟩
  exact ConstrainedAt.of_isCharacteristicP
    ((CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mpr hcore.symm)

end CFSG.Quasithin.H13.KG14726

end
