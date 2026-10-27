module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCrit
public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporComp

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique CFSG.Blueprint

theorem not_isComponent_of_isCharacteristicP {C : Type*} [Group C] [Finite C]
    (h : IsCharacteristicP 2 C) (B : Subgroup C) : ¬ CFSG.IsComponent B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hB
  have hle : B ≤ CFSG.layer C := le_sSup hB
  rw [CFSG.layer_eq_bot_of_isCharacteristicP C 2 h, le_bot_iff] at hle
  have : Subsingleton B := by
    rw [hle]
    infer_instance
  have : Group.IsSolvable B := inferInstance
  exact not_isQuasisimple_of_isSolvable hB.1

theorem cent2NoComp_j4 :
    Cent2NoComp NativeSporadic.J4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite NativeSporadic.J4 := CFSG.Sporadic.J4.fam_j4_simplicity.1
  intro D hD t htD ht2 hcomm B
  obtain ⟨-, hp, hidx'⟩ := hD
  have hidx : ¬ 2 ∣ D.index := by
    rwa [show (D.subgroupOf ⊤).index = D.index from Subgroup.relIndex_top_right D] at hidx'
  let S : Sylow 2 NativeSporadic.J4 := hp.toSylow hidx
  have hS : t ∈ (Subgroup.center (S : Subgroup NativeSporadic.J4)).map
      (S : Subgroup NativeSporadic.J4).subtype :=
    CFSG.Quasithin.H13.J4.mem_center_map_iff.2 ⟨htD, hcomm⟩
  obtain ⟨-, -, -, -, htype⟩ := CFSG.Quasithin.H13.J4.concreteJ4_typeJ4
  obtain ⟨-, -, hcore, -, -⟩ := htype t ht2 ⟨S, hS⟩
  have hchar : IsCharacteristicP 2 ↥(Subgroup.centralizer ({t} : Set NativeSporadic.J4)) :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).2 hcore.1.symm
  exact not_isComponent_of_isCharacteristicP hchar B

end CFSG.Quasithin.E6.Spor
