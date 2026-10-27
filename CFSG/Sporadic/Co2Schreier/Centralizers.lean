
module

public import CFSG.Sporadic.Co2Schreier.CentralizersBase

public import CFSG.Sporadic.Co2Schreier.Chains
public import CFSG.Sporadic.Co2Schreier.OrbitZCheck
public import CFSG.Sporadic.Co2Schreier.OrbitTCheck
public import CFSG.Sporadic.Schreier.Co3Centralizers
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRealization
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem locC_index :
    (locC.subgroupOf co2P).index = 56925 :=
  index_subgroupOf_P locC_le_P card_locC (by norm_num) (by norm_num)

theorem locD_index :
    (locD.subgroupOf co2P).index = 1024650 :=
  index_subgroupOf_P locD_le_P card_locD (by norm_num) (by norm_num)

theorem aArrs_size : aArrs.size = 2 := wordFacts.sizeA

theorem rep_aArrs_gen :
    ∀ k < aArrs.size, Rep 2300 aArrs[k]! (co2Gen k) := by
  intro k hk
  rw [aArrs_size] at hk
  exact rep_co2Gen hk

theorem co2Gen_mem_P : ∀ k < aArrs.size, co2Gen k ∈ co2P := by
  intro k hk
  rw [aArrs_size] at hk
  interval_cases k
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem le_ncard_orbit_of_record
    {g : Equiv.Perm (Fin 2300)} {t : Array ℕ} (ht : Rep 2300 t g)
    {bound : ℕ} {O : Array (List ℕ) × Array ℕ × Array ℕ}
    (h : orbitRecordOK (fixedList 2300 t) bound O = true) :
    bound ≤ (Set.range fun x : co2P => x • {p : Fin 2300 | g p = p}).ncard := by
  obtain ⟨h1, h2, h3⟩ := orbitRecordOK_spec h
  have key := le_ncard_orbit_of_translatesOK (H := co2P) rep_aArrs_gen co2Gen_mem_P
    (pointList_fixedList t) h1 (CFSG.Sporadic.Schreier.Co3.keysSortedOK_nodup h2)
  rw [h3, finSet_fixedList ht] at key
  exact key

theorem iz_orbit :
    56925 ≤ (Set.range fun x : co2P => x • {p : Fin 2300 | locZ p = p}).ncard :=
  le_ncard_orbit_of_record rep_z orbitZ_check

theorem it_orbit :
    1024650 ≤ (Set.range fun x : co2P => x • {p : Fin 2300 | locT p = p}).ncard :=
  le_ncard_orbit_of_record rep_t orbitT_check

theorem locC_subgroupOf_eq :
    locC.subgroupOf co2P = Subgroup.centralizer {zP} := by
  have hH : locC.subgroupOf co2P ≤ Subgroup.centralizer {zP} := by
    intro g hg
    rw [zP, centralizer_mk_eq, Subgroup.mem_subgroupOf]
    exact locC_le_centralizer (Subgroup.mem_subgroupOf.1 hg)
  have horb : (locC.subgroupOf co2P).index ≤
      (Set.range fun g : co2P => g • {p : Fin 2300 | zP • p = p}).ncard := by
    rw [locC_index, fixedSet_zP]
    exact iz_orbit
  exact (fixed_point_set_orbit_centralizer_bound zP _ hH horb).1

theorem locD_subgroupOf_eq :
    locD.subgroupOf co2P = Subgroup.centralizer {tP} := by
  have hH : locD.subgroupOf co2P ≤ Subgroup.centralizer {tP} := by
    intro g hg
    rw [tP, centralizer_mk_eq, Subgroup.mem_subgroupOf]
    exact locD_le_centralizer (Subgroup.mem_subgroupOf.1 hg)
  have horb : (locD.subgroupOf co2P).index ≤
      (Set.range fun g : co2P => g • {p : Fin 2300 | tP • p = p}).ncard := by
    rw [locD_index, fixedSet_tP]
    exact it_orbit
  exact (fixed_point_set_orbit_centralizer_bound tP _ hH horb).1

theorem locC_eq_centralizer :
    locC = co2P ⊓ Subgroup.centralizer {locZ} := by
  have h := locC_subgroupOf_eq
  rw [zP, centralizer_mk_eq, Subgroup.subgroupOf_inj] at h
  rw [inf_comm, ← h]
  exact (inf_eq_left.2 locC_le_P).symm

theorem locD_eq_centralizer :
    locD = co2P ⊓ Subgroup.centralizer {locT} := by
  have h := locD_subgroupOf_eq
  rw [tP, centralizer_mk_eq, Subgroup.subgroupOf_inj] at h
  rw [inf_comm, ← h]
  exact (inf_eq_left.2 locD_le_P).symm

theorem AT_Co2_full_involution_centralizers :
    locC = co2P ⊓ Subgroup.centralizer {locZ} ∧ locD = co2P ⊓ Subgroup.centralizer {locT} ∧
    (locC.subgroupOf co2P).index = 56925 ∧ (locD.subgroupOf co2P).index = 1024650 :=
  ⟨locC_eq_centralizer, locD_eq_centralizer, locC_index, locD_index⟩

end CFSG.Sporadic.Co2Schreier
