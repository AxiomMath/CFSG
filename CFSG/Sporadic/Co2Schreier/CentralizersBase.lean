
module

public import CFSG.Sporadic.Co2Schreier.ChainsBase
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
public import CFSG.Certificates.Kernel.Spor.ONKSound

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

def zP : co2P := ⟨locZ, locZ_mem⟩

def tP : co2P := ⟨locT, locT_mem⟩

theorem centralizer_mk_eq {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    Subgroup.centralizer {(⟨x, hx⟩ : H)} = (Subgroup.centralizer {x}).subgroupOf H := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem index_subgroupOf_P
    {H : Subgroup (Equiv.Perm (Fin 2300))} (hH : H ≤ co2P) {m k : ℕ}
    (hm : Nat.card H = m) (hk : 42305421312000 = k * m) (hm0 : 0 < m) :
    (H.subgroupOf co2P).index = k := by
  have h := (H.subgroupOf co2P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hm, card_co2P, hk] at h
  exact Nat.eq_of_mul_eq_mul_left hm0 (by rw [h, mul_comm])

theorem orbitRecordOK_spec {start : List ℕ} {bound : ℕ}
    {O : Array (List ℕ) × Array ℕ × Array ℕ} (h : orbitRecordOK start bound O = true) :
    translatesOK aArrs start O.1 O.2.1 O.2.2 = true ∧
      CFSG.Sporadic.Schreier.Co3.Native.keysSortedOK O.1 = true ∧ O.1.size = bound := by
  simp only [orbitRecordOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fixedSet_zP : {p : Fin 2300 | zP • p = p} = {p : Fin 2300 | locZ p = p} := rfl

theorem fixedSet_tP : {p : Fin 2300 | tP • p = p} = {p : Fin 2300 | locT p = p} := rfl

end CFSG.Sporadic.Co2Schreier
