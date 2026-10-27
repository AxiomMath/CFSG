
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtBase
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
public import CFSG.Sporadic.FischerOddCore.EmbAction
public import CFSG.Monster.B.Fischer.Fi22ModelBase
public import CFSG.Monster.B.Fischer.Fi22CoverBase
public import Mathlib.GroupTheory.Sylow
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.Monster.B.Fischer.Fi22CentralizerCheckBase
public import CFSG.Monster.B.Fischer.Fi22GraphAutBase
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckBase
public import CFSG.Monster.B.Fischer.Fi22LocalBase
public import CFSG.Monster.B.Fischer.Fi22ModelCheckBase
public import CFSG.Sporadic.FischerOddCore.RefineSpec
public import CFSG.Sporadic.Th.F2Spec

@[expose] public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer

theorem fi22InP_iff
    {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hG : Rep 3510 g G) :
    fi22InP g = true ↔ G ∈ fi22P :=
  siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1 hG

@[expose] def fi22TSeed (k : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22OuterStrong3510 4)[k]!

theorem fi22OuterT_eq_closure :
    fi22OuterT = Subgroup.closure {g | ∃ k < 9, fi22TSeed k = g} := by
  rw [fi22OuterT, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, fi22OuterChainT, RawSchreierDatum.mem_ofArrays_original]
  rfl

theorem conj_apply_eq (x g : Equiv.Perm (Fin 3510)) :
    (MulAut.conj x).toMonoidHom g = x * g * x⁻¹ :=
  rfl

theorem fi22ExtT0_le_S : fi22ExtT0 ≤ fi22ExtS := fun _ ht =>
  Subgroup.subset_closure (Set.mem_insert_of_mem _ ht)

theorem fi22ExtV_mem_S : fi22ExtV ∈ fi22ExtS := Subgroup.subset_closure (Set.mem_insert _ _)

theorem closure_insert_closure {G : Type*} [Group G] (a : G) (A : Set G) :
    Subgroup.closure (insert a (Subgroup.closure A : Set G)) = Subgroup.closure (insert a A) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.closure_mono (Set.subset_insert _ _) hg
  · exact Subgroup.closure_mono (Set.insert_subset_insert Subgroup.subset_closure)

theorem fi22ExtSmallStrong_get {k : ℕ} (hk : k < 18) :
    fi22ExtSmallStrong[k]! = fi22ExtArr256 k := by
  rw [fi22ExtSmallStrong, getElem!_pos _ k (by simp [hk]), Array.getElem_ofFn]

theorem mem_fi22ExtSmallChain_original {g : Equiv.Perm (Fin 256)} :
    g ∈ fi22ExtSmallChain.original.toList ↔ ∃ k < 10, fi22ExtPerm256 k = g := by
  rw [fi22ExtSmallChain, RawSchreierDatum.mem_ofArrays_original]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < 10 := hk
    exact ⟨k, hk', by rw [fi22ExtPerm256, fi22ExtSmallStrong_get (by omega)]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [fi22ExtPerm256, fi22ExtSmallStrong_get (by omega)]⟩

end CFSG.Sporadic.FischerOddCore
