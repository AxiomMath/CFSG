
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtBase

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public import CFSG.Monster.B.Fischer.Fi22Graph
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Monster.B.Fischer.Fi22Outer

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem rep_fi22ExtPerm
    {L : ℕ} (hL : L < 185) : Rep 3510 (fi22ExtArr L) (fi22ExtPerm L) :=
  (rep_permOfArr (fi22Ext_check.2.2.1 L hL)).1

theorem rep_fi22ExtPerm256
    {L : ℕ} (hL : L < 18) : Rep 256 (fi22ExtArr256 L) (fi22ExtPerm256 L) :=
  (rep_permOfArr (fi22Ext_check.2.2.2.1 L hL)).1

theorem rep_fi22ExtRep
    {k : ℕ} (hk : k < 6) : Rep 3510 (fi22ExtArr (21 + k)) (fi22ExtRep k) :=
  rep_fi22ExtPerm (by omega)

theorem fi22ExtSmallPointsNat_length :
    fi22ExtSmallPointsNat.length = 256 :=
  fi22Ext_check.2.2.2.2.2.2.1

theorem fi22ExtSmallPointsNat_getD (i : Fin 256) :
    fi22ExtSmallPointsNat.getD i 0 =
      fi22ExtSmallPointsNat[(i : ℕ)]'(by rw [fi22ExtSmallPointsNat_length]; exact i.2) :=
  List.getD_eq_getElem _ _ _

theorem fi22ExtSmallPointsNat_getD_lt
    (i : Fin 256) : fi22ExtSmallPointsNat.getD i 0 < 3510 := by
  rw [fi22ExtSmallPointsNat_getD]
  exact fi22Ext_check.2.2.2.2.1 _ (List.getElem_mem _)

theorem fi22ExtDeltaPt_val (i : Fin 256) :
    (fi22ExtDeltaPt i : ℕ) = fi22ExtSmallPointsNat.getD i 0 :=
  Nat.mod_eq_of_lt (fi22ExtSmallPointsNat_getD_lt i)

theorem fi22ExtDeltaPt_injective :
    Function.Injective fi22ExtDeltaPt := by
  intro i j h
  have h' := congrArg Fin.val h
  rw [fi22ExtDeltaPt_val, fi22ExtDeltaPt_val, fi22ExtSmallPointsNat_getD,
    fi22ExtSmallPointsNat_getD] at h'
  exact Fin.ext ((fi22Ext_check.2.2.2.2.2.1.getElem_inj_iff).1 h')

theorem CTUC_Fi22_extension_involution_data :
    (∀ L < 185, Rep 3510 (fi22ExtArr L) (fi22ExtPerm L)) ∧
    (∀ L < 18, Rep 256 (fi22ExtArr256 L) (fi22ExtPerm256 L)) ∧
    fi22ExtT0 = fi22OuterT.map (MulAut.conj fi22ExtQ).toMonoidHom ∧
    fi22ExtS = Subgroup.closure (insert fi22ExtV (fi22ExtT0 : Set (Equiv.Perm (Fin 3510)))) ∧
    fi22ExtDelta.length = 256 ∧ fi22ExtDelta.Nodup ∧
    fi22ExtSmallChain.originalCount = 10 ∧ fi22ExtSmallChain.strongCount = 18 ∧
    fi22ExtSmallChain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 6] ∧
    wordsOK fi22ExtSmallGenCount 18 fi22ExtSmallDerivations = true ∧
    fi22ExtInvolutionCount = 6143 ∧ fi22ExtFixedCounts = [54, 182, 694, 72, 360, 64] ∧
    fi22ExtClassSizes.length = 79 ∧ fi22ExtGlobalClasses.length = 79 ∧
    (∀ j < 79, fi22ExtGlobalClass j < 6) := by
  obtain ⟨-, -, -, -, -, -, -, hgc, hgl, hcl, hw⟩ := fi22Ext_check
  refine ⟨fun L hL => rep_fi22ExtPerm hL, fun L hL => rep_fi22ExtPerm256 hL, rfl, rfl,
    List.length_ofFn, List.nodup_ofFn.2 fi22ExtDeltaPt_injective, rfl, ?_, rfl, hw, rfl, rfl,
    hcl, hgl, fun j hj => ?_⟩
  · rw [fi22ExtSmallChain, RawSchreierDatum.ofArrays_strongCount, fi22ExtSmallStrong,
      Array.size_ofFn]
  · rw [fi22ExtGlobalClass, List.getD_eq_getElem _ _ (by rw [hgl]; exact hj)]
    exact hgc _ (List.getElem_mem _)

end CFSG.Sporadic.FischerOddCore
