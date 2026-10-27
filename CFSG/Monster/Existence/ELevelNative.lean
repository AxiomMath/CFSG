module

public import CFSG.Monster.Existence.ELevelCheck
public meta import CFSG.Monster.Existence.ELevelBits
public meta import CFSG.Monster.Existence.ELevelConv
public meta import CFSG.Monster.Existence.ELevelCheck
public meta import CFSG.Monster.VisCert.Basis
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public meta import Certificates.Data.CFSGNative.MonsterB.Short
public meta import Certificates.Data.CFSGNative.MonsterVis.Frame
public import CFSG.Monster.Existence.ELevelNativeInputs
public import Certificates.Certificate6025
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import CFSG.Monster.B.TwoA.Base.Flags
public meta import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public meta import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public meta import CFSG.Monster.B.TwoA.Par3.Main
public meta import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public meta import CFSG.Monster.B.TwoA.Unitary.Semilinear
public meta import CFSG.Open.MonsterY443Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.Plane
public import Certificates.Certificate1020Base

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.B.TwoA.Census

theorem allOK_eq_true : allOK = true :=
  Certificates.certificate6025

theorem fullOK_of_mem {i : ℕ} (hi : i ∈ ({1, 2, 6} : Finset ℕ)) :
    rankOK i = true ∧ checkX shortPacked (tT i) (tD i) (packP (wP i)) = true := by
  have h := allOK_eq_true
  simp only [allOK, fullOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨h1.1, h1.2⟩
  · exact ⟨h2.1, h2.2⟩
  · exact ⟨h3.1, h3.2⟩

theorem rankSpec :
    RankSpec := rankSpec_of_check fun _ hi => (fullOK_of_mem hi).1

theorem checkSpec
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) : CheckSpec i :=
  checkSpec_of_checkX (fullOK_of_mem (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hi)).2

end CFSG.Monster.Existence
