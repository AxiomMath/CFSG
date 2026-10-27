module

public import CFSG.Monster.GMS.U6OddSylow
public import CFSG.Sporadic.Co1.Module.U6OddProg
public import CFSG.Sporadic.Co1.Module.U6OddForest
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Sporadic.Co1.Module.U6OddLitFacts
public import Certificates.Certificate10078
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.U6OddProg
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.U6OddCheck
public meta import Certificates.Data.CFSGNative.Co1.U6OddData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative Matrix
open CFSG.Sporadic.Co1.U6OddNative CFSG.Perm.Native
open CFSG.Sporadic.Co1.Module (co1Act v₂ toVecD_v₂)
open CFSG.Sporadic.Co1.Module.CoTwo

theorem lit_ok : ∃ W : U6W, U6OK W :=
  Certificates.certificate10078

@[expose] def U0 : Subgroup NativeSporadic.Co1 :=
  vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)

@[expose] def normU (g : NativeSporadic.Co1) : Subgroup NativeSporadic.Co1 :=
  Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) :
    Set NativeSporadic.Co1) ⊓ U0

theorem y₀_mem_cls :
    toVecD 24 u2 ∈ Pairs.cls 3 :=
  y₀_mem_cls_lit lit_ok

theorem card_U0 :
    Nat.card U0 = 9196830720 :=
  card_U0_lit lit_ok

theorem conj_fix {h m : NativeSporadic.Co1} {a b : Fin 24 → ZMod 2} (hh : co1Act h a = b)
    (hm : co1Act m a = a) : co1Act (h * m * h⁻¹) b = b := by
  rw [← hh]
  calc co1Act (h * m * h⁻¹) (co1Act h a) = co1Act (h * m * h⁻¹ * h) a :=
        (Odd.co1Act_mul' _ _ _).symm
    _ = co1Act (h * m) a := by rw [show h * m * h⁻¹ * h = h * m by group]
    _ = co1Act h (co1Act m a) := Odd.co1Act_mul' _ _ _
    _ = co1Act h a := by rw [hm]

theorem norm_ex_five :
    ∃ g ∈ U0, orderOf g = 5 ∧ Nat.card (normU g) ∣ 120 :=
  norm_ex_five_lit lit_ok

theorem norm_ex_seven :
    ∃ g ∈ U0, orderOf g = 7 ∧ Nat.card (normU g) ∣ 42 :=
  norm_ex_seven_lit lit_ok

theorem norm_ex_eleven :
    ∃ g ∈ U0, orderOf g = 11 ∧ Nat.card (normU g) ∣ 55 :=
  norm_ex_eleven_lit lit_ok

theorem s0_exists :
    ∃ S : Subgroup NativeSporadic.Co1, Nat.card S = 729 ∧ S ≤ U0 ∧
    ∀ A : Subgroup NativeSporadic.Co1, A ≤ S → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      Nat.card A < 243 :=
  s0_exists_lit lit_ok

end CFSG.Sporadic.Co1.Module.U6Odd
