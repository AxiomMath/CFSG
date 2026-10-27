module

public import CFSG.Monster.B.Rep4371.PacketCert
public import CFSG.Monster.B.Rep4371.GlueDefs

public section

namespace CFSG.Monster.B.Rep4371

@[expose] def genActM (i : Nat) : Model.Key → List (Model.Key × Int) :=
  if i < 23 then Model.keyActPauli (Model.qPauli i)
  else if i < 35 then Model.keyActPerm Model.recPerms[i - 23]!
  else if i < 46 then Model.keyActSign Native.signCodes[i - 35]!
  else Model.keyActXi

theorem native_genAct : Native.genAct = genActM := by
  delta Native.genAct genActM
  rw [native_keyActPauli, native_qPauli, native_keyActPerm, native_recPerms, native_keyActSign,
    native_keyActXi]

theorem genCheck_all
    {i : Nat} (hi : i < 47) : Native.genCheck i = true := by
  rcases Nat.lt_or_ge i 23 with h1 | h1
  · exact List.all_eq_true.1 genCheck_pauli i (List.mem_range.2 h1)
  rcases Nat.lt_or_ge i 35 with h2 | h2
  · have := List.all_eq_true.1 genCheck_perm (i - 23) (List.mem_range.2 (by omega))
    rwa [show 23 + (i - 23) = i by omega] at this
  rcases Nat.lt_or_ge i 46 with h3 | h3
  · have := List.all_eq_true.1 genCheck_sign (i - 35) (List.mem_range.2 (by omega))
    rwa [show 35 + (i - 35) = i by omega] at this
  · rw [show i = 46 by omega]
    exact genCheck_xi

theorem genOK_packet {i : Nat} (hi : i < 47) :
    Model.genOK (genActM i) CFSG.Monster.B.Native.packetRows[i]! = true := by
  have h := genCheck_all hi
  rw [Native.genCheck, native_genOK, native_genAct] at h
  exact h

theorem rowOK_packet {i k : Nat} (hi : i < 47) (hk : k < 4371) :
    Model.rowOK (genActM i) CFSG.Monster.B.Native.packetRows[i]![k]! k = true :=
  List.all_eq_true.1 (genOK_packet hi) k (List.mem_range.2 hk)

theorem packetRows_tau {k : Nat} (hk : k < 4371) :
    CFSG.Monster.B.Native.packetRows[47]![k]! = Model.tauRow k := by
  have h := List.all_eq_true.1 tauCheck_eq_true k (List.mem_range.2 hk)
  rw [beq_iff_eq, native_tauRow] at h
  exact h

theorem octDataOK_true : Model.octDataOK = true := by
  rw [← native_octDataOK]
  exact octCheck_eq_true.1

theorem octSignOK_true : Model.octSignOK = true := by
  rw [← native_octSignOK]
  exact octCheck_eq_true.2

theorem labelsCheck_model :
    Native.labelsCheck = true := labelsCheck_eq_true.1

theorem spinIndexCheck_model :
    Native.spinIndexCheck = true := labelsCheck_eq_true.2

end CFSG.Monster.B.Rep4371
