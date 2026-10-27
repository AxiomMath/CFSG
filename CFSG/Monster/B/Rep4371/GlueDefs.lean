module

public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import CFSG.Monster.B.Rep4371.Model

public section

namespace CFSG.Monster.B.Rep4371

theorem native_popcN : @Native.popcN = @Model.popcN := by
  funext k a
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [Native.popcN, Model.popcN, ih]

theorem native_parN : @Native.parN = @Model.parN := by
  delta Native.parN Model.parN
  rw [native_popcN]
  all_goals rfl

theorem native_xorSum : @Native.xorSum = @Model.xorSum := by
  funext f n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Native.xorSum, Model.xorSum, ih]

theorem native_packN : @Native.packN = @Model.packN := by
  funext f n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Native.packN, Model.packN, ih]

theorem native_combN : @Native.combN = @Model.combN := by
  funext m n a
  induction n with
  | zero => rfl
  | succ n ih => simp only [Native.combN, Model.combN, ih]

theorem native_bmaskN : @Native.bmaskN = @Model.bmaskN := rfl

theorem native_umaskN : @Native.umaskN = @Model.umaskN := rfl

theorem native_wordN : @Native.wordN = @Model.wordN := by
  delta Native.wordN Model.wordN
  rw [native_combN, native_bmaskN]
  all_goals rfl

theorem native_repN : @Native.repN = @Model.repN := by
  delta Native.repN Model.repN
  rw [native_combN, native_umaskN]
  all_goals rfl

theorem native_coeffN : @Native.coeffN = @Model.coeffN := by
  delta Native.coeffN Model.coeffN
  rw [native_packN, native_parN, native_umaskN]
  all_goals rfl

theorem native_dualN : @Native.dualN = @Model.dualN := by
  delta Native.dualN Model.dualN
  rw [native_packN, native_parN, native_bmaskN]
  all_goals rfl

theorem native_pairN : @Native.pairN = @Model.pairN := by
  delta Native.pairN Model.pairN
  rw [native_parN]
  all_goals rfl

theorem native_mu0N : @Native.mu0N = @Model.mu0N := rfl

theorem native_pi0N : @Native.pi0N = @Model.pi0N := rfl

theorem native_shiftN : @Native.shiftN = @Model.shiftN := by
  delta Native.shiftN Model.shiftN
  rw [native_pi0N]
  all_goals rfl

theorem native_pN : @Native.pN = @Model.pN := by
  delta Native.pN Model.pN
  rw [native_popcN, native_wordN]
  all_goals rfl

theorem native_kN : @Native.kN = @Model.kN := by
  delta Native.kN Model.kN
  rw [native_popcN, native_wordN]
  all_goals rfl

theorem native_acodeN : @Native.acodeN = @Model.acodeN := by
  delta Native.acodeN Model.acodeN
  rw [native_dualN, native_wordN]
  all_goals rfl

theorem native_betaN : @Native.betaN = @Model.betaN := by
  delta Native.betaN Model.betaN
  rw [native_popcN, native_bmaskN]
  all_goals rfl

theorem native_thetaRec : @Native.thetaRec = @Model.thetaRec := by
  funext n a
  induction n with
  | zero => rfl
  | succ n ih => simp only [Native.thetaRec, Model.thetaRec, ih, native_packN, native_betaN, native_dualN, native_combN, native_bmaskN]

theorem native_thetaN : @Native.thetaN = @Model.thetaN := by
  delta Native.thetaN Model.thetaN
  rw [native_thetaRec]
  all_goals rfl

theorem native_thetaBit : @Native.thetaBit = @Model.thetaBit := by
  delta Native.thetaBit Model.thetaBit
  rw [native_pairN, native_thetaN]
  all_goals rfl

theorem native_Pauli : Native.Pauli = Model.Pauli := rfl

theorem native_Pauli_s : @Native.Pauli.s = @Model.Pauli.s := rfl

theorem native_Pauli_a : @Native.Pauli.a = @Model.Pauli.a := rfl

theorem native_Pauli_d : @Native.Pauli.d = @Model.Pauli.d := rfl

theorem native_Pauli_mul : @Native.Pauli.mul = @Model.Pauli.mul := by
  delta Native.Pauli.mul Model.Pauli.mul
  rw [native_Pauli_s, native_pairN, native_Pauli_a, native_Pauli_d]
  all_goals rfl

theorem native_permWordN : @Native.permWordN = @Model.permWordN := by
  delta Native.permWordN Model.permWordN
  rw [native_combN]
  all_goals rfl

theorem native_permCN : @Native.permCN = @Model.permCN := by
  delta Native.permCN Model.permCN
  rw [native_coeffN, native_permWordN, native_wordN]
  all_goals rfl

theorem native_permDN : @Native.permDN = @Model.permDN := by
  delta Native.permDN Model.permDN
  rw [native_dualN, native_permWordN, native_repN]
  all_goals rfl

theorem native_betaPN : @Native.betaPN = @Model.betaPN := by
  delta Native.betaPN Model.betaPN
  rw [native_thetaBit, native_permCN, native_betaN]
  all_goals rfl

theorem native_kappaN : @Native.kappaN = @Model.kappaN := by
  delta Native.kappaN Model.kappaN
  rw [native_xorSum, native_betaPN]
  all_goals rfl

theorem native_qGN : @Native.qGN = @Model.qGN := by
  delta Native.qGN Model.qGN
  rw [native_popcN]
  all_goals rfl

theorem native_bGN : @Native.bGN = @Model.bGN := by
  delta Native.bGN Model.bGN
  rw [native_parN]
  all_goals rfl

theorem native_gammaLowN : @Native.gammaLowN = @Model.gammaLowN := by
  delta Native.gammaLowN Model.gammaLowN
  rw [native_parN]
  all_goals rfl

theorem native_sumRange : @Native.sumRange = @Model.sumRange := by
  funext f n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Native.sumRange, Model.sumRange, ih]

theorem native_sgnI : @Native.sgnI = @Model.sgnI := rfl

theorem native_conjPauliN : @Native.conjPauliN = @Model.conjPauliN := by
  delta Native.conjPauliN Model.conjPauliN
  rw [native_Pauli_s, native_pairN, native_Pauli_a, native_Pauli_d]
  all_goals rfl

theorem native_conjPermN : @Native.conjPermN = @Model.conjPermN := by
  delta Native.conjPermN Model.conjPermN
  rw [native_Pauli_s, native_kappaN, native_Pauli_a, native_permCN, native_thetaN, native_permDN, native_Pauli_d]
  all_goals rfl

theorem native_conjTN : @Native.conjTN = @Model.conjTN := by
  delta Native.conjTN Model.conjTN
  rw [native_thetaBit, native_acodeN]
  all_goals rfl

theorem native_conjDN : @Native.conjDN = @Model.conjDN := by
  delta Native.conjDN Model.conjDN
  rw [native_pairN, native_pN, native_thetaN]
  all_goals rfl

theorem native_conjYN : @Native.conjYN = @Model.conjYN := by
  delta Native.conjYN Model.conjYN
  rw [native_Pauli_mul, native_Pauli_s, native_conjTN, native_Pauli_a, native_conjDN, native_Pauli_d]
  all_goals rfl

theorem native_conjXiN : @Native.conjXiN = @Model.conjXiN := by
  delta Native.conjXiN Model.conjXiN
  rw [native_Pauli_a, native_Pauli_d, native_parN, native_Pauli_s, native_qGN, native_bGN, native_gammaLowN]
  all_goals rfl

theorem native_ePauliN : @Native.ePauliN = @Model.ePauliN := by
  delta Native.ePauliN Model.ePauliN
  rw [native_Pauli_s, native_mu0N, native_Pauli_a, native_pairN, native_shiftN, native_pi0N, native_Pauli_d]
  all_goals rfl

theorem native_ePermN : @Native.ePermN = @Model.ePermN := by
  delta Native.ePermN Model.ePermN
  rw [native_kappaN, native_pi0N, native_mu0N, native_permCN]
  all_goals rfl

theorem native_eYN : @Native.eYN = @Model.eYN := by
  delta Native.eYN Model.eYN
  rw [native_kN, native_pi0N, native_thetaBit, native_shiftN]
  all_goals rfl

theorem native_xiGammaN : @Native.xiGammaN = @Model.xiGammaN := by
  delta Native.xiGammaN Model.xiGammaN
  rw [native_sumRange, native_pairN, native_gammaLowN, native_sgnI, native_qGN, native_pi0N]
  all_goals rfl

theorem native_xiGTerm : @Native.xiGTerm = @Model.xiGTerm := by
  delta Native.xiGTerm Model.xiGTerm
  rw [native_qGN, native_mu0N, native_shiftN, native_pi0N]
  all_goals rfl

theorem native_Key : Native.Key = Model.Key := rfl

theorem native_Key_A : @Native.Key.A = @Model.Key.A := rfl

theorem native_Key_X : @Native.Key.X = @Model.Key.X := rfl

theorem native_Key_W : @Native.Key.W = @Model.Key.W := rfl

theorem native_coeffOf : @Native.coeffOf = @Model.coeffOf := by
  funext κ v
  induction v with
  | nil => rfl
  | cons e v ih => simp only [Native.coeffOf, Model.coeffOf, ih]

theorem native_eqModel : @Native.eqModel = @Model.eqModel := by
  delta Native.eqModel Model.eqModel
  rw [native_coeffOf]
  all_goals rfl

theorem native_c4N : @Native.c4N = @Model.c4N := rfl

theorem native_signedTerm : @Native.signedTerm = @Model.signedTerm := by
  delta Native.signedTerm Model.signedTerm
  rw [native_sgnI]
  all_goals rfl

theorem native_keyActPauli : @Native.keyActPauli = @Model.keyActPauli := by
  delta Native.keyActPauli Model.keyActPauli
  rw [native_Key_A, native_conjPauliN, native_signedTerm, native_Key_X, native_Pauli_a, native_Pauli_d, native_Pauli_s, native_ePauliN, native_Key_W]
  all_goals rfl

theorem native_keyActPerm : @Native.keyActPerm = @Model.keyActPerm := by
  delta Native.keyActPerm Model.keyActPerm
  rw [native_Key_A, native_sgnI, native_conjPermN, native_signedTerm, native_Key_X, native_Pauli_a, native_Pauli_d, native_Pauli_s, native_ePermN, native_Key_W]
  all_goals rfl

theorem native_keyActSign : @Native.keyActSign = @Model.keyActSign := by
  delta Native.keyActSign Model.keyActSign
  rw [native_signedTerm, native_Key_A, native_wordN, native_conjYN, native_Key_X, native_Pauli_a, native_Pauli_d, native_Pauli_s, native_eYN, native_Key_W]
  all_goals rfl

theorem native_keyActXi : @Native.keyActXi = @Model.keyActXi := by
  delta Native.keyActXi Model.keyActXi
  rw [native_Key_A, native_c4N, native_sgnI, native_bmaskN, native_conjYN, native_conjXiN, native_signedTerm, native_Key_X, native_Pauli_a, native_Pauli_d, native_Pauli_s, native_xiGTerm, native_eYN, native_Key_W, native_xiGammaN]
  all_goals rfl

theorem native_actVec : @Native.actVec = @Model.actVec := rfl

theorem native_oddCodesOf : @Native.oddCodesOf = @Model.oddCodesOf := by
  delta Native.oddCodesOf Model.oddCodesOf
  rw [native_wordN]
  all_goals rfl

theorem native_oddCodes : Native.oddCodes = Model.oddCodes := by
  delta Native.oddCodes Model.oddCodes
  rw [native_oddCodesOf]
  all_goals rfl

theorem native_octCoeffsOf : @Native.octCoeffsOf = @Model.octCoeffsOf := by
  delta Native.octCoeffsOf Model.octCoeffsOf
  rw [native_popcN, native_wordN]
  all_goals rfl

theorem native_octCoeffs : Native.octCoeffs = Model.octCoeffs := by
  delta Native.octCoeffs Model.octCoeffs
  rw [native_octCoeffsOf]
  all_goals rfl

theorem native_localOrder : @Native.localOrder = @Model.localOrder := rfl

theorem native_spreadN : @Native.spreadN = @Model.spreadN := by
  delta Native.spreadN Model.spreadN
  rw [native_combN, native_localOrder]
  all_goals rfl

theorem native_localPairs : @Native.localPairs = @Model.localPairs := rfl

theorem native_minusKey : @Native.minusKey = @Model.minusKey := by
  delta Native.minusKey Model.minusKey
  rw [native_Key_X, native_dualN]
  all_goals rfl

theorem native_plusKey : @Native.plusKey = @Model.plusKey := by
  delta Native.plusKey Model.plusKey
  rw [native_Key_X, native_dualN]
  all_goals rfl

theorem native_oddCode : @Native.oddCode = @Model.oddCode := by
  delta Native.oddCode Model.oddCode
  rw [native_wordN, native_pN]
  all_goals rfl

theorem native_oddKey : @Native.oddKey = @Model.oddKey := by
  delta Native.oddKey Model.oddKey
  rw [native_Key_X, native_oddCode, native_thetaN, native_dualN]
  all_goals rfl

theorem native_octCode : @Native.octCode = @Model.octCode := by
  delta Native.octCode Model.octCode
  rw [native_popcN, native_spreadN, native_wordN]
  all_goals rfl

theorem native_octKey : @Native.octKey = @Model.octKey := by
  delta Native.octKey Model.octKey
  rw [native_Key_X, native_octCode, native_thetaN, native_dualN, native_spreadN, native_wordN]
  all_goals rfl

theorem native_rawModel : @Native.rawModel = @Model.rawModel := by
  delta Native.rawModel Model.rawModel
  rw [native_Key_A, native_minusKey, native_plusKey, native_oddKey, native_oddCodes, native_octKey, native_octCoeffs, native_localPairs, native_Key_W]
  all_goals rfl

theorem native_rowModel : @Native.rowModel = @Model.rowModel := by
  delta Native.rowModel Model.rowModel
  rw [native_rawModel]
  all_goals rfl

theorem native_rowOK : @Native.rowOK = @Model.rowOK := by
  delta Native.rowOK Model.rowOK
  rw [native_eqModel, native_actVec, native_rawModel, native_rowModel]
  all_goals rfl

theorem native_genOK : @Native.genOK = @Model.genOK := by
  delta Native.genOK Model.genOK
  rw [native_rowOK]
  all_goals rfl

theorem native_Mtab : Native.Mtab = Model.Mtab := rfl

theorem native_Mentry : @Native.Mentry = @Model.Mentry := by
  delta Native.Mentry Model.Mentry
  rw [native_Mtab]
  all_goals rfl

theorem native_tauRow : @Native.tauRow = @Model.tauRow := by
  delta Native.tauRow Model.tauRow
  rw [native_sgnI, native_wordN, native_oddCodes, native_Mentry, native_pN]
  all_goals rfl

theorem native_octDataOK : Native.octDataOK = Model.octDataOK := by
  delta Native.octDataOK Model.octDataOK
  rw [native_octCoeffs, native_wordN, native_spreadN, native_popcN]
  all_goals rfl

theorem native_octSign : @Native.octSign = @Model.octSign := by
  delta Native.octSign Model.octSign
  rw [native_sgnI, native_popcN]
  all_goals rfl

theorem native_octSignOK : Native.octSignOK = Model.octSignOK := by
  delta Native.octSignOK Model.octSignOK
  rw [native_popcN, native_octSign, native_localPairs, native_sumRange, native_Mentry]
  all_goals rfl

theorem native_recPerms : Native.recPerms = Model.recPerms := rfl

theorem native_qPauli : @Native.qPauli = @Model.qPauli := rfl

theorem native_frameCode : @Native.frameCode = @Model.frameCode := rfl

end CFSG.Monster.B.Rep4371
