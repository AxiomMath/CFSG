module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import Certificates.Kernel.LocalQT.Base.C4075
import CFSG.Certificates.Kernel.LocalQTBaseSound

public section

namespace Certificates

open CFSG.KD.LQT.C4075 CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.Mathieu (m11a m11b m12a m12b m22a m22b m24a m24b card_M11 card_M12 card_M22 card_M24) in
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card) in
theorem certificate4075 : (slpValidAux m11Prog 2 = true)
    ∧ (BaseCertS 11 (List.range 11) m11SLP m11Qp 159 189 193 191 195
            m11Enum.1 m11Enum.2.1 m11Enum.2.2 4)
    ∧ (slpValidAux m12Prog 2 = true)
    ∧ (BaseCertS 12 (List.range 12) m12SLP m12Qp 153 204 208 206 210
            m12Enum.1 m12Enum.2.1 m12Enum.2.2 6)
    ∧ (slpValidAux m22Prog 2 = true)
    ∧ (BaseCertS 22 (List.range 22) m22SLP m22Qp 163 205 209 207 211
            m22Enum.1 m22Enum.2.1 m22Enum.2.2 7)
    ∧ (slpValidAux m23Prog 2 = true)
    ∧ (BaseCertS 23 (List.range 23) m23SLP m23Qp 159 199 203 201 205
            m23Enum.1 m23Enum.2.1 m23Enum.2.2 7)
    ∧ (slpValidAux m24Prog 2 = true)
    ∧ (BaseCertS 24 (List.range 24) m24SLP m24Qp 162 213 216 214 217
            m24Enum.1 m24Enum.2.1 m24Enum.2.2 10) :=
  ⟨v11, CFSG.KC.LQT.BC.base_sound (by decide) _ _ _ _ _ _ _ _ _ _ _ _ b11,
    v12, CFSG.KC.LQT.BC.base_sound (by decide) _ _ _ _ _ _ _ _ _ _ _ _ b12,
    v22, CFSG.KC.LQT.BC.base_sound (by decide) _ _ _ _ _ _ _ _ _ _ _ _ b22,
    v23, CFSG.KC.LQT.BC.base_sound (by decide) _ _ _ _ _ _ _ _ _ _ _ _ b23,
    v24, CFSG.KC.LQT.BC.base_sound (by decide) _ _ _ _ _ _ _ _ _ _ _ _ b24⟩

end Certificates
