module

public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.Co1B.TwistData
public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Block.Iota

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CertificateChecks.KernelCo1Cover
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.TwistNative

@[expose] noncomputable def TWB : List Nat := [R0, R1, getL oneK IRS 23] ++ IQK

theorem twBase_eq : twBaseRows = TWB.map (unpackR 24) := by
  have hq : (List.range 8).map CFSG.Sporadic.Co1Block.iotaQRows = IQK.map (unpackR 24) := twoAQ_eq
  rw [twBaseRows, aR_eq, bR_eq, iotaA_eq, hq, TWB, List.map_append]
  rfl

theorem tw_chk : dagOK TWB twDerivs TWS TWIS = true := by quickRfl

theorem tw_dag : dag twBaseRows twDerivs = (TWS.map (unpackR 24), TWIS.map (unpackR 24), true) := by
  rw [twBase_eq]
  exact dag_sound tw_chk

theorem dag_snd_aux : ∀ (ds : List (List Int)) (st : List Rows × List Rows × Bool),
    st.2.1 = st.1.map inv → (ds.foldl step st).2.1 = (ds.foldl step st).1.map inv
  | [], _, h => h
  | w :: ds, st, h => by
    rw [List.foldl_cons]
    apply dag_snd_aux ds
    simp only [step, List.map_append, List.map_cons, List.map_nil, h]

theorem dag_snd (base : List Rows) (ds : List (List Int)) :
    (dag base ds).2.1 = (dag base ds).1.map inv :=
  dag_snd_aux ds _ rfl

theorem inv_one' : inv one = one := by
  rw [← one_eq]
  exact inv_sound' (A := oneK) (AI := oneK) (by quickRfl)

theorem TWS_len : TWS.length = 83 := rfl

theorem TWIS_len : TWIS.length = 83 := rfl

theorem tw_flag : (dag twBaseRows twDerivs).2.2 = true := by rw [tw_dag]

theorem twRow_get (j : Nat) : twRow j = unpackR 24 (getL oneK TWS (j - 1)) := by
  rw [twRow, twRows, tw_dag, ← one_eq]
  exact getD_map_u oneK TWS (j - 1)

theorem invTw (k : Nat) : inv (unpackR 24 (getL oneK TWS k)) = unpackR 24 (getL oneK TWIS k) := by
  have h := dag_snd twBaseRows twDerivs
  rw [tw_dag] at h
  rw [← getD_map_u, ← getD_map_u, one_eq]
  by_cases hk : k < 83
  · have h1 : ((TWS.map (unpackR 24)).map inv).getD k one = inv ((TWS.map (unpackR 24)).getD k one) := by
      rw [List.getD_eq_getElem _ _ (by simpa [TWS_len] using hk),
        List.getD_eq_getElem _ _ (by simpa [TWS_len] using hk), List.getElem_map]
    rw [← h1]
    exact congrArg (fun l => l.getD k one) h.symm
  · rw [List.getD_eq_default _ _ (by simpa [TWS_len] using hk),
      List.getD_eq_default _ _ (by simpa [TWIS_len] using hk), inv_one']

@[expose] noncomputable def qwK (e : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => if e.testBit k = true then mulK acc (getL oneK IRS (36 + k)) else acc) oneK

theorem qWordRow_eq (e : Nat) : qWordRow e = unpackR 24 (qwK e) := by
  rw [qWordRow, qwK, ← one_eq]
  simp only [iotaQ_eq]
  exact foldl_mul_unpack (fun k => e.testBit k) (fun k => getL oneK IRS (36 + k)) _ oneK

theorem yRow_q (i : Nat) : yRow i = unpackR 24 (qwK (yBits.getD i 0)) := qWordRow_eq _

@[expose] noncomputable def ypK (c : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if c.testBit i = true then mulK acc (qwK (yBits.getD i 0)) else acc) oneK

theorem yprodRow_q (c : Nat) : yprodRow c = unpackR 24 (ypK c) := by
  rw [yprodRow, ypK, ← one_eq]
  simp only [yRow_q]
  exact foldl_mul_unpack (fun i => c.testBit i) (fun i => qwK (yBits.getD i 0)) _ oneK

end CertificateChecks.KernelCo1B

end
