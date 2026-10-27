module

public import CFSG.Sporadic.Recognition.Co2MultiplierInputs
import Certificates.Kernel.Co2Mult.TabK
import CFSG.Certificates.Kernel.TabMatSound

public section

namespace CertificateChecks.KernelCo2Mult

open CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.Co2 CFSG.Sporadic.Co2.Native
  CFSG.Sporadic.Recognition.Co2Multiplier CFSG.Sporadic.Bridge.TwoGen.Native

theorem tab : co2TabCheck = true := by
  have horb : ∀ h < (co2Data ()).n, orbAt (co2Data ()).d (co2Data ()).n NA NB Pt AT BT h = true :=
    allS_cover (S := 256) (ns := 9) (fun s hs => by
      match s, hs with
      | 0, _ => exact orb_0
      | 1, _ => exact orb_1
      | 2, _ => exact orb_2
      | 3, _ => exact orb_3
      | 4, _ => exact orb_4
      | 5, _ => exact orb_5
      | 6, _ => exact orb_6
      | 7, _ => exact orb_7
      | 8, _ => exact orb_8
      | _ + 9, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hbfs : ∀ h < (co2Data ()).n, bfsAt (co2Data ()).n AT BT FO h = true :=
    allS_cover (S := 256) (ns := 9) (fun s hs => by
      match s, hs with
      | 0, _ => exact bfs_0
      | 1, _ => exact bfs_1
      | 2, _ => exact bfs_2
      | 3, _ => exact bfs_3
      | 4, _ => exact bfs_4
      | 5, _ => exact bfs_5
      | 6, _ => exact bfs_6
      | 7, _ => exact bfs_7
      | 8, _ => exact bfs_8
      | _ + 9, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hsort : ∀ h < (co2Data ()).n, sortAt (co2Data ()).n Pt S IP SP h = true :=
    allS_cover (S := 256) (ns := 9) (fun s hs => by
      match s, hs with
      | 0, _ => exact sort_0
      | 1, _ => exact sort_1
      | 2, _ => exact sort_2
      | 3, _ => exact sort_3
      | 4, _ => exact sort_4
      | 5, _ => exact sort_5
      | 6, _ => exact sort_6
      | 7, _ => exact sort_7
      | 8, _ => exact sort_8
      | _ + 9, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hP := vpts_of hn horb hsort
  obtain ⟨ha, hb⟩ := orbit_real (co2Data ()) hA hB hseed hn hP0 horb hbfs hsort
  have hai := (real_inv hP ha fun v hv => vmF_inv hAi hv).1
  have hbi := (real_inv hP hb fun v hv => vmF_inv hBi hv).1
  have h := relCheck_of_tabMatK hP ha hai hb hbi co2GenWords (by decide) co2Pairs tabK
  rw [← co2CheckWords_eq] at h
  exact h

end CertificateChecks.KernelCo2Mult

end
