module

public import CFSG.Quasithin.EmptyFaithful.ModECheck

public section

namespace CFSG.Quasithin.ModE

theorem lt0K_gen : lt0K = [wK (tgW.getD 0 []), wK (tgW.getD 1 []), wK (tgW.getD 2 []),
    wK (tgiW.getD 0 []), wK (tgiW.getD 1 []), wK (tgiW.getD 2 [])] := by decide +kernel

theorem lt0K_inv0 : Nat.beq (comp (wK (tgW.getD 0 [])) (wK (tgiW.getD 0 []))) kId = true := by
  decide +kernel

theorem lt0K_inv1 : Nat.beq (comp (wK (tgW.getD 1 [])) (wK (tgiW.getD 1 []))) kId = true := by
  decide +kernel

theorem lt0K_inv2 : Nat.beq (comp (wK (tgW.getD 2 [])) (wK (tgiW.getD 2 []))) kId = true := by
  decide +kernel

theorem chain0 : chainR lt0K tab0 [kId] = true := by decide +kernel

theorem tlK_eq : tlK = tab0.map (fun t => t.1) ++ [kId] := by decide +kernel

theorem tlK_len : tlK.length = 128 := by decide +kernel

theorem tlK_nodup : nodupB tlK = true := by decide +kernel

theorem tlK_closed :
    allB (fun x => allB (fun g => memB (comp g x) tlK) lt0K) tlK = true := by decide +kernel

theorem zk_eq : zk = wK zW := by decide +kernel

theorem zk_unique : allB (fun x => Nat.beq x kId || !(Nat.beq (comp x x) kId) ||
    !(allB (fun g => Nat.beq (comp x g) (comp g x)) lt0K) || Nat.beq x zk) tlK = true := by
  decide +kernel

theorem chainC0 : chainC ltK tabC [zk] = true := by decide +kernel

theorem ysK_eq : ysK = tabC.map (fun t => t.1) ++ [zk] := by decide +kernel

theorem ysK_len : ysK.length = 495 := by decide +kernel

theorem ysK_nodup : nodupB ysK = true := by decide +kernel

theorem gk_eq : gk = wK gW := by decide +kernel

theorem gik_eq : gik = wK giW := by decide +kernel

theorem g_inv : Nat.beq (comp gk gik) kId = true := by decide +kernel

theorem g_comm : Nat.beq (comp gk zk) (comp zk gk) = true := by decide +kernel

theorem qg_sub : allB (fun x => memB x qgK ||
    !(memB (comp (comp gk x) gik) tlK && memB (comp (comp gik x) gk) tlK)) tlK = true := by
  decide +kernel

theorem qg_count : allB (fun x => Nat.beq x kId || !(Nat.beq (comp x x) kId) || Nat.beq x zk ||
    Nat.ble (cntB (fun y => Nat.beq (comp y y) kId && Nat.beq (comp x y) (comp y x)) qgK) 12)
    qgK = true := by decide +kernel

end CFSG.Quasithin.ModE
